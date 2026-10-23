package aprove.verification.dpframework.LCTRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.LCTRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Splits a dependency pair problem of an LCTRS into the strongly connected components of an
 * over-approximation of its dependency graph. An infinite chain ends in one of the components, so the
 * problem is finite iff all components are.
 *
 * <p>There is an edge from <code>s -> t [phi]</code> to <code>u -> v [psi]</code> unless one of two
 * checks shows that the second pair cannot follow the first one in a chain:</p>
 * <ul>
 * <li><code>cap(t)</code> and <code>u</code> do not unify, where <code>cap</code> replaces everything that
 * a rewrite step or an instantiation can change by a fresh variable: the variables and the subterms whose
 * root is a defined symbol or a theory symbol (which a calculation step may replace). Values are kept,
 * since they are normal forms.</li>
 * <li>With <code>UseGuards</code>: the formula <code>phi and psi and psi(t, u, L)</code> of Kop
 * (Termination of LCTRSs, 2016, Thm. 7) is unsatisfiable, where L are the logical variables of both pairs
 * and <code>psi(t, u, L)</code> collects the equations between the logical terms in t and the terms at the
 * same positions of u. A logical term over L is instantiated by values, so it can only be evaluated.</li>
 * </ul>
 *
 * <p>So in contrast to the dependency graph after a projection onto the declared sorts, this graph takes
 * the values and the guards of the pairs into account.</p>
 */
public class LCTRSDependencyGraphProcessor extends Processor.ProcessorSkeleton {

    public static class Arguments {

        /** Whether an SMT solver is asked if the guards allow that a pair follows another one. */
        public boolean useGuards = true;

        /** The time limit of the SMT solver for one edge in milliseconds. */
        public int guardTimeout = 500;

        /** The number of calls of the SMT solver after which the remaining edges are not checked. */
        public int maxChecks = 2000;

        public void setUseGuards(final boolean useGuards) {
            this.useGuards = useGuards;
        }

        public void setGuardTimeout(final int guardTimeout) {
            this.guardTimeout = guardTimeout;
        }

        public void setMaxChecks(final int maxChecks) {
            this.maxChecks = maxChecks;
        }

    }

    private final Arguments arguments;

    @ParamsViaArgumentObject
    public LCTRSDependencyGraphProcessor(final Arguments arguments) {
        this.arguments = arguments;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof LCTRSDPProblem;
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        final LCTRSDPProblem dp = (LCTRSDPProblem) obl;
        final LCTRSSignature signature = dp.getSignature();
        final Set<FunctionSymbol> defined = dp.getDefinedSymbols();
        final Map<LCTRSRule, Node<LCTRSRule>> nodes = new LinkedHashMap<>();
        final Map<LCTRSRule, TRSTerm> caps = new LinkedHashMap<>();
        for (final LCTRSRule pair : dp.getP()) {
            nodes.put(pair, new Node<>(pair));
            caps.put(pair, LCTRSDependencyGraphProcessor.cap(pair.right(), signature, defined, new int[1]));
        }
        final LCTRSSmt smt = new LCTRSSmt(signature, this.arguments.guardTimeout);
        final Graph<LCTRSRule, Object> graph = new Graph<>(new LinkedHashSet<>(nodes.values()));
        for (final LCTRSRule from : dp.getP()) {
            aborter.checkAbortion();
            for (final LCTRSRule to : dp.getP()) {
                if (caps.get(from).unifiesVarDisjoint(to.left())
                    && !this.guardsExclude(from, to, signature, defined, smt, aborter))
                {
                    graph.addEdge(nodes.get(from), nodes.get(to));
                }
            }
        }
        final List<LCTRSDPProblem> components = new ArrayList<>();
        int kept = 0;
        for (final Cycle<LCTRSRule> scc : graph.getSCCs()) {
            final List<LCTRSRule> pairs = new ArrayList<>(dp.getP());
            pairs.removeIf(pair -> !scc.contains(nodes.get(pair)));
            kept += pairs.size();
            components.add(new LCTRSDPProblem(signature, dp.getDPSort(), pairs, dp.getR()));
        }
        if (components.size() == 1 && kept == dp.getP().size()) {
            return ResultFactory.unsuccessful("The dependency graph is strongly connected.");
        }
        final LCTRSDependencyGraphProof proof =
            new LCTRSDependencyGraphProof(components.size(), dp.getP().size() - kept);
        return components.isEmpty()
            ? ResultFactory.proved(proof)
            : ResultFactory.provedAnd(components, YNMImplication.EQUIVALENT, proof);
    }

    /**
     * @return true iff the SMT solver shows that the pair <code>to</code> cannot follow <code>from</code>
     */
    private boolean guardsExclude(
        final LCTRSRule from,
        final LCTRSRule to,
        final LCTRSSignature signature,
        final Set<FunctionSymbol> defined,
        final LCTRSSmt smt,
        final Abortion aborter) throws AbortionException
    {
        if (!this.arguments.useGuards || smt.getCalls() >= this.arguments.maxChecks) {
            return false;
        }
        final List<TRSTerm[]> equations = new ArrayList<>();
        if (!LCTRSDependencyGraphProcessor.collectEquations(
            from.right(), to.left(), from.logicalVariables(), to.logicalVariables(), signature, defined, equations))
        {
            return true;
        }
        if (equations.isEmpty() && !from.hasGuard() && !to.hasGuard()) {
            return false;
        }
        // the variables of the two pairs are kept apart by the prefixes
        final LCTRSSmt.Formula formula = smt.new Formula();
        formula.add(from.guard(), from.variableSorts(), "1.");
        formula.add(to.guard(), to.variableSorts(), "2.");
        for (final TRSTerm[] equation : equations) {
            formula.addEquation(equation[0], from.variableSorts(), "1.", equation[1], to.variableSorts(), "2.");
        }
        return formula.isUnsatisfiable(aborter);
    }

    /**
     * The formula <code>psi(s, t, L)</code> of Kop (Termination of LCTRSs, 2016, Sect. 4), a necessary
     * condition for <code>s gamma</code> rewriting to <code>t gamma</code> if gamma maps the logical
     * variables to values. The variables of s and t are regarded as different.
     *
     * @param logicalS the logical variables among the variables of s
     * @param logicalT the logical variables among the variables of t
     * @param equations collects the equations <code>s' = t'</code> of the formula
     * @return false iff the formula is false
     */
    private static boolean collectEquations(
        final TRSTerm s,
        final TRSTerm t,
        final Set<TRSVariable> logicalS,
        final Set<TRSVariable> logicalT,
        final LCTRSSignature signature,
        final Set<FunctionSymbol> defined,
        final List<TRSTerm[]> equations)
    {
        final FunctionSymbol f = s.isVariable() ? null : ((TRSFunctionApplication) s).getRootSymbol();
        final FunctionSymbol g = t.isVariable() ? null : ((TRSFunctionApplication) t).getRootSymbol();
        // s is a logical term whose variables are instantiated by values: it can only be evaluated
        final boolean logical = signature.isLogicalTerm(s) && logicalS.containsAll(s.getVariables());
        final boolean isCalculation = f != null && signature.isTheorySymbol(f) && !signature.isValue(f);
        if (f == null ? !logical : defined.contains(f)) {
            // s can be instantiated or rewritten arbitrarily
            return true;
        }
        if (isCalculation && !logical && (g == null || signature.isValue(g))) {
            // s may be evaluated to a value once its arguments are rewritten
            return true;
        }
        if (f != null && !isCalculation && g == null && !logicalT.contains(t)) {
            // t matches every term
            return true;
        }
        if (f != null && f.equals(g)) {
            for (int i = 0; i < f.getArity(); i++) {
                if (!LCTRSDependencyGraphProcessor.collectEquations(
                    ((TRSFunctionApplication) s).getArgument(i),
                    ((TRSFunctionApplication) t).getArgument(i),
                    logicalS,
                    logicalT,
                    signature,
                    defined,
                    equations))
                {
                    return false;
                }
            }
            return true;
        }
        if (logical && signature.isLogicalTerm(t)) {
            equations.add(new TRSTerm[] {s, t});
            return true;
        }
        return false;
    }

    /**
     * @param counter the number of fresh variables that were created
     */
    private static TRSTerm cap(
        final TRSTerm term,
        final LCTRSSignature signature,
        final Set<FunctionSymbol> defined,
        final int[] counter)
    {
        final FunctionSymbol f = term.isVariable() ? null : ((TRSFunctionApplication) term).getRootSymbol();
        if (f == null || defined.contains(f) || signature.isTheorySymbol(f) && !signature.isValue(f)) {
            return TRSTerm.createVariable("cap" + counter[0]++);
        }
        final List<TRSTerm> args = new ArrayList<>();
        for (final TRSTerm arg : ((TRSFunctionApplication) term).getArguments()) {
            args.add(LCTRSDependencyGraphProcessor.cap(arg, signature, defined, counter));
        }
        return TRSTerm.createFunctionApplication(f, args);
    }

    /**
     * The proof of the decomposition.
     */
    private static class LCTRSDependencyGraphProof extends Proof.DefaultProof {

        private final int components;

        private final int removed;

        private LCTRSDependencyGraphProof(final int components, final int removed) {
            this.components = components;
            this.removed = removed;
            this.setShortName("LCTRSDependencyGraphProof");
            this.setLongName("Dependency Graph");
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "The approximation of the dependency graph (Kop, Termination of LCTRSs, 2016) has " + this.components
                + " strongly connected component(s). " + this.removed
                + " pair(s) are on no cycle and were removed.";
        }

    }

}
