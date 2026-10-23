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

/**
 * The sort projection of a dependency pair problem of an LCTRS (Kulmer, Integer Term Rewriting via
 * Projections, Def. 3.6): removes everything that does not have one of the sorts S to keep.
 *
 * <p>The argument filter pi_S keeps the arguments of a term symbol (or tuple symbol) whose sort is in S,
 * and all arguments of a theory symbol. The result is the dependency pair problem with</p>
 * <ul>
 * <li>P: <code>pi_S(s) -> pi_S(t) [phi]</code> for every pair <code>s -> t [phi]</code>,</li>
 * <li>R: <code>pi_S(l) -> pi_S(r) [phi]</code> for every rule whose sort is in S. The other rules cannot
 * be used at a position that is kept.</li>
 * </ul>
 *
 * <p>Every rewrite step of the LCTRS is either removed or still possible after the projection, so an
 * infinite chain stays an infinite chain and the projection is sound. It is not complete, as the removed
 * arguments may be the reason for termination. A step that is innermost in the LCTRS is not necessarily
 * innermost in the projection (filtered left-hand sides match more terms), so the chains of the result
 * must not be restricted to innermost rewriting.</p>
 *
 * <p>The projection is only applicable if it does not make a variable of a right-hand side free (Def.
 * 3.7): a variable that only occurs in removed arguments of the left-hand side could not be instantiated
 * by the value-substitutions of an LCTRS anymore, unless it already was a logical variable.</p>
 */
public class LCTRSSortProjectionProcessor extends Processor.ProcessorSkeleton {

    /**
     * The sorts to keep.
     */
    public enum Keep {
        /** The sorts that are declared in the input, i.e. everything from the theories is removed. */
        TERMS,

        /** The sorts of the theories, i.e. everything that is built from declared sorts is removed. */
        THEORY
    }

    public static class Arguments {

        public Keep keep = Keep.TERMS;

        public void setKeep(final Keep keep) {
            this.keep = keep;
        }

    }

    private final Keep keep;

    @ParamsViaArgumentObject
    public LCTRSSortProjectionProcessor(final Arguments arguments) {
        this.keep = arguments.keep;
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
        final LCTRSSort dpSort = dp.getDPSort();
        final Map<FunctionSymbol, LCTRSSortDeclaration> declarations = signature.functions();

        // the argument filter and the filtered signature
        final Map<FunctionSymbol, List<Integer>> filter = new LinkedHashMap<>();
        final Map<FunctionSymbol, FunctionSymbol> filteredSymbols = new LinkedHashMap<>();
        final Set<FunctionSymbol> used = new LinkedHashSet<>(signature.theorySymbols().keySet());
        used.addAll(signature.userTheorySymbols().keySet());
        final Map<FunctionSymbol, LCTRSSortDeclaration> filtered = new LinkedHashMap<>();
        boolean changed = false;
        for (final Map.Entry<FunctionSymbol, LCTRSSortDeclaration> entry : declarations.entrySet()) {
            final LCTRSSortDeclaration declaration = entry.getValue();
            if (!this.isKept(declaration.resultSort(), dpSort)) {
                changed = true;
                continue;
            }
            final List<Integer> positions = new ArrayList<>();
            final List<LCTRSSort> sorts = new ArrayList<>();
            for (int i = 0; i < declaration.arity(); i++) {
                if (this.isKept(declaration.argumentSorts().get(i), dpSort)) {
                    positions.add(i);
                    sorts.add(declaration.argumentSorts().get(i));
                }
            }
            // symbols with different arities may get the same arity
            final FunctionSymbol f = entry.getKey();
            String name = f.getName();
            while (!used.add(FunctionSymbol.create(name, positions.size()))) {
                name += "'";
            }
            final FunctionSymbol filteredSymbol = FunctionSymbol.create(name, positions.size());
            changed |= positions.size() < f.getArity();
            filter.put(f, positions);
            filteredSymbols.put(f, filteredSymbol);
            filtered.put(filteredSymbol, new LCTRSSortDeclaration(sorts, declaration.resultSort()));
        }
        if (!changed) {
            return ResultFactory.unsuccessful("All sorts are kept.");
        }

        final Projection projection = new Projection(filter, filteredSymbols);
        final List<LCTRSRule> pairs = new ArrayList<>();
        final List<LCTRSRule> rules = new ArrayList<>();
        for (final boolean isPair : new boolean[] {true, false}) {
            for (final LCTRSRule rule : isPair ? dp.getP() : dp.getR()) {
                aborter.checkAbortion();
                if (!filter.containsKey(rule.left().getRootSymbol())) {
                    // a rule of a sort that is removed
                    continue;
                }
                final LCTRSRule projected = projection.project(rule);
                // the projection must not make a variable of a right-hand side free
                final Set<TRSVariable> logical = rule.logicalVariables();
                for (final TRSVariable x : projected.right().getVariables()) {
                    if (!projected.left().getVariables().contains(x) && !logical.contains(x)) {
                        return ResultFactory.unsuccessful(
                            "The projection is not applicable: the variable " + x.getName() + " of " + rule
                                + " would only occur in the right-hand side of " + projected + ".");
                    }
                }
                final List<LCTRSRule> target = isPair ? pairs : rules;
                if (!target.contains(projected)) {
                    target.add(projected);
                }
            }
        }

        final Set<LCTRSSort> sorts = new LinkedHashSet<>();
        if (this.keep == Keep.TERMS) {
            sorts.addAll(signature.sorts());
        }
        sorts.add(dpSort);
        final LCTRSSignature projectedSignature =
            new LCTRSSignature(
                signature.theories(),
                sorts,
                filtered,
                signature.theorySymbols(),
                signature.userTheorySymbols());
        return ResultFactory.proved(
            new LCTRSDPProblem(projectedSignature, dpSort, pairs, rules),
            YNMImplication.SOUND,
            new LCTRSSortProjectionProof(this.keep, signature, declarations, projection));
    }

    private boolean isKept(final LCTRSSort sort, final LCTRSSort dpSort) {
        return sort.equals(dpSort) || sort.isTheorySort() == (this.keep == Keep.THEORY);
    }

    /**
     * The argument filter pi_S.
     *
     * @param positions the arguments to keep (starting with 0) of the term symbols that are kept
     * @param symbols the function symbols for the filtered term symbols
     */
    private record Projection(
        Map<FunctionSymbol, List<Integer>> positions,
        Map<FunctionSymbol, FunctionSymbol> symbols)
    {

        /**
         * @return the rule <code>pi(left) -> pi(right) [guard]</code> with the sorts of its variables
         */
        private LCTRSRule project(final LCTRSRule rule) {
            final TRSFunctionApplication projectedLeft = (TRSFunctionApplication) this.project(rule.left());
            final TRSTerm projectedRight = this.project(rule.right());
            final Map<TRSVariable, LCTRSSort> variableSorts = new LinkedHashMap<>(rule.variableSorts());
            final Set<TRSVariable> occurring = new LinkedHashSet<>(projectedLeft.getVariables());
            occurring.addAll(projectedRight.getVariables());
            occurring.addAll(rule.guard().getVariables());
            variableSorts.keySet().retainAll(occurring);
            return new LCTRSRule(projectedLeft, projectedRight, rule.guard(), variableSorts);
        }

        /**
         * Applies the argument filter. Theory symbols and values keep all arguments.
         */
        private TRSTerm project(final TRSTerm term) {
            if (term.isVariable()) {
                return term;
            }
            final TRSFunctionApplication app = (TRSFunctionApplication) term;
            final FunctionSymbol f = app.getRootSymbol();
            final List<Integer> kept = this.positions.get(f);
            final List<TRSTerm> args = new ArrayList<>();
            for (int i = 0; i < f.getArity(); i++) {
                if (kept == null || kept.contains(i)) {
                    args.add(this.project(app.getArgument(i)));
                }
            }
            return TRSTerm.createFunctionApplication(this.symbols.getOrDefault(f, f), args);
        }

    }

    /**
     * The proof of the projection.
     */
    private static class LCTRSSortProjectionProof extends Proof.DefaultProof {

        private final Keep keep;

        private final LCTRSSignature signature;

        private final Map<FunctionSymbol, LCTRSSortDeclaration> declarations;

        private final Projection projection;

        private LCTRSSortProjectionProof(
            final Keep keep,
            final LCTRSSignature signature,
            final Map<FunctionSymbol, LCTRSSortDeclaration> declarations,
            final Projection projection)
        {
            this.keep = keep;
            this.signature = signature;
            this.declarations = declarations;
            this.projection = projection;
            this.setShortName("LCTRSSortProjectionProof");
            this.setLongName("Sort Projection");
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append("Projected the pairs and rules onto ");
            if (this.keep == Keep.TERMS) {
                final StringJoiner sorts = new StringJoiner(", ");
                this.signature.sorts().forEach(sort -> sorts.add(sort.toString()));
                res.append("the declared sorts ");
                res.append(o.escape(this.signature.sorts().isEmpty() ? "(there are none)" : sorts.toString()));
            } else {
                res.append("the sorts of the theories");
            }
            res.append(": all arguments of other sorts and all rules of other sorts are removed. ");
            res.append("Every rewrite step is either removed or still possible after the projection, so an ");
            res.append("infinite chain is still an infinite chain (not necessarily innermost).");
            final List<String> removed = new ArrayList<>();
            for (final Map.Entry<FunctionSymbol, LCTRSSortDeclaration> entry : this.declarations.entrySet()) {
                final FunctionSymbol f = entry.getKey();
                final List<Integer> positions = this.projection.positions().get(f);
                if (positions == null) {
                    removed.add(f.getName() + " : " + entry.getValue() + " is removed");
                } else if (positions.size() < f.getArity()) {
                    final StringJoiner kept = new StringJoiner(", ", "[", "]");
                    positions.forEach(i -> kept.add(Integer.toString(i + 1)));
                    final String renamed = this.projection.symbols().get(f).getName();
                    removed.add(
                        f.getName() + " : " + entry.getValue() + " keeps the arguments " + kept
                            + (renamed.equals(f.getName()) ? "" : " and is renamed to " + renamed));
                }
            }
            if (!removed.isEmpty()) {
                res.append(o.linebreak()).append("The following function symbols are affected:");
                removed.forEach(line -> res.append(o.linebreak()).append(o.escape(line)));
            }
            return res.toString();
        }

    }

}
