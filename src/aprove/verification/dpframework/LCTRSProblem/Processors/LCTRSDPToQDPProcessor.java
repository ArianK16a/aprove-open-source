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
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.LCTRSProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Converts a dependency pair problem of an LCTRS without theory sorts into a QDP problem (Kulmer, Integer
 * Term Rewriting via Projections, Sect. 3.3), e.g. the result of
 * {@link LCTRSSortProjectionProcessor} for the declared sorts.
 *
 * <p>If no term of the pairs and rules contains a theory symbol, a value or a variable of a theory sort,
 * then a guard shares no variable with its rule. So a guard either does not restrict the rule at all (if
 * it is satisfiable) or the rule can never be applied. Hence the guards are removed, and with
 * <code>CheckGuards</code> the pairs and rules with an unsatisfiable guard are removed as well. Since no
 * theory symbol occurs, there are no calculation steps, and the remaining pairs and rules are those of an
 * ordinary TRS.</p>
 *
 * <p>The QDP problem is neither innermost nor minimal, as the chains of an {@link LCTRSDPProblem} are not.
 * It is unsorted and so has more chains than the LCTRS problem, i.e. the conversion is only sound.</p>
 */
public class LCTRSDPToQDPProcessor extends Processor.ProcessorSkeleton {

    public static class Arguments {

        /** Whether an SMT solver is asked if the guards are satisfiable. */
        public boolean checkGuards = true;

        /** The time limit of the SMT solver for one guard in milliseconds. */
        public int guardTimeout = 500;

        public void setCheckGuards(final boolean checkGuards) {
            this.checkGuards = checkGuards;
        }

        public void setGuardTimeout(final int guardTimeout) {
            this.guardTimeout = guardTimeout;
        }

    }

    private final Arguments arguments;

    @ParamsViaArgumentObject
    public LCTRSDPToQDPProcessor(final Arguments arguments) {
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
        final List<LCTRSRule> all = new ArrayList<>(dp.getP());
        all.addAll(dp.getR());
        for (final LCTRSRule rule : all) {
            final Set<FunctionSymbol> symbols = new LinkedHashSet<>(rule.left().getFunctionSymbols());
            symbols.addAll(rule.right().getFunctionSymbols());
            final Set<TRSVariable> variables = new LinkedHashSet<>(rule.left().getVariables());
            variables.addAll(rule.right().getVariables());
            for (final FunctionSymbol f : symbols) {
                if (!signature.isTermSymbol(f)) {
                    return ResultFactory.unsuccessful(
                        rule + " contains the theory symbol " + signature.getName(f) + ".");
                }
            }
            for (final TRSVariable x : variables) {
                if (rule.variableSorts().get(x).isTheorySort()) {
                    return ResultFactory.unsuccessful(
                        rule + " contains the variable " + x.getName() + " of a theory sort.");
                }
            }
            if (!rule.left().getVariables().containsAll(rule.right().getVariables())) {
                // cannot happen: such a variable is a logical variable and has a theory sort
                return ResultFactory.unsuccessful(rule + " has a variable that only occurs in its right-hand side.");
            }
        }
        final LCTRSSmt smt = new LCTRSSmt(signature, this.arguments.guardTimeout);
        final List<LCTRSRule> removed = new ArrayList<>();
        final Set<Rule> pairs = this.convert(dp.getP(), smt, removed, aborter);
        final Set<Rule> rules = this.convert(dp.getR(), smt, removed, aborter);
        final QDPProblem qdp =
            QDPProblem.create(
                ImmutableCreator.create(pairs),
                QTRSProblem.create(ImmutableCreator.create(rules)),
                false);
        return ResultFactory.proved(qdp, YNMImplication.SOUND, new LCTRSDPToQDPProof(removed, signature));
    }

    /**
     * @param removed collects the rules with an unsatisfiable guard
     * @return the other rules without their guards
     */
    private Set<Rule> convert(
        final List<LCTRSRule> rules,
        final LCTRSSmt smt,
        final List<LCTRSRule> removed,
        final Abortion aborter) throws AbortionException
    {
        final Set<Rule> res = new LinkedHashSet<>();
        for (final LCTRSRule rule : rules) {
            aborter.checkAbortion();
            if (this.arguments.checkGuards && rule.hasGuard()) {
                final LCTRSSmt.Formula formula = smt.new Formula();
                formula.add(rule.guard(), rule.variableSorts(), "");
                if (formula.isUnsatisfiable(aborter)) {
                    removed.add(rule);
                    continue;
                }
            }
            res.add(Rule.create(rule.left(), rule.right()));
        }
        return res;
    }

    /**
     * The proof of the conversion.
     */
    private static class LCTRSDPToQDPProof extends Proof.DefaultProof {

        private final List<LCTRSRule> removed;

        private final LCTRSSignature signature;

        private LCTRSDPToQDPProof(final List<LCTRSRule> removed, final LCTRSSignature signature) {
            this.removed = removed;
            this.signature = signature;
            this.setShortName("LCTRSDPToQDPProof");
            this.setLongName("LCTRS DP problem to QDP");
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append("No theory symbol, value or variable of a theory sort occurs in the pairs and rules, so ");
            res.append("the guards share no variable with them: a guard does not restrict its rule if it is ");
            res.append("satisfiable, and otherwise the rule cannot be applied. Hence the guards are removed, ");
            res.append("which yields a QDP problem (for full rewriting, not minimal).");
            if (!this.removed.isEmpty()) {
                res.append(o.linebreak());
                res.append("The following pairs and rules have an unsatisfiable guard and are removed:");
                this.removed.forEach(rule -> res.append(o.linebreak()).append(rule.export(o, this.signature)));
            }
            return res.toString();
        }

    }

}
