package aprove.verification.oldframework.IntTRS.Nonterm;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Prove periodic non-termination.
 *
 * @author Marc Brockschmidt
 */
public class IntTRSPeriodicNontermProcessor extends IntTRSNontermProcessor {
    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    public static class Arguments {
        /**
         * The number of unrolling steps to consider.
         */
        public int numberOfUnrollings = 10;
    }

    /**
     * Parameters for this processor.
     */
    private final Arguments arguments;

    /**
     * @param args The arguments to this processor.
     */
    @ParamsViaArgumentObject
    public IntTRSPeriodicNontermProcessor(final Arguments args) {
        this.arguments = args;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (!(obl instanceof IRSwTProblem) || !((IRSwTProblem) obl).isIRS()) {
            return false;
        }
        if (!Options.certifier.isNone()) {
            return false;
        }

        final IRSwTProblem problem = (IRSwTProblem) obl;

        if (problem.getStartTerm() != null) {
            return false;
        }

        final IDPPredefinedMap predefMap = IDPPredefinedMap.DEFAULT_MAP;
        final FunctionSymbol divSym = predefMap.getSym(Func.Div, DomainFactory.INTEGERS);
        final FunctionSymbol modSym = predefMap.getSym(Func.Mod, DomainFactory.INTEGERS);
        for (final IGeneralizedRule r : problem.getRules()) {
            final Set<FunctionSymbol> usedSyms = r.getFunctionSymbols();
            if (usedSyms.contains(divSym) || usedSyms.contains(modSym)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }

        final Set<IGeneralizedRule> normalizedRules = IntTRSNontermProcessor.moveFsIntoArgsAndNormalize(problem.getRules());

        //Now just encode the TRS a few times, trying to prove that variables at the end are the same as at the beginning:
        final FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<>();

        //The actual unrolling:
        final List<Formula<SMTLIBTheoryAtom>> unrollings = new LinkedList<>();
        for (int i = 1; i <= this.arguments.numberOfUnrollings; i++) {
            final List<Formula<SMTLIBTheoryAtom>> formulaeForThisUnrolling = new LinkedList<>();
            for (final IGeneralizedRule normalizedRule : normalizedRules) {
                final Pair<Formula<SMTLIBTheoryAtom>, Formula<SMTLIBTheoryAtom>> oneRuleStep =
                    IntTRSNontermProcessor.turnRuleIntoSMTFormulae(normalizedRule, "run" + i + "_", "run" + (i + 1) + "_", factory);
                formulaeForThisUnrolling.add(factory.buildAnd(oneRuleStep.x, oneRuleStep.y));
            }
            unrollings.add(factory.buildOr(formulaeForThisUnrolling));
        }

        //The equality checks:
        final List<Formula<SMTLIBTheoryAtom>> equalities = new LinkedList<>();
        for (int i = 2; i <= this.arguments.numberOfUnrollings; i++) {
            equalities.add(IntTRSPeriodicNontermProcessor.buildEqualities(normalizedRules, "run1_", "run" + i + "_", factory));
        }

        final Formula<SMTLIBTheoryAtom> equalityAfterUnrollingFormula =
            factory.buildAnd(factory.buildAnd(unrollings), factory.buildOr(equalities));

        final SMTEngine smtEngine = new SMTLIBEngine();
        Pair<YNM, Map<String, String>> res;
        try {
            final Abortion subAbortion = aborter.createChild(1000);
            res =
                smtEngine.solve(Collections.singletonList(equalityAfterUnrollingFormula), SMTLogic.QF_NIA, subAbortion);
        } catch (final WrongLogicException | AbortionException e) {
            // we do not care
            res = new Pair<>(YNM.MAYBE, null);
        }
        //If the formula is SAT, we are happy and haven proven nonterm. Otherwise, go away:
        if (res.x != YNM.YES) {
            return ResultFactory.unsuccessful();
        }

        final TRSFunctionApplication someLHS =
            (TRSFunctionApplication) normalizedRules.iterator().next().getLeft().renumberVariables("x");
        final Map<TRSVariable, TRSFunctionApplication> witnessSubst = IntTRSPeriodicNontermProcessor.extractVariableAssignment(res.y, "run1_");
        final TRSTerm witness = someLHS.applySubstitution(TRSSubstitution.create(ImmutableCreator.create(witnessSubst)));

        return ResultFactory.disproved(new IntTRSPeriodicNontermProof(normalizedRules, witness));
    }

    /**
     * @param normalizedRules normalized rules (i.e. first argument encodes program counter, number of arguments is fixed over all symbols, ...)
     * @param prefixOfFirstRun the variable prefix for the first run
     * @param prefixOfCurrentRun the variable prefix for the current run
     * @param factory some formula factory
     * @return a formulae encoding that the variables in the first and current run all have equal values
     */
    private static Formula<SMTLIBTheoryAtom> buildEqualities(
        final Set<IGeneralizedRule> normalizedRules,
        final String prefixOfFirstRun,
        final String prefixOfCurrentRun,
        final FormulaFactory<SMTLIBTheoryAtom> factory)
    {
        //We need some rule to get the number of arguments:
        final IGeneralizedRule someRule = normalizedRules.iterator().next();
        final IGeneralizedRule firstRunRule = someRule.getWithRenumberedVariables(prefixOfFirstRun);
        final IGeneralizedRule currentRunRule = someRule.getWithRenumberedVariables(prefixOfCurrentRun);
        final ImmutableList<TRSTerm> args = firstRunRule.getLeft().getArguments();
        final List<SMTLIBTheoryAtom> eqFormulae = new LinkedList<>();
        for (int i = 0; i < args.size(); i++) {
            final TRSVariable firstRunVariable = (TRSVariable) firstRunRule.getLeft().getArgument(i);
            final TRSVariable currentRunVariable = (TRSVariable) currentRunRule.getLeft().getArgument(i);
            eqFormulae.add(
                SMTLIBIntEquals.create(
                    SMTLIBIntVariable.create(firstRunVariable.getName()),
                    SMTLIBIntVariable.create(currentRunVariable.getName())
                )
            );
        }
        return factory.buildAnd(factory.buildTheoryAtoms(eqFormulae));
    }

    /**
     * @param smtAssignement some variable assignment provided by SMT
     * @param label a label marking the variables we are interested in
     * @return a map from abstract variable references to Long values.
     */
    public static Map<TRSVariable, TRSFunctionApplication> extractVariableAssignment(
        final Map<String, String> smtAssignement,
        final String label)
    {
        final Map<TRSVariable, TRSFunctionApplication> res = new LinkedHashMap<>();
        for (final Map.Entry<String, String> e : smtAssignement.entrySet()) {
            final String smtVarName = e.getKey();
            if (smtVarName.startsWith(label)) {
                final String varName = smtVarName.substring(label.length());
                final TRSVariable var = TRSTerm.createVariable("x" + varName);
                final TRSFunctionApplication value =
                    TRSTerm.createFunctionApplication(FunctionSymbol.create(e.getValue(), 0));
                res.put(var, value);
            }
        }
        return res;
    }

    /**
     * The proof of nontermination.
     * @author Marc Brockschmidt
     */
    private class IntTRSPeriodicNontermProof extends DefaultProof {
        /** The set of normalized rules generated. */
        private final Set<IGeneralizedRule> normalizedRules;

        /** The term for which we have a looping reduction. */
        private final TRSTerm witnessTerm;

        /**
         * @param rules The set of normalized rules generated.
         * @param witness The term for which we have a looping reduction.
         */
        public IntTRSPeriodicNontermProof(final Set<IGeneralizedRule> rules, final TRSTerm witness) {
            this.normalizedRules = rules;
            this.witnessTerm = witness;
        }

        /**
         * @return the proof as a nice string representation.
         * @param o an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();

            res.append("Normalized system to the following form:").append(o.linebreak());
            for (final IGeneralizedRule r : this.normalizedRules) {
                res.append(r.export(o)).append(o.linebreak());
            }

            res.append("Witness term starting non-terminating reduction: ").append(this.witnessTerm.toString());

            return res.toString();
        }
    }
}
