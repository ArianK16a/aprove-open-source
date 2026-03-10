/**
 *
 * @author 
 * @version $Id$
 */

package aprove.DPFramework.IDPProblem.Processors;

import immutables.Immutable.*;

import java.util.*;
import java.util.Map.*;
import java.util.logging.*;

import aprove.Complexity.LowerBounds.Types.*;
import aprove.DPFramework.*;
import aprove.DPFramework.BasicStructures.*;
import aprove.DPFramework.DPProblem.*;
import aprove.DPFramework.IDPProblem.*;
import aprove.DPFramework.IDPProblem.PfFunctions.*;
import aprove.DPFramework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.DPFramework.IDPProblem.PfFunctions.domains.*;
import aprove.DPFramework.IDPProblem.PfManager.*;
import aprove.DPFramework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.DPFramework.IDPProblem.idpGraph.*;
import aprove.DPFramework.IDPProblem.idpGraph.Node;
import aprove.DPFramework.IDPProblem.utility.*;
import aprove.DPFramework.TRSProblem.*;
import aprove.Framework.BasicStructures.*;
import aprove.Framework.Bytecode.Processors.ToIDPv1.*;
import aprove.Framework.IRSwT.Processors.FilterProcessors.IRSwTTempSortFilterProcessor.*;
import aprove.Framework.IntTRS.*;
import aprove.Framework.Logic.*;
import aprove.Framework.Utility.*;
import aprove.Framework.Utility.GenericStructures.*;
import aprove.Framework.Utility.Graph.*;
import aprove.GraphUserInterface.Factories.Solvers.*;
import aprove.Probabilistic.Termination.ADPProblem.AST.Processors.AST_ADPReductionPairProcessor.*;
import aprove.ProofTree.Export.*;
import aprove.ProofTree.Export.Utility.*;
import aprove.ProofTree.Obligations.*;
import aprove.ProofTree.Proofs.Proof.DefaultProof;
import aprove.Strategies.Abortions.*;
import aprove.Strategies.Annotations.*;
import aprove.Strategies.ExecutableStrategies.*;
import aprove.Strategies.UserStrategies.*;

/**
 * Converts an IDPProblem to an IRSProblem.
 *
 * The IDPProblem must not contain any terms. nested function calls will be
 * replaced by fresh variables
 */
public class IDPToIRSProcessor extends IDPProcessor {
    // ================================================================================
    // Properties
    // ================================================================================

    private final static Logger log = Logger.getLogger("aprove.DPFramework.IDPProblem.Processors.IDPToIRSProcessor");

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    // ================================================================================
    // isApplicable
    // ================================================================================

    /**
     * Checks if this processor is applicable to the IDP.
     */
    @Override
    public boolean isIDPApplicable(final IDPProblem iDP) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    private class ArithmeticElimination {
        public TRSTerm condition;
        public TRSTerm replacement;

        public ArithmeticElimination(TRSTerm condition, TRSTerm replacement) {
            this.condition = condition;
            this.replacement = replacement;
        }
    }

    /**
     * 
     * @param term
     * @return the constraint necessary to replace term by
     */
    private ArithmeticElimination eliminateNestedArithmetic(TRSTerm term, FreshNameGenerator fng) {
        if (term instanceof TRSVariable) {
            return new ArithmeticElimination(null, term);
        }

        TRSVariable var = TRSTerm.createVariable(fng.getFreshName(term.getName(), false));
        // If any nested function symbol is not pre-defined, return a free
        // variable
        for (FunctionSymbol symbol : term.getFunctionSymbols()) {
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(symbol)) {
                return new ArithmeticElimination(null, var);
            }
        }

        assert term instanceof TRSFunctionApplication;
        TRSFunctionApplication funApp = (TRSFunctionApplication) term;
        assert IDPPredefinedMap.DEFAULT_MAP.isPredefined(funApp.getFunctionSymbol());

        // +(a,b)...
        if (IDPPredefinedMap.DEFAULT_MAP.isArithmeticFunction(funApp.getFunctionSymbol())) {
            // the new variables used in the constraint
            List<TRSTerm> newArgs = new ArrayList<>();
            List<TRSTerm> subConstraints = new ArrayList<>();

            for (TRSTerm arg : funApp.getArguments()) {
                ArithmeticElimination childElim = this.eliminateNestedArithmetic(arg, fng);
                newArgs.add(childElim.replacement);
                if (childElim.condition != null) {
                    subConstraints.add(childElim.condition);
                }
            }

            TRSTerm constraintRhs = TRSTerm.createFunctionApplication(funApp.getRootSymbol(), newArgs);

            TRSTerm constraint = TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    constraintRhs);

            for (TRSTerm subConstraint : subConstraints) {
                constraint = IDPv2ToIDPv1Utilities.getConjunction(constraint, subConstraint);
            }
            return new ArithmeticElimination(constraint, var);
        }

        // >(a,b)...
        if (IDPPredefinedMap.DEFAULT_MAP.isIntegerRelation(funApp.getFunctionSymbol())) {
            // replace with constant true or false and add appropriate
            // condition

            // the new variables used in the constraint
            List<TRSTerm> newArgs = new ArrayList<>();
            List<TRSTerm> subConstraints = new ArrayList<>();

            for (TRSTerm arg : funApp.getArguments()) {
                ArithmeticElimination childElim = this.eliminateNestedArithmetic(arg, fng);
                newArgs.add(childElim.replacement);
                if (childElim.condition != null) {
                    subConstraints.add(childElim.condition);
                }
            }

            TRSTerm constraint = TRSTerm.createFunctionApplication(funApp.getRootSymbol(), newArgs);

            for (TRSTerm subConstraint : subConstraints) {
                constraint = IDPv2ToIDPv1Utilities.getConjunction(constraint, subConstraint);
            }

            // TODO also add false with negated condition?
            return new ArithmeticElimination(constraint, IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getTerm());
        }

        // 6, 7,...
        if (IDPPredefinedMap.DEFAULT_MAP.isInt(funApp.getFunctionSymbol(), DomainFactory.INTEGERS)) {
            return new ArithmeticElimination(null, term);
        }

        return new ArithmeticElimination(null, var);
    }

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter) throws AbortionException {
        final Set<IGeneralizedRule> rules = new LinkedHashSet<>();
        Set<String> usedNames = new LinkedHashSet<>();
        usedNames.addAll(CollectionUtils.getNames(CollectionUtils.getFunctionSymbols(iDP.getP())));
        usedNames.addAll(CollectionUtils.getNames(CollectionUtils.getVariables(iDP.getP())));
        FreshNameGenerator fng = new FreshNameGenerator(usedNames, FreshNameGenerator.APPEND_NUMBERS);

        // transform iDP to rules with no nested functions but with conditions
        for (GeneralizedRule rule : iDP.getP()) {
            List<TRSTerm> args = new ArrayList<>();
            TRSTerm condition = null;

            if (rule.getRight() instanceof TRSFunctionApplication) {
                TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
                // eliminate nested function calls:
                // if an argument is an arithmetic function with constant or
                // variable arguments, move it to the constraint
                // otherwise replace it by a fresh variable
                for (TRSTerm arg : rhs.getArguments()) {
                    ArithmeticElimination elim = this.eliminateNestedArithmetic(arg, fng);
                    args.add(elim.replacement);
                    if (elim.condition == null) {
                        continue;
                    }
                    condition = IDPv2ToIDPv1Utilities.getConjunction(condition, elim.condition);

                }
                TRSTerm newRhs = TRSTerm.createFunctionApplication(rhs.getRootSymbol(), ImmutableCreator.create(args));

                final IGeneralizedRule iRule = IGeneralizedRule.create(rule.getLeft(), newRhs, condition);
                rules.add(iRule);
            }
        }
        final IRSProblem irs = new IRSProblem(ImmutableCreator.create(rules));

        final IDPToIRSProof proof = new IDPToIRSProof();

        return ResultFactory.proved(irs, YNMImplication.SOUND, proof);

    }

    private TrsTypes runTypeInference(final Set<GeneralizedRule> rules) {
        Set<FunctionSymbol> allSymbols = CollectionUtils.getFunctionSymbols(rules);
        Set<FunctionSymbol> definedSymbols = CollectionUtils.getRootSymbols(rules);

        // Predefined symbols don't occur as root symbols but are defined too
        for (final FunctionSymbol fun : allSymbols) {
            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(fun)) {
                definedSymbols.add(fun);
            }
        }

        // Convert the rules to the type expected for TypeInference
        Set<aprove.Complexity.LowerBounds.BasicStructures.Rule> newRules = new LinkedHashSet<>();
        for (final GeneralizedRule rule : rules) {
            newRules.add(new aprove.Complexity.LowerBounds.BasicStructures.Rule(rule.getLeft(), rule.getRight()));
        }

        return TypeInference.infer(newRules, allSymbols, definedSymbols);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public class IDPToIRSProof extends DefaultProof implements DOT_Able {

        /** Obligation node where substrategy has been applied. */

        public IDPToIRSProof() {
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("No proof yet :(");
            result.append(o.linebreak());
            return result.toString();
        }

        @Override
        public String toDOT() {
            return "";
            // return this.idp.getIdpGraph().toDOT();
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

}
