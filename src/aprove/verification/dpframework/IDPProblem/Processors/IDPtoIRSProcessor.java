/**
 *
 * @author 
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.Processors;

import immutables.*;
import immutables.Immutable.*;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Converts an IDPProblem to an IRSProblem.
 *
 * This is done by removing all positions whose type is neither integer nor
 * boolean. Remaining nested terms that an IRS cannot express are replaced by
 * fresh variables.
 */
public class IDPtoIRSProcessor extends IDPProcessor {
    // ================================================================================
    // isApplicable
    // ================================================================================

    /**
     * Checks if this processor is applicable to the IDP.
     */
    @Override
    public boolean isIDPApplicable(final IDPProblem iDP) {
        final IDPRuleAnalysis ruleA = iDP.getRuleAnalysis();

        // IRSs work on unbounded integers
        return !ruleA.hasRestrictedInt();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter) throws AbortionException {
        final Pair<IRSProblem, IDPtoIRSProof> conversion = this.IDPtoIRS(iDP);
        if (conversion == null) {
            return ResultFactory.unsuccessful("The IDP is not well-typed.");
        }
        return ResultFactory.proved(conversion.x, YNMImplication.SOUND, conversion.y);
    }

    /**
     * @return the IRS together with the proof of the conversion, or
     *         <code>null</code> if the IDP is not well-typed
     */
    private Pair<IRSProblem, IDPtoIRSProof> IDPtoIRS(final IDPProblem iDP) {
        final ImmutableSet<GeneralizedRule> idpPRules = iDP.getP();
        final ImmutableSet<GeneralizedRule> idpRRules = iDP.getR();
        final IDPPredefinedMap predefinedMap = iDP.getRuleAnalysis().getPreDefinedMap();

        // Build the filter which collects all positions that are neither
        // integer nor boolean
        final Set<GeneralizedRule> allRules = new LinkedHashSet<GeneralizedRule>();
        allRules.addAll(idpRRules);
        allRules.addAll(idpPRules);

        final CollectionMap<FunctionSymbol, Integer> filter = IDPTypeFilter.getOtherPositions(allRules, predefinedMap);
        if (filter == null) {
            return null;
        }

        final Set<HasFunctionSymbols> forbiddenSymbols = new LinkedHashSet<HasFunctionSymbols>();
        forbiddenSymbols.addAll(iDP.getQ().getExplicitTerms());
        forbiddenSymbols.addAll(idpPRules);
        forbiddenSymbols.addAll(idpRRules);
        final Set<FunctionSymbol> takenSymbols = CollectionUtils.getFunctionSymbols(forbiddenSymbols);

        final Map<FunctionSymbol, FunctionSymbol> freshNameMap = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

        // Apply the filter to the rules of the IDP nodes. R and the edge
        // conditions are not needed for the IRS.
        final Map<Node, GeneralizedRule> filteredRules = new LinkedHashMap<>();
        for (final Node node : iDP.getIdpGraph().getNodes()) {
            final GeneralizedRule rule = node.getRule();
            final TRSFunctionApplication newL = (TRSFunctionApplication) HelperClass.remove(rule.getLeft(), filter,
                    freshNameMap, takenSymbols, predefinedMap);
            final TRSTerm newR = HelperClass.remove(rule.getRight(), filter, freshNameMap, takenSymbols, predefinedMap);
            filteredRules.put(node, GeneralizedRule.create(newL, newR));
        }

        final IRSProblem irsProblem = this.toIRSProblem(filteredRules, predefinedMap);

        return new Pair<IRSProblem, IDPtoIRSProof>(irsProblem, new IDPtoIRSProof(filter));
    }

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

        // The fresh variable
        TRSVariable var = TRSTerm.createVariable(fng.getFreshName("var_" + term.getName(), false));

        // If any nested function symbol is not pre-defined or a bitwise
        // operation, which IRSs cannot express, return a free variable
        for (FunctionSymbol symbol : term.getFunctionSymbols()) {
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(symbol)) {
                return new ArithmeticElimination(null, var);
            }
            final PredefinedFunction<? extends Domain> func = IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(symbol);
            if (func != null && func.isBitwise()) {
                return new ArithmeticElimination(null, var);
            }
        }

        assert term instanceof TRSFunctionApplication;
        TRSFunctionApplication funApp = (TRSFunctionApplication) term;
        assert IDPPredefinedMap.DEFAULT_MAP.isPredefined(funApp.getFunctionSymbol());

        // A constant value v is replaced by a fresh variable x and the
        // constraint
        // v = x. Boolean constants (true and false) are replaced by integer
        // variables with value 1 or 0.
        // This is only necessary for the lhs, but doesn't harm to also have for
        // the rhs.
        if (IDPPredefinedMap.DEFAULT_MAP.isBooleanTrue(funApp.getFunctionSymbol())) {
            return new ArithmeticElimination(
                    TRSTerm.createFunctionApplication(
                            IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq,
                                    DomainFactory.INTEGER_INTEGER),
                            var,
                            PredefinedSemanticsFactory.getInt(BigIntImmutable.ONE, DomainFactory.INTEGERS).getTerm()),
                    var);
        } else if (IDPPredefinedMap.DEFAULT_MAP.isBooleanFalse(funApp.getFunctionSymbol())) {
            return new ArithmeticElimination(
                    TRSTerm.createFunctionApplication(
                            IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq,
                                    DomainFactory.INTEGER_INTEGER),
                            var,
                            PredefinedSemanticsFactory.getInt(BigIntImmutable.ZERO, DomainFactory.INTEGERS).getTerm()),
                    var);
        } else if (IDPPredefinedMap.DEFAULT_MAP.isInt(funApp.getFunctionSymbol(), DomainFactory.INTEGERS)) {
            return new ArithmeticElimination(TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    funApp), var);
        }

        // +(a,b)...
        // Arithmetic functions are moved 1:1 to the constraint and a fresh
        // variable is inserted.
        if (IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(funApp.getFunctionSymbol()).isArithmetic()) {
            TRSTerm constraint = TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    funApp);

            return new ArithmeticElimination(constraint, var);
        }

        // >(a,b)...
        // Relations/Boolean functions return a boolean, but IRSs only allow
        // integers.
        // Replace them by a new integer variable which is fixed to 1 if the
        // relation holds, and 0 otherwise.
        if (IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(funApp.getFunctionSymbol()).isRelation()
                || IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(funApp.getFunctionSymbol()).isBoolean()) {
            // replace with constant true, represented as 1, or false,
            // represented as 0, and add appropriate conditions

            // a > b holds
            // the variable replacing a > b is replaced by 1 (treated as true,
            // must also be replaced in the lhs of all rules)
            TRSTerm varIsTrue = TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    PredefinedSemanticsFactory.getInt(BigIntImmutable.ONE, DomainFactory.INTEGERS).getTerm());
            TRSTerm varIsFalse = TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    PredefinedSemanticsFactory.getInt(BigIntImmutable.ZERO, DomainFactory.INTEGERS).getTerm());

            TRSTerm relationIsTrue = IDPv2ToIDPv1Utilities.getConjunction(funApp, varIsTrue);
            TRSTerm relationIsFalse = IDPv2ToIDPv1Utilities.getConjunction(IDPv2ToIDPv1Utilities.negate(funApp),
                    varIsFalse);

            TRSTerm condition = IDPv2ToIDPv1Utilities.getDisjunction(relationIsTrue, relationIsFalse);
            // return new ArithmeticElimination(relationIsTrue, var);
            return new ArithmeticElimination(condition, var);
        }

        assert false : "encountered predefined but unhandled function symbol: " + funApp.getFunctionSymbol().toString();

        return new ArithmeticElimination(null, var);
    }

    /**
     * Converts the filtered rules of the IDP nodes to IRS rules.
     */
    private IRSProblem toIRSProblem(final Map<Node, GeneralizedRule> filteredRules,
            final IDPPredefinedMap predefinedMap) {
        final Set<IGeneralizedRule> rules = new LinkedHashSet<>();
        Set<String> usedNames = new LinkedHashSet<>();
        usedNames.addAll(CollectionUtils.getNames(CollectionUtils.getFunctionSymbols(filteredRules.values())));
        usedNames.addAll(CollectionUtils.getNames(CollectionUtils.getVariables(filteredRules.values())));
        FreshNameGenerator fng = new FreshNameGenerator(usedNames, FreshNameGenerator.APPEND_NUMBERS);

        // transform the rules to rules with no nested functions but with conditions
        for (final Map.Entry<Node, GeneralizedRule> entry : filteredRules.entrySet()) {
            final GeneralizedRule rule = entry.getValue();
            List<TRSTerm> rhsArgs = new ArrayList<>();
            List<TRSTerm> lhsArgs = new ArrayList<>();
            TRSTerm condition = IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getTerm();

            if (rule.getRight() instanceof TRSFunctionApplication) {
                TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
                TRSFunctionApplication lhs = (TRSFunctionApplication) rule.getLeft();
                // eliminate nested function calls:
                // if an argument is an arithmetic function with constant or
                // variable arguments, move it to the constraint
                // otherwise replace it by a fresh variable
                for (TRSTerm arg : rhs.getArguments()) {
                    ArithmeticElimination elim = this.eliminateNestedArithmetic(arg, fng);
                    rhsArgs.add(elim.replacement);
                    condition = IDPv2ToIDPv1Utilities.getConjunction(condition, elim.condition);

                }
                TRSTerm newRhs = TRSTerm.createFunctionApplication(rhs.getRootSymbol(),
                        ImmutableCreator.create(rhsArgs));

                for (TRSTerm arg : lhs.getArguments()) {
                    ArithmeticElimination elim = this.eliminateNestedArithmetic(arg, fng);
                    lhsArgs.add(elim.replacement);
                    condition = IDPv2ToIDPv1Utilities.getConjunction(condition, elim.condition);

                }
                TRSFunctionApplication newLhs = TRSTerm.createFunctionApplication(lhs.getRootSymbol(),
                        ImmutableCreator.create(lhsArgs));

                final TRSFunctionApplication condFA = (TRSFunctionApplication) condition;

                TRSTerm killedNot = IRSwTFormatTransformer.killNOT(condFA, predefinedMap);
                final Set<TRSTerm> newConds = killedNot.isVariable() ? Collections.singleton(killedNot)
                        : IRSwTFormatTransformer.killOR(
                                IRSwTFormatTransformer.killNE((TRSFunctionApplication) killedNot, predefinedMap),
                                predefinedMap);
                for (TRSTerm cond : newConds) {
                    IGeneralizedRule iRule = IGeneralizedRule.create(newLhs, newRhs, cond);
                    // iRule = IDPv2ToIDPv1Utilities.shuffleMatchings(iRule);
                    rules.add(iRule);
                }
            }
        }

        return new IRSProblem(ImmutableCreator.create(rules));
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public class IDPtoIRSProof extends DefaultProof {
        private final CollectionMap<FunctionSymbol, Integer> filter;

        public IDPtoIRSProof(final CollectionMap<FunctionSymbol, Integer> filter) {
            this.filter = filter;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result = new StringBuilder();

            result.append("The following positions were removed because their type is neither integer nor boolean:");
            result.append(o.linebreak());
            for (Entry<FunctionSymbol, Collection<Integer>> entry : this.filter.entrySet()) {
                result.append(
                        "function symbol: " + entry.getKey().getName() + ", removed positions: " + entry.getValue());
                result.append(o.cond_linebreak());
            }

            return result.toString();
        }
    }
}
