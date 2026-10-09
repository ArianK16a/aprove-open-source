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
import aprove.strategies.UserStrategies.*;
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
 *
 * With <code>TempFilter</code>, the IRS is only used to remove nodes from the
 * IDP, see {@link IDPTemporaryFilter}.
 */
public class IDPtoIRSProcessor extends IDPProcessor {
    // ================================================================================
    // Properties
    // ================================================================================

    /**
     * When do we want to be applicable?
     */
    private final Applicability apply;

    private final boolean tempFilter;
    private final UserStrategy strategy;
    private final int time;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================
    @ParamsViaArgumentObject
    public IDPtoIRSProcessor(final Arguments arguments) {
        this.apply = arguments.apply;
        this.tempFilter = arguments.tempFilter;
        this.strategy = arguments.strategy;
        this.time = arguments.time;
    }

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
        if (ruleA.hasRestrictedInt()) {
            return false;
        }
        switch (this.apply) {
        case ALWAYS:
            return true;
        case INTONLY:
            final IDPPredefinedMap predefinedMap = ruleA.getPreDefinedMap();
            for (final FunctionSymbol sym : IDPtoIRSProcessor.getArgumentSymbols(iDP.getP())) {
                final PredefinedFunction<? extends Domain> func = predefinedMap.getPredefinedFunction(sym);
                // Constructors and bitwise operations would be replaced by
                // fresh variables
                if (!predefinedMap.isPredefined(sym) || (func != null && func.isBitwise())) {
                    return false;
                }
                // The IRS backend only approximates / and %, so problems
                // that depend on them are left to the IDP processors
                if (predefinedMap.isDivOrMod(sym)) {
                    return false;
                }
            }
            return true;
        default:
            throw new aprove.verification.oldframework.Exceptions.NotYetHandledException("Check for "
                    + this.apply + " not handled yet!");
        }
    }

    /**
     * @return the function symbols that occur below the root symbols of the
     *         rules
     */
    private static Set<FunctionSymbol> getArgumentSymbols(final Collection<GeneralizedRule> rules) {
        final Set<FunctionSymbol> symbols = new LinkedHashSet<>();
        for (final GeneralizedRule rule : rules) {
            for (final TRSTerm side : Arrays.asList(rule.getLeft(), rule.getRight())) {
                if (side instanceof TRSFunctionApplication) {
                    for (final TRSTerm arg : ((TRSFunctionApplication) side).getArguments()) {
                        symbols.addAll(arg.getFunctionSymbols());
                    }
                }
            }
        }
        return symbols;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter) throws AbortionException {
        final IDPConversion<IGeneralizedRule> conversion = this.IDPtoIRS(iDP);
        if (conversion == null) {
            return ResultFactory.unsuccessful("The IDP is not well-typed.");
        }
        if (!this.tempFilter) {
            return ResultFactory.proved(conversion.getTarget(), YNMImplication.SOUND, conversion.getProof());
        }
        return IDPTemporaryFilter.run(iDP, conversion, this.strategy, this.time, aborter, this.rti, this);
    }

    /**
     * @return the IRS together with the mapping back to the IDP nodes, or
     *         <code>null</code> if the IDP is not well-typed
     */
    private IDPConversion<IGeneralizedRule> IDPtoIRS(final IDPProblem iDP) {
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

        // Maps each IRS rule back to the IDP node it was created from
        final CollectionMap<IGeneralizedRule, Node> inverseNodes = new CollectionMap<>();
        final IRSProblem irsProblem = this.toIRSProblem(filteredRules, predefinedMap, inverseNodes);

        return new IDPConversion<>(irsProblem, inverseNodes,
                obl -> obl instanceof IRSwTProblem ? ((IRSwTProblem) obl).getRules() : null,
                new IDPtoIRSProof(filter));
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
     *
     * @param inverseNodes is filled with the IDP node each IRS rule was
     *            created from
     */
    private IRSProblem toIRSProblem(final Map<Node, GeneralizedRule> filteredRules,
            final IDPPredefinedMap predefinedMap, final CollectionMap<IGeneralizedRule, Node> inverseNodes) {
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
                    inverseNodes.add(iRule, entry.getKey());
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

    // ================================================================================
    // Arguments Class
    // ================================================================================

    /**
     * When the processor is applicable.
     */
    public static enum Applicability {
        /**
         * Always (for unbounded integers). Nested terms that an IRS cannot
         * express, such as constructor terms, are replaced by fresh variables.
         */
        ALWAYS,

        /**
         * Only if nothing but variables and predefined operations occurs
         * below the root of the P rules, so no term has to be replaced by a
         * fresh variable. Bitwise operations are excluded as they would be
         * replaced, and / and % because the IRS backend only approximates
         * them.
         */
        INTONLY,
    }

    public static class Arguments {
        // when do we want to be applicable?
        public Applicability apply = Applicability.ALWAYS;

        /**
         * Whether the IRS is only used to remove nodes from the IDP. If true,
         * `strategy` is executed on the IRS and the nodes whose rules it
         * removed are removed from the IDP. If false, the IRS is returned.
         */
        boolean tempFilter = false;

        /** Strategy to execute on the IRS if `tempFilter` is set. */
        UserStrategy strategy;

        /** Time limit for `strategy`. */
        int time = 42042;

        public void setTempFilter(final boolean tempFilter) {
            this.tempFilter = tempFilter;
        }

        public void setStrategy(final String strategyName) {
            this.strategy = new VariableStrategy(strategyName);
        }

        public void setTime(final int timeVal) {
            this.time = timeVal;
        }
    }
}
