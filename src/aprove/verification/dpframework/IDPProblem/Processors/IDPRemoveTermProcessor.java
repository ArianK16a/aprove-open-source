/**
 *
 * @author 
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.Processors;

import immutables.*;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
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
 * Converts an IDP into an IRS by removing all arguments that are neither
 * integer nor boolean, see {@link IDPProjection}. Remaining nested terms that
 * an IRS cannot express are replaced by fresh variables. R and the edge
 * conditions are dropped, so the result is only SOUND.
 *
 * With <code>TempFilter</code>, the IRS is only used to remove nodes from the
 * IDP, see {@link IDPTemporaryFilter}.
 */
public class IDPRemoveTermProcessor extends IDPProcessor {
    // ================================================================================
    // Properties
    // ================================================================================

    private final boolean tempFilter;
    private final UserStrategy strategy;
    private final int time;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================
    @ParamsViaArgumentObject
    public IDPRemoveTermProcessor(final Arguments arguments) {
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
        return !ruleA.hasRestrictedInt();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter) {
        // Not used, as process passes the runtime information
        throw new UnsupportedOperationException();
    }

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {
        final IDPProjection projection = IDPProjection.removeOthers(iDP);
        if (projection == null) {
            return ResultFactory.unsuccessful("The IDP is not well-typed.");
        }
        final IDPConversion<IGeneralizedRule> conversion = this.toIRS(iDP, projection);
        if (!this.tempFilter) {
            return ResultFactory.proved(conversion.getTarget(), YNMImplication.SOUND, conversion.getProof());
        }
        return IDPTemporaryFilter.run(iDP, conversion, this.strategy, this.time, aborter, rti, this);
    }

    /**
     * @return the IRS together with the mapping back to the IDP nodes
     */
    private IDPConversion<IGeneralizedRule> toIRS(final IDPProblem iDP, final IDPProjection projection) {
        // Maps each IRS rule back to the IDP node it was created from. R and
        // the edge conditions are not needed for the IRS.
        final CollectionMap<IGeneralizedRule, Node> inverseNodes = new CollectionMap<>();
        final IRSProblem irsProblem = this.toIRSProblem(projection.getPairs(),
                iDP.getRuleAnalysis().getPreDefinedMap(), inverseNodes);

        return new IDPConversion<>(irsProblem, inverseNodes,
                obl -> obl instanceof IRSwTProblem ? ((IRSwTProblem) obl).getRules() : null,
                new IDPRemoveTermProof(projection));
    }

    /**
     * The replacement of an argument together with the condition it has to
     * satisfy (or <code>null</code> if there is none).
     */
    private static class ArgumentElimination {
        private final TRSTerm replacement;
        private final TRSTerm condition;

        private ArgumentElimination(final TRSTerm replacement, final TRSTerm condition) {
            this.replacement = replacement;
            this.condition = condition;
        }
    }

    /**
     * Replaces an argument of a rule by a fresh variable, since IRS rules
     * only have variables below the root of the lhs and no booleans. An
     * integer term t is replaced by a variable x with the condition x = t,
     * a boolean term b by an integer variable x with
     * (b && x = 1) || (!b && x = 0), where boolean variables in b stand for
     * the integers 1 and 0. Subterms that an IRS cannot express are replaced
     * by unconstrained variables first, see
     * {@link #abstractInexpressible(TRSTerm, FreshNameGenerator)}.
     */
    private static ArgumentElimination eliminateArgument(final TRSTerm argument, final FreshNameGenerator fng) {
        final TRSTerm term = IDPRemoveTermProcessor.abstractInexpressible(argument, fng);
        if (term instanceof TRSVariable) {
            return new ArgumentElimination(term, null);
        }
        final TRSVariable var = TRSTerm.createVariable(fng.getFreshName("var_" + term.getName(), false));

        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        final FunctionSymbol root = ((TRSFunctionApplication) term).getRootSymbol();
        if (predefinedMap.isBooleanTrue(root)) {
            return new ArgumentElimination(var, IDPRemoveTermProcessor.equal(var, BigIntImmutable.ONE));
        }
        if (predefinedMap.isBooleanFalse(root)) {
            return new ArgumentElimination(var, IDPRemoveTermProcessor.equal(var, BigIntImmutable.ZERO));
        }
        final PredefinedFunction<? extends Domain> func = predefinedMap.getPredefinedFunction(root);
        if (predefinedMap.isInt(root, DomainFactory.INTEGERS) || func.isArithmetic()) {
            return new ArgumentElimination(var, IDPRemoveTermProcessor.equal(var, term));
        }
        if (func.isRelation() || func.isBoolean()) {
            final TRSTerm cond = IDPRemoveTermProcessor.encodeBooleanVariables(term);
            final TRSTerm isTrue =
                IDPv2ToIDPv1Utilities.getConjunction(cond, IDPRemoveTermProcessor.equal(var, BigIntImmutable.ONE));
            final TRSTerm isFalse = IDPv2ToIDPv1Utilities.getConjunction(IDPv2ToIDPv1Utilities.negate(cond),
                    IDPRemoveTermProcessor.equal(var, BigIntImmutable.ZERO));
            return new ArgumentElimination(var, IDPv2ToIDPv1Utilities.getDisjunction(isTrue, isFalse));
        }
        assert false : "encountered predefined but unhandled function symbol: " + root;
        return new ArgumentElimination(var, null);
    }

    /**
     * Replaces the maximal subterms that an IRS cannot express, e.g.
     * constructor terms, calls of functions defined in R and bitwise
     * operations, by fresh unconstrained variables. Every occurrence gets
     * its own variable, as two calls of the same function do not have to
     * yield the same result. For example, 5 + g(x) becomes 5 + y.
     */
    private static TRSTerm abstractInexpressible(final TRSTerm term, final FreshNameGenerator fng) {
        if (term instanceof TRSVariable) {
            return term;
        }
        final TRSFunctionApplication fa = (TRSFunctionApplication) term;
        final FunctionSymbol root = fa.getRootSymbol();
        final PredefinedFunction<? extends Domain> func = IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(root);
        if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(root) || (func != null && func.isBitwise())) {
            return TRSTerm.createVariable(fng.getFreshName("var_" + root.getName(), false));
        }
        final List<TRSTerm> args = new ArrayList<>();
        for (final TRSTerm arg : fa.getArguments()) {
            args.add(IDPRemoveTermProcessor.abstractInexpressible(arg, fng));
        }
        return TRSTerm.createFunctionApplication(root, args);
    }

    /**
     * Replaces the variables that occur as boolean operands in the term, e.g.
     * b in !b or b && x > 0, by b = 1. Booleans are integers in the IRS,
     * where TRUE is 1 and FALSE is 0.
     */
    private static TRSTerm encodeBooleanVariables(final TRSTerm term) {
        if (term instanceof TRSVariable) {
            return IDPRemoveTermProcessor.equal(term, BigIntImmutable.ONE);
        }
        final TRSFunctionApplication fa = (TRSFunctionApplication) term;
        final PredefinedFunction<? extends Domain> func =
            IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(fa.getRootSymbol());
        if (func == null) {
            return term;
        }
        final List<TRSTerm> args = new ArrayList<>();
        for (int i = 0; i < fa.getArguments().size(); i++) {
            final TRSTerm arg = fa.getArgument(i);
            args.add(func.getDomains().get(i) instanceof BooleanDomain
                ? IDPRemoveTermProcessor.encodeBooleanVariables(arg) : arg);
        }
        return TRSTerm.createFunctionApplication(fa.getRootSymbol(), args);
    }

    private static TRSTerm equal(final TRSTerm left, final TRSTerm right) {
        return TRSTerm.createFunctionApplication(
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER),
                left, right);
    }

    private static TRSTerm equal(final TRSTerm left, final BigIntImmutable right) {
        return IDPRemoveTermProcessor.equal(left,
                PredefinedSemanticsFactory.getInt(right, DomainFactory.INTEGERS).getTerm());
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
                for (TRSTerm arg : rhs.getArguments()) {
                    final ArgumentElimination elim = IDPRemoveTermProcessor.eliminateArgument(arg, fng);
                    rhsArgs.add(elim.replacement);
                    condition = IDPv2ToIDPv1Utilities.getConjunction(condition, elim.condition);
                }
                TRSTerm newRhs = TRSTerm.createFunctionApplication(rhs.getRootSymbol(),
                        ImmutableCreator.create(rhsArgs));

                for (TRSTerm arg : lhs.getArguments()) {
                    final ArgumentElimination elim = IDPRemoveTermProcessor.eliminateArgument(arg, fng);
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

    public static class IDPRemoveTermProof extends DefaultProof {
        private final IDPProjection projection;

        public IDPRemoveTermProof(final IDPProjection projection) {
            this.projection = projection;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return this.projection.export(o);
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

    public static class Arguments {
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
