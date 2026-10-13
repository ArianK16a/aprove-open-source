/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class IDPGInterpretation extends GInterpretation<BigIntImmutable> {

    public static enum ConstantType {
        StrictOrientation("bso_", null, null), CompareToNonInfConstant("bni_", null, null), ActiveCondition("ac", null,
                null), UsableInc_0("buInc0_", true, RelDependency.Independent), UsableInc_m1("buInc-1_", true,
                RelDependency.Decreasing), UsableInc_1("buInc1_", true, RelDependency.Increasing), UsableInc_2(
                "buInc2_", true, RelDependency.Wild), UsableDec_0("buDec0_", false, RelDependency.Independent), UsableDec_m1(
                "buDec-1_", false, RelDependency.Decreasing), UsableDec_1("buDec1_", false, RelDependency.Increasing), UsableDec_2(
                "buDec2_", false, RelDependency.Wild);

        private final String prefix;
        private final Boolean increasing;
        private final RelDependency csar;

        ConstantType(final String prefix, final Boolean increasing, final RelDependency csar) {
            this.prefix = prefix;
            this.increasing = increasing;
            this.csar = csar;
        }

        public Boolean getIncreasing() {
            return this.increasing;
        }

        public RelDependency getCsar() {
            return this.csar;
        }

        public RelDependency total() {
            if (this.increasing) {
                return this.csar;
            } else {
                switch (this.csar) {
                case Increasing:
                    return RelDependency.Decreasing;
                case Decreasing:
                    return RelDependency.Increasing;
                case Independent:
                    return RelDependency.Independent;
                default:
                    return RelDependency.Wild;
                }
            }
        }

        public String getPrefix() {
            return this.prefix;
        }
    }

    public static final String[] contextExtensions = new String[] {"_dec", "_inc" };

    /**
     * The pgrefix used for variables that will be used for v_f_i.
     */
    public static final String V_f_i_PREFIX = "f_";

    public static final String ContextSwitchPrefix = "cs_";

    /**
     * @param factory The GPolyFactory that will be used to create new
     * OrderPolys.
     * @param innerFactory This factory will be used to create coefficients for
     * the OrderPolys.
     * @param constraintFactory This factory will be used to create constraints.
     * @param <BigIntImmutable> The type of the coefficients.
     * @param inner A FlatteningVisitor that is able to flatten the inner
     * inner polynomials.
     * @param outer A FlatteningVisitor that is able to flatten the outer
     * polynomials.
     * @param coeffOrderParam A CoeffOrder that is able to put some coefficient
     * of type BigIntImmutable in relation to 0.
     * @param citationsParam The citations of the techniques used here
     * (e.g. POLO).
     * @return an empty interpretation.
     * @param maxSimpleDegree The maximum degree of monomials constructed
     * @param maxCoeffValueParam The maximum value of coefficients occurring in the
     * polynomials of predefined functions
     * in simple or simple mixed mode.
     * @throws AbortionException
     */
    public static IDPGInterpretation create(final boolean isNat,
        final boolean isTupleNat,
        final IDPRuleAnalysis ruleAnalysis,
        final IdpShapeHeuristic maxHeuristic,
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory,
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFactory,
        final ConstraintFactory<BigIntImmutable> constraintFactory,
        final FlatteningVisitor<BigIntImmutable, GPolyVar> inner,
        final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outer,
        final CoeffOrder<BigIntImmutable> coeffOrderParam,
        final List<Citation> citationsParam,
        final OPCRange<BigIntImmutable> coeffRange,
        final BigIntImmutable maxCoeffValueParam,
        final Abortion aborter) throws AbortionException {
        return new IDPGInterpretation(isNat, isTupleNat, ruleAnalysis, maxHeuristic, factory, innerFactory,
            constraintFactory, inner, outer, coeffOrderParam, citationsParam, coeffRange, maxCoeffValueParam, aborter);
    }

    /**
     * maximum value of the coefficients occurring in interpretations of predefined functions
     */
    protected final BigIntImmutable maxPredefCoeffValue;
    protected final BigIntImmutable maxPredefCoeffValueMinusOne;
    protected final OPCRange<BigIntImmutable> coeffRange;
    protected final BigIntImmutable rangeShift;
    protected final GPoly<BigIntImmutable, GPolyVar> rangeShiftPoly;
    protected final BigIntImmutable natRangeShift;
    protected final GPoly<BigIntImmutable, GPolyVar> natRangeShiftPoly;
    protected final OPCRange<BigIntImmutable> normedCoeffRange;
    protected final Map<FunctionSymbol, Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>> v_f_i;
    protected final Map<FunctionSymbol, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>> v_f_i_Encodings;
    protected final Set<OrderPolyConstraint<BigIntImmutable>> usableRulesConstraints;
    protected final Set<OrderPolyConstraint<BigIntImmutable>> contextUsableRulesConstraints;

    /**
     * Cached IExtendedAfs after specialization
     */
    protected volatile IExtendedAfs extendedAfs;

    private final Map<ConstantType, Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>> boolConstants;
    private final Map<ConstantType, Map<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>> boolTermConstants;

    private final Map<GeneralizedRule, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>> ruleLogVars;
    private final Map<TRSTerm, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>> termLogVars;

    private final OPCRange<BigIntImmutable> boolRange;

    /**
     * context sensitive cache for context sensitive interpretations (div, mod, ...)
     * contains number of possible context decisions + the OrderPoly that represents all of them (switching variable)
     * FunctionSymbol -> PathToRoot -> Arguments -> Polynom
     */
    private final Map<FunctionSymbol, Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>> contextPol;

    /**
     * context sensitive cache for boolean switch coefficients
     */
    private final Map<List<ImmutablePair<FunctionSymbol, Integer>>, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> contextBoolSwitchCache;

    /**
     * which context sensitive symbols can be replaced by non context sensitive ones?
     * e.g. /@z can be replaced by /@z_inc when used at increasing positions
     * and by /@z_dec when used at decreasing positions etc...
     * This is initialized during specialization!
     */
    private final Map<FunctionSymbol, Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, FunctionSymbol>> contextSensitiveReplacements;

    protected final IdpShapeHeuristic maxHeuristic;

    protected final IDPRuleAnalysis ruleAnalysis;
    protected final IDPPredefinedMap predefinedMap;

    protected final boolean isNat;
    protected final boolean isTupleNat;
    protected final ImmutableSet<FunctionSymbol> tupleSymbols;

    protected final Graph<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>, Object> activeHierarchy;
    protected final Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>> activeRoot;
    protected final Map<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>> activeMapping;

    protected IDPGInterpretation(final boolean isNat, final boolean isTupleNat, final IDPRuleAnalysis ruleAnalysis,
            final IdpShapeHeuristic maxHeuristic,
            final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factoryParam,
            final GPolyFactory<BigIntImmutable, GPolyVar> innerFactoryParam,
            final ConstraintFactory<BigIntImmutable> constraintFactoryParam,
            final FlatteningVisitor<BigIntImmutable, GPolyVar> inner,
            final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outer,
            final CoeffOrder<BigIntImmutable> coeffOrderParam, final List<Citation> citationsParam,
            final OPCRange<BigIntImmutable> coeffRange, final BigIntImmutable maxCoeffValueParam, final Abortion aborter)
            throws AbortionException {
        super(factoryParam, innerFactoryParam, constraintFactoryParam, inner, outer, coeffOrderParam, citationsParam);
        assert (this.ring.isRing());
        // System.err.println("COEFF RANGE: " + coeffRange.getList().get(0).x + " - " + coeffRange.getList().get(0).y);
        this.tupleSymbols = ruleAnalysis.getPAnalysis().getRootSymbols();
        this.isNat = isNat;
        if (isTupleNat && !isNat) {
            throw new IllegalArgumentException("must be nat if tupleNat");
        }
        this.isTupleNat = isTupleNat;
        this.rangeShift = coeffRange.getList().get(0).x;
        this.rangeShiftPoly = this.factory.getInnerFactory().buildFromCoeff(this.rangeShift);
        if (this.rangeShift.getBigInt().signum() >= 0) {
            this.natRangeShift = this.rangeShift;
            this.natRangeShiftPoly = this.rangeShiftPoly;
        } else {
            this.natRangeShift = BigIntImmutable.ZERO;
            this.natRangeShiftPoly = this.factory.getInnerFactory().zero();
        }
        this.normedCoeffRange =
            new OPCRange<BigIntImmutable>(BigIntImmutable.ZERO, ((Ring<BigIntImmutable>) this.ring).minus(
                coeffRange.getList().get(0).y, this.rangeShift));
        this.coeffRange = coeffRange;
        this.maxPredefCoeffValue = maxCoeffValueParam;
        this.maxPredefCoeffValueMinusOne =
            BigIntImmutable.create(this.maxPredefCoeffValue.getBigInt().subtract(BigInteger.ONE));
        this.v_f_i =
            new LinkedHashMap<FunctionSymbol, Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>();
        this.v_f_i_Encodings =
            new LinkedHashMap<FunctionSymbol, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>>();
        this.usableRulesConstraints = new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        // initialize boolConstants
        this.boolConstants =
            new LinkedHashMap<ConstantType, Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>>();
        this.boolTermConstants =
            new LinkedHashMap<ConstantType, Map<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>>();
        this.ruleLogVars =
            new LinkedHashMap<GeneralizedRule, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>>();
        this.termLogVars =
            new LinkedHashMap<TRSTerm, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>>();
        for (final ConstantType type : ConstantType.values()) {
            this.boolConstants.put(
                type,
                new LinkedHashMap<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>());
            this.boolTermConstants.put(type,
                new LinkedHashMap<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>());
        }
        this.boolRange = new OPCRange<BigIntImmutable>(BigIntImmutable.ZERO, BigIntImmutable.ONE);
        this.contextPol =
            new LinkedHashMap<FunctionSymbol, Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>>();
        this.contextUsableRulesConstraints = new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        this.contextBoolSwitchCache =
            new LinkedHashMap<List<ImmutablePair<FunctionSymbol, Integer>>, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>();
        this.contextSensitiveReplacements =
            new LinkedHashMap<FunctionSymbol, Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, FunctionSymbol>>();
        this.ruleAnalysis = ruleAnalysis;
        this.predefinedMap = ruleAnalysis.getPreDefinedMap();
        this.maxHeuristic = maxHeuristic;
        this.activeHierarchy =
            new Graph<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>, Object>();
        this.activeRoot =
            new Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>>(
                new ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>(
                    ImmutableCreator.create(Collections.<ImmutablePair<FunctionSymbol, Integer>>emptySet()), null));
        this.activeHierarchy.addNode(this.activeRoot);
        this.activeMapping =
            new LinkedHashMap<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>();

        final GInterpretationMode<BigIntImmutable> imode = new GInterpretationModeLinear<BigIntImmutable>();
        this.extend(PredefinedSemanticsFactory.BOOLEAN_FS_TRUE, imode, aborter);
        this.extend(PredefinedSemanticsFactory.BOOLEAN_FS_FALSE, imode, aborter);
        // extend(PredefinedFunction.Func.undefined.getSym(), imode);
    }

    protected boolean isContextFunction(final FunctionSymbol fs) {
        final PredefinedFunction<? extends Domain> func = this.predefinedMap.getPredefinedFunction(fs);
        if (func != null) {
            return func.getFunc() == Func.Div || func.getFunc() == Func.Mod;
        } else {
            return false;
        }
    }

    public boolean isContextSensitive(final TRSTerm t) {
        final Set<FunctionSymbol> funcs = t.getFunctionSymbols();
        for (final FunctionSymbol func : funcs) {
            if (this.isContextFunction(func)) {
                return true;
            }
        }
        return false;
    }

    protected RelDependency getPredefinedV_f_i(final FunctionSymbol fs, final int argNr) {
        final PredefinedFunction func = this.predefinedMap.getPredefinedFunction(fs);
        if (func != null) {
            if (this.isNat) {
                return RelDependency.Independent;
            } else {
                switch (func.getFunc()) {
                case Div:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Wild;
                    case 1:
                        return RelDependency.Wild;
                    }
                    break;
                case Mod:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Wild;
                    case 1:
                        return RelDependency.Wild;
                    }
                    break;
                case Eq:
                case Neq:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Wild;
                    case 1:
                        return RelDependency.Wild;
                    }
                    break;
                case Ge:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Independent;
                    case 1:
                        return RelDependency.Independent;
                    }
                    break;
                case Gt:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Independent;
                    case 1:
                        return RelDependency.Independent;
                    }
                    break;
                case Lt:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Independent;
                    case 1:
                        return RelDependency.Independent;
                    }
                    break;
                case Le:
                    switch (argNr) {
                    case 0:
                        return RelDependency.Independent;
                    case 1:
                        return RelDependency.Independent;
                    }
                    break;
                }
            }
        }
        return null;
    }

    /**
     * Interprets a term t with a GPoly, built up using
     * the polynomial interpretations of its function symbols.
     *
     * @param t the term to be interpreted
     * @return the polynomial which corresponds to t in this
     */
    @Override
    @Deprecated
    public OrderPoly<BigIntImmutable> interpretTerm(final TRSTerm t, final Abortion aborter) throws AbortionException {
        return this.interpretTerm(t, RelDependency.Increasing, aborter);
    }

    public OrderPoly<BigIntImmutable> interpretTerm(final TRSTerm t, final RelDependency k, final Abortion aborter)
            throws AbortionException {
        // System.err.println("interpretTerm " + t + " " + k);
        if (Globals.useAssertions) {
            assert (k != null) : t;
        }
        return this.interpretTerm(new Pair<RelDependency, Stack<ImmutablePair<FunctionSymbol, Integer>>>(k,
            new Stack<ImmutablePair<FunctionSymbol, Integer>>()), t, aborter);
    }

    protected OrderPoly<BigIntImmutable> interpretTerm(final Pair<RelDependency, Stack<ImmutablePair<FunctionSymbol, Integer>>> kPathToRoot,
        final TRSTerm t,
        final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert (t != null && (t instanceof TRSFunctionApplication) || (t instanceof TRSVariable));
            // if other terms should ever be created, the below code
            // needs to be checked
        }
        OrderPoly<BigIntImmutable> result;
        final Stack<ImmutablePair<FunctionSymbol, Integer>> pathToRoot = kPathToRoot.y;
        if (t.isVariable()) { // easy: Variable
            result =
                this.factory.concat(this.factory.getCoeffOne(),
                    this.factory.buildVariable(GAtomicVar.createVariable(t.getName())));
        } else { // FunctionApplication
            // compute the interpretations of the arguments of t ...
            // System.err.println("interpretTerm " + t);
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            final FunctionSymbol rootSymbol = fApp.getRootSymbol();
            final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            if (this.predefinedMap.isUndefinedInt(rootSymbol)) {
                return this.interpretAsArbitraryConstant(args.get(0));
            }
            if (args.isEmpty()) { // fApp is a constant
                // can not be div, mod, ...
                if (this.predefinedMap.isInt(rootSymbol, DomainFactory.INTEGERS)) {
                    if (!this.pol.containsKey(rootSymbol)) {
                        this.pol.put(rootSymbol, this.getPolynomialFromFunction(rootSymbol, null, aborter));
                    }
                }
                if (Globals.useAssertions) {
                    assert (this.pol.containsKey(rootSymbol)) : "Must extend fs >" + rootSymbol.getName() + "< first";
                }
                return this.pol.get(rootSymbol);
            }
            // ... then get the interpretation of the root symbol
            if (!this.isContextFunction(rootSymbol)) {
                // nothing context sensitive
                result = this.pol.get(rootSymbol);
            } else {
                // its a div, mod, ... or something renamed / contextSensitive
                result = this.getContextPolyFromFunction(kPathToRoot, rootSymbol, args, null);
            }

            assert (result != null) : t;
            final ImmutableSet<GPolyVar> occuringVars = result.getVariables();
            Map<GPolyVar, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> substitution;
            // x_j |-> poly interpretation of t|_j

            final int size = args.size();
            substitution = new LinkedHashMap<GPolyVar, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>(size);
            final ArrayList<OrderPoly<BigIntImmutable>> argPolys = new ArrayList<OrderPoly<BigIntImmutable>>(size);
            for (int i = 0; i < size; ++i) {
                aborter.checkAbortion();
                final GPolyVar argVar = this.getVariableForFunctionSymbolArgument(i);
                if (!occuringVars.contains(argVar)) {
                    continue;
                }
                pathToRoot.push(new ImmutablePair<FunctionSymbol, Integer>(rootSymbol, i));
                final OrderPoly<BigIntImmutable> argPoly = this.interpretTerm(kPathToRoot, args.get(i), aborter);
                argPolys.add(argPoly);
                substitution.put(argVar, argPoly.unwrap());
                pathToRoot.pop();
            }

            // and plug the arg polys into the root poly
            result = this.factory.substituteVariables(result, substitution, this.polyRing, aborter);
        }
        // System.out.println("InterpretTerm: [" + t + "] = " + factory.wrap(result).exportFlatDeep(fvInner, fvOuter, new PLAIN_Util()));
        // System.out.println("InterpretTerm: [" + t + "] = " + result);
        return result;

    }

    /**
     * ignores predefined div & mod
     */
    @Override
    public void extend(final FunctionSymbol symbol,
        final GInterpretationMode<BigIntImmutable> form,
        final Abortion aborter) throws AbortionException {
        // System.err.println("EXTEND: " + symbol);
        if (!this.isContextFunction(symbol)) {
            super.extend(symbol, form, aborter);
        }
    }

    @Override
    @Deprecated
    public GInterpretation<BigIntImmutable> specialize(final Map<GPolyVar, BigIntImmutable> state,
        final BigIntImmutable defValue,
        final Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException("Use different verrsion of specialize");
    }

    public IDPGInterpretation specialize(final Map<GPolyVar, BigIntImmutable> state,
        final Map<OPCLogVar<BigIntImmutable>, Boolean> logState,
        final BigIntImmutable defValue,
        final Abortion aborter) throws AbortionException {
        synchronized (this) {
            this.extendedAfs = null;
            final IDPGInterpretation specialization =
                new IDPGInterpretation(this.isNat, this.isTupleNat, this.ruleAnalysis, this.maxHeuristic,
                    this.factory.getFactory(), this.factory.getInnerFactory(), this.constraintFactory, this.fvInner,
                    this.fvOuter, this.coeffOrder, this.citations, this.coeffRange, this.maxPredefCoeffValue, aborter);
            this.applySpecialization(specialization, state, logState, defValue, aborter);
            return specialization;
        }
    }

    protected void applySpecialization(final GInterpretation<BigIntImmutable> spec,
        final Map<GPolyVar, BigIntImmutable> state,
        final Map<OPCLogVar<BigIntImmutable>, Boolean> logState,
        final BigIntImmutable defValue,
        final Abortion aborter) throws AbortionException {
        final IDPGInterpretation specialization = (IDPGInterpretation) spec;
        // boolConstants
        for (final Map.Entry<ConstantType, Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>> entry : this.boolConstants.entrySet()) {
            aborter.checkAbortion();
            final Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constMap =
                new LinkedHashMap<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>();
            for (final Map.Entry<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constEntry : entry.getValue().entrySet()) {
                final BigIntImmutable value = state.get(constEntry.getValue().x);
                if (Globals.useAssertions) {
                    assert (constEntry.getValue().y == null || value == null || value.equals(constEntry.getValue().y)) : "invalid specialization: "
                        + constEntry.getValue().x + " " + constEntry.getValue().y + " -> " + value;
                }
                if (value != null) {
                    constMap.put(constEntry.getKey(),
                        new Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>(
                            constEntry.getValue().x, value, this.factory.getInnerFactory().buildFromCoeff(value)));
                } else {
                    constMap.put(constEntry.getKey(),
                        new Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>(
                            constEntry.getValue().x, constEntry.getValue().y, constEntry.getValue().z));
                }
            }
            specialization.boolConstants.put(entry.getKey(), constMap);
        }
        for (final Map.Entry<ConstantType, Map<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>> entry : this.boolTermConstants.entrySet()) {
            aborter.checkAbortion();
            final Map<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constMap =
                new LinkedHashMap<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>>();
            for (final Map.Entry<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constEntry : entry.getValue().entrySet()) {
                final BigIntImmutable value = state.get(constEntry.getValue().x);
                if (Globals.useAssertions) {
                    assert (constEntry.getValue().y == null || value == null || value.equals(constEntry.getValue().y)) : "invalid specialization: "
                        + constEntry.getValue().x + " " + constEntry.getValue().y + " -> " + value;
                }
                if (value != null) {
                    constMap.put(constEntry.getKey(),
                        new Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>(
                            constEntry.getValue().x, value, this.factory.getInnerFactory().buildFromCoeff(value)));
                } else {
                    constMap.put(constEntry.getKey(),
                        new Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>(
                            constEntry.getValue().x, constEntry.getValue().y, constEntry.getValue().z));
                }
            }
            specialization.boolTermConstants.put(entry.getKey(), constMap);
        }

        for (final Map.Entry<GeneralizedRule, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>> entry : this.ruleLogVars.entrySet()) {
            aborter.checkAbortion();
            final Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constMap =
                new LinkedHashMap<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>();
            for (final Map.Entry<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constEntry : entry.getValue().entrySet()) {
                final Boolean value = logState.get(constEntry.getValue().x);
                if (Globals.useAssertions) {
                    assert (constEntry.getValue().y == null || value == null || value.equals(constEntry.getValue().y)) : "invalid specialization: "
                        + constEntry.getValue().x + " " + constEntry.getValue().y + " -> " + value;
                }
                if (value != null) {
                    final OrderPolyConstraint<BigIntImmutable> v =
                        value ? this.constraintFactory.createTrue() : this.constraintFactory.createFalse();
                    constMap.put(constEntry.getKey(),
                        new Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>(
                            constEntry.getValue().x, value, v));
                } else {
                    constMap.put(constEntry.getKey(),
                        new Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>(
                            constEntry.getValue().x, constEntry.getValue().y, constEntry.getValue().z));
                }
            }
            specialization.ruleLogVars.put(entry.getKey(), constMap);
        }

        for (final Map.Entry<TRSTerm, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>> entry : this.termLogVars.entrySet()) {
            aborter.checkAbortion();
            final Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constMap =
                new LinkedHashMap<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>();
            for (final Map.Entry<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constEntry : entry.getValue().entrySet()) {
                final Boolean value = logState.get(constEntry.getValue().x);
                if (Globals.useAssertions) {
                    assert (constEntry.getValue().y == null || value == null || value.equals(constEntry.getValue().y)) : "invalid specialization: "
                        + constEntry.getValue().x + " " + constEntry.getValue().y + " -> " + value;
                }
                if (value != null) {
                    final OrderPolyConstraint<BigIntImmutable> v =
                        value ? this.constraintFactory.createTrue() : this.constraintFactory.createFalse();
                    constMap.put(constEntry.getKey(),
                        new Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>(
                            constEntry.getValue().x, value, v));
                } else {
                    constMap.put(constEntry.getKey(),
                        new Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>(
                            constEntry.getValue().x, constEntry.getValue().y, constEntry.getValue().z));
                }
            }
            specialization.termLogVars.put(entry.getKey(), constMap);
        }

        // contextSwitchConstants
        for (final Map.Entry<List<ImmutablePair<FunctionSymbol, Integer>>, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> entry : this.contextBoolSwitchCache.entrySet()) {
            aborter.checkAbortion();
            BigIntImmutable value = state.get(entry.getValue().x);
            if (Globals.useAssertions) {
                assert (value != null);
            }
            if (value == null) {
                value = BigIntImmutable.ZERO;
                assert (false);
            }
            specialization.contextBoolSwitchCache.put(entry.getKey(),
                new Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>(entry.getValue().x, value,
                    this.factory.getInnerFactory().buildFromCoeff(value)));
        }

        specialization.v_f_i.putAll(this.v_f_i);
        specialization.v_f_i_Encodings.putAll(this.v_f_i_Encodings);
        specialization.usableRulesConstraints.addAll(this.usableRulesConstraints);
        specialization.contextUsableRulesConstraints.addAll(this.contextUsableRulesConstraints);

        // copy and specialize all context pol
        for (final Entry<FunctionSymbol, Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>> symbolEntry : this.contextPol.entrySet()) {
            aborter.checkAbortion();
            final Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>> newSymbolMap =
                new LinkedHashMap<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>();
            specialization.contextPol.put(symbolEntry.getKey(), newSymbolMap);
            for (final Entry<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>> pathEntry : symbolEntry.getValue().entrySet()) {
                final Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>> newPathMap =
                    new LinkedHashMap<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>();
                newSymbolMap.put(pathEntry.getKey(), newPathMap);
                for (final Entry<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>> argsEntry : pathEntry.getValue().entrySet()) {
                    OrderPoly<BigIntImmutable> polynomial = argsEntry.getValue();
                    // replace according to state
                    final Map<GPolyVar, BigIntImmutable> newState = new LinkedHashMap<GPolyVar, BigIntImmutable>(state);
                    // replace every other variable by defValue
                    for (final GPolyVar var : polynomial.getInnerVariables()) {
                        if (!newState.containsKey(var)) {
                            if (Globals.useAssertions) {
                                assert (false);
                            }
                            newState.put(var, defValue);
                        }
                    }
                    polynomial = this.deepSubstitute(polynomial, newState, aborter);
                    newPathMap.put(argsEntry.getKey(), polynomial);
                }
            }
        }

        // fill context sensitive replacement map
        final FreshNameGenerator freshName = new FreshNameGenerator(this.pol.keySet(), FreshNameGenerator.VARIABLES);
        for (final Entry<FunctionSymbol, Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>> symbolEntry : this.contextPol.entrySet()) {
            aborter.checkAbortion();
            final Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, FunctionSymbol> newFuncMap =
                new LinkedHashMap<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, FunctionSymbol>();
            final Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>> newContextFuncMap =
                new LinkedHashMap<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>();
            specialization.contextPol.put(symbolEntry.getKey(), newContextFuncMap);
            final FunctionSymbol[] newSymbols =
                new FunctionSymbol[] {
                    FunctionSymbol.create(
                        freshName.getFreshName(symbolEntry.getKey().getName() + IDPGInterpretation.contextExtensions[0], true),
                        symbolEntry.getKey().getArity()),
                    FunctionSymbol.create(
                        freshName.getFreshName(symbolEntry.getKey().getName() + IDPGInterpretation.contextExtensions[1], true),
                        symbolEntry.getKey().getArity()) };
            for (final Entry<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>> pathEntry : symbolEntry.getValue().entrySet()) {
                // create new symbol
                BigIntImmutable contextDecision;
                if (!pathEntry.getKey().y.isEmpty()) {
                    contextDecision = specialization.contextBoolSwitchCache.get(pathEntry.getKey().y).y;
                } else {
                    switch (pathEntry.getKey().x) {
                    case Decreasing:
                        contextDecision = BigIntImmutable.ZERO;
                        break;
                    case Independent:
                        contextDecision = BigIntImmutable.ZERO;
                        break;
                    case Increasing:
                        contextDecision = BigIntImmutable.ONE;
                        break;
                    default:
                        if (Globals.useAssertions) {
                            assert (false);
                        }
                        contextDecision = BigIntImmutable.ONE;
                    }
                }
                final FunctionSymbol newSymbol = newSymbols[contextDecision.getBigInt().intValue()];
                newFuncMap.put(pathEntry.getKey(), newSymbol);
                // System.err.println("contextSensitiveReplacements " + symbolEntry.getKey() + " " + pathEntry.getKey());
                // fill context pol
                final Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>> newContextPathMap =
                    new LinkedHashMap<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>();
                newContextFuncMap.put(pathEntry.getKey(), newContextPathMap);
                for (final Entry<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>> argsEntry : pathEntry.getValue().entrySet()) {
                    newContextPathMap.put(argsEntry.getKey(), this.getContextPolyFromFunction(pathEntry.getKey(),
                        symbolEntry.getKey(), (ImmutableList<? extends TRSTerm>) argsEntry.getKey(),
                        contextDecision.getBigInt()));
                }
            }
            // System.err.println("Replacement " + symbolEntry.getKey() + " " + newFuncMap);
            specialization.contextSensitiveReplacements.put(symbolEntry.getKey(), newFuncMap);
        }

        super.applySpecialization(specialization, state, defValue, aborter);
    }

    @Override
    @Deprecated
    protected void applySpecialization(final GInterpretation<BigIntImmutable> specialization,
        final Map<GPolyVar, BigIntImmutable> state,
        final BigIntImmutable defValue,
        final Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException("Use different verrsion of applySpecialization");
    }

    /**
     * computes the extended AFS corresponding to this interpretation.
     * Requires that this is a concrete interpretation (without unchosen coefficients)
     * @return
     */
    public IExtendedAfs getExtendedAfs() {
        if (this.extendedAfs == null) {
            synchronized (this) {
                if (this.extendedAfs == null) {
                    final Map<FunctionSymbol, List<IDependence>> afs =
                        new LinkedHashMap<FunctionSymbol, List<IDependence>>();
                    final Pair<Semiring<GPoly<BigIntImmutable, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> outerRingMonoid =
                        this.getOuterRingMonoid();
                    final Pair<Semiring<BigIntImmutable>, CMonoid<GMonomial<GPolyVar>>> innerRingMonoid =
                        this.getInnerRingMonoid();
                    final MaxMinToVarVisitor<BigIntImmutable> maxMinToVarVisitor =
                        new MaxMinToVarVisitor<BigIntImmutable>(this.fvInner, this.fvOuter, this.factory.getFactory());
                    for (final Map.Entry<FunctionSymbol, OrderPoly<BigIntImmutable>> entry : this.pol.entrySet()) {
                        final FunctionSymbol f = entry.getKey();
                        GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> poly = entry.getValue().unwrap();
                        poly = maxMinToVarVisitor.applyTo(poly);
                        if (!poly.isFlat(outerRingMonoid)) {
                            poly = this.fvOuter.applyTo(poly);
                        }
                        final int arity = f.getArity();
                        final List<IDependence> depedences = new ArrayList<IDependence>(arity);
                        for (int position = 0; position < arity; position++) {
                            final GPolyVar var = this.getVariableForFunctionSymbolArgument(position);
                            final ImmutableList<GPoly<BigIntImmutable, GPolyVar>> coeffs =
                                poly.getCoeffsFromMap(var, outerRingMonoid);
                            IDependence dependence = IDependence.None;
                            coeffFor: for (GPoly<BigIntImmutable, GPolyVar> coeff : coeffs) {
                                if (!coeff.isFlat(innerRingMonoid)) {
                                    coeff = this.fvInner.applyTo(coeff);
                                }
                                assert (coeff.isConstant());
                                switch (coeff.getConstantPart(innerRingMonoid).getBigInt().signum()) {
                                case 0:
                                    break;
                                case 1:
                                    if (dependence == IDependence.None) {
                                        dependence = IDependence.Incr;
                                    } else if (dependence == IDependence.Decr) {
                                        dependence = IDependence.Wild;
                                        break coeffFor;
                                    }
                                    break;
                                case -1:
                                    if (dependence == IDependence.None) {
                                        dependence = IDependence.Decr;
                                    } else if (dependence == IDependence.Incr) {
                                        dependence = IDependence.Wild;
                                        break coeffFor;
                                    }
                                    break;
                                }
                            }
                            depedences.add(dependence);
                        }
                        afs.put(f, depedences);
                    }

                    this.extendedAfs = new IExtendedAfs() {
                        @Override
                        public IDependence filterPosition(final FunctionSymbol f, final int i) {
                            final PredefinedFunction func =
                                IDPGInterpretation.this.predefinedMap.getPredefinedFunction(f);
                            if (func != null) {
                                if (func.isRelation() || func.isBoolean()) {
                                    return IDependence.None;
                                } else {
                                    return func.filterPositon(i);
                                }
                            } else {
                                return afs.get(f).get(i);
                            }
                        }
                    };
                }
            }
        }
        return this.extendedAfs;
    }

    public FunctionSymbol getContextReplacementSymbol(final FunctionSymbol fs,
        final Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>> pathToRoot) {
        final Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, FunctionSymbol> fsMap =
            this.contextSensitiveReplacements.get(fs);
        if (fsMap != null) {
            final FunctionSymbol newFs = fsMap.get(pathToRoot);
            /*
            if (Globals.useAssertions) {
                assert(newFs != null) : fs + " @ " + pathToRoot;
            } */
            return newFs;
        } else {
            return null;
        }
    }

    @Override
    public OrderPoly<BigIntImmutable> getPolynomialFromFunction(final FunctionSymbol symbol,
        final GInterpretationMode<BigIntImmutable> form,
        final Abortion aborter) throws AbortionException {
        final PredefinedSemantics sem = this.predefinedMap.getPredefinedSemantics(symbol);
        if (sem != null) {
            if (this.isNat) {
                return this.factory.wrap(this.factory.getFactory().zero());
            } else {
                if (sem.isConstructor()) {
                    if (this.predefinedMap.isInt(symbol, DomainFactory.INTEGERS)) {
                        return this.getPolyInt(symbol);
                    } else if (this.predefinedMap.isBooleanTrue(symbol)) {
                        return this.getPolyTrue(symbol, form, aborter);
                    } else if (this.predefinedMap.isBooleanFalse(symbol)) {
                        return this.getPolyFalse(symbol, form, aborter);
                    }
                } else {
                    final PredefinedFunction func = (PredefinedFunction) sem;
                    switch (func.getFunc()) {
                    case Add:
                        return this.getPolyAdd(symbol);
                    case Sub:
                        return this.getPolySub(symbol);
                    case UnaryMinus:
                        return this.getPolyUnaryMinus(symbol);
                    case Mul:
                        return this.getPolyMul(symbol);
                    case Ge:
                        return this.getPolyGe(symbol);
                    case Gt:
                        return this.getPolyGt(symbol);
                    case Le:
                        return this.getPolyLe(symbol);
                    case Lt:
                        return this.getPolyLt(symbol);
                    case Eq:
                        return this.getPolyEq(symbol);
                    case Neq:
                        return this.getPolyNeq(symbol);
                    case Land:
                        return this.getPolyLand(symbol);
                    case Lor:
                        return this.getPolyLor(symbol);
                    case Lnot:
                        return this.getPolyLnot(symbol);
                    }
                }
            }
            throw new IllegalArgumentException("can not interpret predefined function " + symbol);
        } else {
            return this.getPolynomialFromUserDefinedFunction(symbol, form, aborter);
        }
    }

    public OrderPoly<BigIntImmutable> getPolynomialFromUserDefinedFunction(final FunctionSymbol symbol,
        final GInterpretationMode<BigIntImmutable> form,
        final Abortion aborter) throws AbortionException {
        final Triple<OrderPoly<BigIntImmutable>, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>, Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>> shape =
            this.maxHeuristic.getShape(this, symbol, aborter);
        OrderPoly<BigIntImmutable> res;
        if (shape == null) {
            res = super.getPolynomialFromFunction(symbol, form, aborter);
        } else {
            this.v_f_i.put(symbol, shape.z);
            this.v_f_i_Encodings.put(symbol, shape.y);
            res = shape.x;
        }
        if (Globals.useAssertions) {
            if (this.isTupleNat || (this.isNat && !this.tupleSymbols.contains(symbol))) {
                if (!res.isFlat(this.getOuterRingMonoid())) {
                    this.fvOuter.applyTo(res);
                }
                for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> entry : res.getMonomials(
                    this.getOuterRingMonoid()).entrySet()) {
                    aborter.checkAbortion();
                    final GPoly<BigIntImmutable, GPolyVar> inner = entry.getValue();
                    if (!inner.isFlat(this.getInnerRingMonoid())) {
                        this.fvInner.applyTo(inner);
                    }
                    for (final Map.Entry<GMonomial<GPolyVar>, BigIntImmutable> innerEntry : inner.getMonomials(
                        this.getInnerRingMonoid()).entrySet()) {
                        assert innerEntry.getValue().getBigInt().signum() >= 0 : "Coefficients must be nat for "
                            + symbol + "!";
                    }
                }
            }
        }
        return res;
    }

    private OrderPoly<BigIntImmutable> getPolyInt(final FunctionSymbol symbol) {
        return this.factory.buildFromCoeff(this.factory.getInnerFactory().buildFromCoeff(
            BigIntImmutable.create(this.predefinedMap.getInt(symbol, DomainFactory.INTEGERS))));
    }

    private OrderPoly<BigIntImmutable> getPolyAdd(final FunctionSymbol symbol) {
        return this.factory.plus(this.factory.buildFromVariable(this.getVariableForFunctionSymbolArgument(0)),
            this.factory.buildFromVariable(this.getVariableForFunctionSymbolArgument(1)));
    }

    private OrderPoly<BigIntImmutable> getPolySub(final FunctionSymbol symbol) {
        // x_1 - x_2
        return this.factory.minus(this.factory.buildFromVariable(this.getVariableForFunctionSymbolArgument(0)),
            this.factory.buildFromVariable(this.getVariableForFunctionSymbolArgument(1)));
    }

    private OrderPoly<BigIntImmutable> getPolyUnaryMinus(final FunctionSymbol symbol) {
        // 0 - x_1
        return this.factory.minus(this.factory.wrap(this.factory.getFactory().zero()),
            this.factory.buildFromVariable(this.getVariableForFunctionSymbolArgument(0)));
    }

    private OrderPoly<BigIntImmutable> getPolyMul(final FunctionSymbol symbol) {
        return this.factory.times(this.factory.buildFromVariable(this.getVariableForFunctionSymbolArgument(0)),
            this.factory.buildFromVariable(this.getVariableForFunctionSymbolArgument(1)));
    }

    private OrderPoly<BigIntImmutable> getContextPolyFromFunction(Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>> kPathToRoot,
        final FunctionSymbol fs,
        final ImmutableList<? extends TRSTerm> args,
        final BigInteger contextDecision) {
        if (this.isNat) {
            if (this.predefinedMap.isDiv(fs)) {
                return this.factory.wrap(this.factory.getFactory().zero());
            } else if (this.predefinedMap.isMod(fs)) {
                return this.factory.wrap(this.factory.getFactory().zero());
            } else {
                throw new IllegalArgumentException("can not interpret function " + fs);
            }
        }
        Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>> pathMap =
            null;
        Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>> argsMap = null;
        // we get a mutable stack as input, so copy if necessary
        if (contextDecision == null) {
            pathMap = this.contextPol.get(fs);
            // check cache
            if (pathMap == null) {
                pathMap =
                    new LinkedHashMap<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>();
                this.contextPol.put(fs, pathMap);
            } else {
                argsMap = pathMap.get(kPathToRoot);
            }
            if (argsMap == null) {
                argsMap = new LinkedHashMap<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>();
                kPathToRoot = this.duplicatePathToRoot(kPathToRoot);
                pathMap.put(kPathToRoot, argsMap);
            }
        }
        OrderPoly<BigIntImmutable> result;
        if (this.predefinedMap.isDiv(fs)) {
            result = this.getPolyDiv(argsMap, kPathToRoot, fs, args, contextDecision);
        } else if (this.predefinedMap.isMod(fs)) {
            result = this.getPolyMod(argsMap, kPathToRoot, fs, args, contextDecision);
        } else {
            throw new IllegalArgumentException("can not interpret function " + fs);
        }
        return result;
    }

    private OrderPoly<BigIntImmutable> getPolyDiv(final Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>> argsMap,
        final Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>> pathToRoot,
        final FunctionSymbol rootSymbol,
        final ImmutableList<? extends TRSTerm> args,
        final BigInteger contextDecision) {
        List<TRSTerm> newArgs = null;
        OrderPoly<BigIntImmutable> result;
        if (contextDecision == null) {
            newArgs = new LinkedList<TRSTerm>(args);
            newArgs.set(0, null);
            result = argsMap.get(newArgs);
            if (result != null) {
                return result;
            }
        }
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fac = this.factory.getFactory();
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFac = this.factory.getInnerFactory();
        final GPolyVar x1 = this.getVariableForFunctionSymbolArgument(0);
        final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> x1Poly = fac.buildFromVariable(x1);
        final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> x1NegPoly =
            fac.concat(innerFac.buildFromCoeff(BigIntImmutable.MINUS_ONE), fac.buildVariable(x1));
        final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> absX1 = fac.max(x1Poly, x1NegPoly);

        // get offset
        final TRSTerm divisor = args.get(1);
        boolean foundOffset = false;
        GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> offsetPoly = null;
        if (!divisor.isVariable()) {
            final FunctionSymbol divisorFs = ((TRSFunctionApplication) divisor).getRootSymbol();
            if (this.predefinedMap.isInt(divisorFs, DomainFactory.INTEGERS)) {
                final BigInteger d = this.predefinedMap.getInt(divisorFs, DomainFactory.INTEGERS);
                if (d.abs().compareTo(BigInteger.ONE) > 0) {
                    offsetPoly = fac.one();
                }
                foundOffset = true;
            }
        }
        if (!foundOffset) {
            final GPolyVar x2 = this.getVariableForFunctionSymbolArgument(1);
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> x2Poly = fac.buildFromVariable(x2);
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> x2NegPoly =
                fac.concat(innerFac.buildFromCoeff(BigIntImmutable.MINUS_ONE), fac.buildVariable(x2));
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> absX2 = fac.max(x2Poly, x2NegPoly);
            // offsetPoly = min(absX2 - 1, absX1)
            offsetPoly = fac.min(fac.minus(absX2, fac.one()), absX1);
        }

        GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> coeffPoly;
        if (contextDecision == null) {
            final GPoly<BigIntImmutable, GPolyVar> aCoeff = this.getContextPolySwitchCoeff(pathToRoot);
            // coeffPoly = 2a -1
            coeffPoly =
                fac.buildFromCoeff(innerFac.minus(
                    innerFac.times(innerFac.buildFromCoeff(BigIntImmutable.create(BigInteger.valueOf(2))), aCoeff),
                    innerFac.one()));
        } else if (contextDecision.intValue() == 0) {
            // coeffPoly = 2 * 0 - 1 = -1
            coeffPoly = fac.buildFromCoeff(innerFac.buildFromCoeff(BigIntImmutable.create(BigInteger.valueOf(-1))));
        } else {
            // coeffPoly = 2 * 1 - 1 = 1 -> nothing
            coeffPoly = null;
        }

        // coeffPoly * (max(x1, -x1) - offsetPoly)
        // a decides for over and under approximation

        GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> tmp = absX1;
        if (offsetPoly != null) {
            tmp = fac.minus(tmp, offsetPoly);
        }
        if (coeffPoly != null) {
            tmp = fac.times(coeffPoly, tmp);
        }

        result = this.factory.wrap(tmp);
        if (contextDecision == null) {
            argsMap.put(ImmutableCreator.create(newArgs), result);
        }
        return result;
    }

    private OrderPoly<BigIntImmutable> getPolyMod(final Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>> argsMap,
        final Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>> pathToRoot,
        final FunctionSymbol rootSymbol,
        final ImmutableList<? extends TRSTerm> args,
        final BigInteger contextDecision) {
        List<TRSTerm> newArgs = null;
        OrderPoly<BigIntImmutable> result;
        if (contextDecision == null) {
            newArgs = new LinkedList<TRSTerm>(args);
            newArgs.set(0, null);
            result = argsMap.get(newArgs);
            if (result != null) {
                return result;
            }
        }
        // (2a -1) * max(x2, -x2)
        // a decides for over and under approximation
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fac = this.factory.getFactory();
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFac = this.factory.getInnerFactory();
        final GPolyVar x2 = this.getVariableForFunctionSymbolArgument(1);
        final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> x2Poly = fac.buildFromVariable(x2);
        final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> x2NegPoly =
            fac.concat(innerFac.buildFromCoeff(BigIntImmutable.MINUS_ONE), fac.buildVariable(x2));
        if (contextDecision == null) {
            final GPoly<BigIntImmutable, GPolyVar> aCoeff = this.getContextPolySwitchCoeff(pathToRoot);
            result =
                this.factory.wrap(
                // (2a - 1) * max(x2, -x2)
                fac.times(fac.buildFromCoeff(innerFac.minus(
                    innerFac.times(innerFac.buildFromCoeff(BigIntImmutable.create(BigInteger.valueOf(2))), aCoeff),
                    innerFac.one())), fac.max(x2Poly, x2NegPoly)));
        } else {
            switch (contextDecision.intValue()) {
            case 0:
                result = this.factory.wrap(
                // (2 * 0 - 1) * max(x2, -x2) = - max(x2, -x2) = min (x2, -x2);
                fac.min(x2Poly, x2NegPoly));
                break;
            case 1:
                result = this.factory.wrap(
                // (2 * 1 - 1) *  max(x2, -x2)
                fac.max(x2Poly, x2NegPoly));
                break;
            default:
                throw new IllegalArgumentException("we can only decide for 0 or 1, not " + contextDecision.intValue());
            }
        }
        if (contextDecision == null) {
            argsMap.put(ImmutableCreator.create(newArgs), result);
        }
        return result;
    }

    /**
     * Creates a boolean coeff that is 1 if function is used at incr. and 0 when used at decr positions or free for filtered
     * @param pathToRoot
     * @return
     */
    protected GPoly<BigIntImmutable, GPolyVar> getContextPolySwitchCoeff(final Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>> kPathToRoot) {
        Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> res =
            this.contextBoolSwitchCache.get(kPathToRoot.y);
        if (res != null) {
            switch (kPathToRoot.x) {
            case Decreasing:
                return this.factory.getInnerFactory().minus(this.factory.getInnerFactory().one(), res.z);
            case Independent:
                return this.factory.getInnerFactory().zero();
            case Increasing:
                return res.z;
            default:
                if (Globals.useAssertions) {
                    assert (false) : "no wild for context sensitive polys";
                }
            }
        }
        if (Globals.useAssertions) {
            assert (kPathToRoot.x != RelDependency.Wild);
        }
        if (kPathToRoot.y.isEmpty()) {
            // WARNING: change applySpecialization() accordingly!
            switch (kPathToRoot.x) {
            case Decreasing:
                return this.factory.getInnerFactory().zero();
            case Independent:
                return this.factory.getInnerFactory().zero();
            case Increasing:
                return this.factory.getInnerFactory().one();
            default:
                if (Globals.useAssertions) {
                    assert (false);
                }
            }
        }
        // System.err.println("CONTEXT SWITCH: " + pathToRoot);
        final GPolyVar a = this.getNextCoeff(IDPGInterpretation.ContextSwitchPrefix, this.boolRange);
        IActiveCondition condition;
        if (kPathToRoot.y.isEmpty()) {
            condition =
                IActiveCondition.create(ImmutableCreator.create(Collections.<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>>emptySet()));
            ;
        } else {
            condition =
                IActiveCondition.create(ImmutableCreator.create(Collections.singleton(ImmutableCreator.create(new LinkedHashSet<ImmutablePair<FunctionSymbol, Integer>>(
                    kPathToRoot.y)))));
        }

        final ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> activeConstraints =
            this.getIActiveConstraints(condition, true);
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFac = this.factory.getInnerFactory();
        final OrderPolyConstraint<BigIntImmutable> constraint =
            this.constraintFactory.createAnd(
            // incr => a = 1
                this.constraintFactory.createOr(this.constraintFactory.createOr(
                    this.constraintFactory.createNot(activeConstraints.x), activeConstraints.y),
                    this.constraintFactory.createWithQuantifier(
                        this.factory.buildFromCoeff(innerFac.buildFromVariable(a)),
                        this.factory.buildFromCoeff(innerFac.one()), ConstraintType.EQ)),
                // decr => a = 0
                this.constraintFactory.createOr(this.constraintFactory.createOr(
                    this.constraintFactory.createNot(activeConstraints.y), activeConstraints.x),
                    this.constraintFactory.createWithQuantifier(this.factory.buildFromInnerVariable(a),
                        ConstraintType.EQ)));
        this.contextUsableRulesConstraints.add(constraint);
        this.contextUsableRulesConstraints.add(this.constraintFactory.createOr(activeConstraints.x, activeConstraints.y));
        res =
            new Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>(a, null,
                this.factory.getInnerFactory().buildFromVariable(a));
        this.contextBoolSwitchCache.put(this.duplicatePathToRoot(kPathToRoot).y, res);
        // System.err.println("contextBoolSwitchCache "  + pathToRoot + " " + activeConstraints + " ==> " + constraint);
        switch (kPathToRoot.x) {
        case Decreasing:
            return this.factory.getInnerFactory().minus(this.factory.getInnerFactory().one(), res.z);
        case Independent:
            return this.factory.getInnerFactory().zero();
        case Increasing:
            return res.z;
        default:
            if (Globals.useAssertions) {
                assert (false);
            }
        }
        return res.z;
    }

    private OrderPoly<BigIntImmutable> getPolyGe(final FunctionSymbol symbol) {
        return this.getNextCoeffOrderPoly(symbol);
    }

    private OrderPoly<BigIntImmutable> getPolyGt(final FunctionSymbol symbol) {
        return this.getNextCoeffOrderPoly(symbol);
    }

    private OrderPoly<BigIntImmutable> getPolyEq(final FunctionSymbol symbol) {
        return this.getNextCoeffOrderPoly(symbol);
    }

    private OrderPoly<BigIntImmutable> getPolyNeq(final FunctionSymbol symbol) {
        return this.getNextCoeffOrderPoly(symbol);
    }

    private OrderPoly<BigIntImmutable> getPolyLe(final FunctionSymbol symbol) {
        return this.getNextCoeffOrderPoly(symbol);
    }

    private OrderPoly<BigIntImmutable> getPolyLt(final FunctionSymbol symbol) {
        return this.getNextCoeffOrderPoly(symbol);
    }

    private OrderPoly<BigIntImmutable> getPolyLand(final FunctionSymbol symbol) {
        return this.getNextCoeffOrderPoly(symbol);
    }

    private OrderPoly<BigIntImmutable> getPolyLnot(final FunctionSymbol symbol) {
        return this.getNextCoeffOrderPoly(symbol);
    }

    private OrderPoly<BigIntImmutable> getPolyLor(final FunctionSymbol symbol) {
        return this.getNextCoeffOrderPoly(symbol);
    }

    private OrderPoly<BigIntImmutable> getPolyTrue(final FunctionSymbol symbol,
        final GInterpretationMode<BigIntImmutable> form,
        final Abortion aborter) throws AbortionException {
        return super.getPolynomialFromFunction(symbol, form, aborter);
    }

    private OrderPoly<BigIntImmutable> getPolyFalse(final FunctionSymbol symbol,
        final GInterpretationMode<BigIntImmutable> form,
        final Abortion aborter) throws AbortionException {
        return super.getPolynomialFromFunction(symbol, form, aborter);
    }

    // shift coeffs so that lower bound of range is zero

    /**
     * @return a new inner GPoly representing a fresh coeff.
     */
    @Override
    protected GPoly<BigIntImmutable, GPolyVar> getNextCoeffPoly(final FunctionSymbol fs) {
        final GPolyVar coeff = this.getNextCoeff(this.normedCoeffRange);
        final GPolyFactory<BigIntImmutable, GPolyVar> fact = this.factory.getInnerFactory();
        if (this.isTupleNat || (this.isNat && !this.tupleSymbols.contains(fs))) {
            return fact.plus(fact.buildFromVariable(coeff), this.natRangeShiftPoly);
        } else {
            return fact.plus(fact.buildFromVariable(coeff), this.rangeShiftPoly);
        }
    }

    public BigIntImmutable getMaxPredefCoeffValue() {
        return this.maxPredefCoeffValue;
    }

    public BigIntImmutable getMaxPredefCoeffValueMinusOne() {
        return this.maxPredefCoeffValueMinusOne;
    }

    public OPCRange<BigIntImmutable> getCoeffRange() {
        return this.coeffRange;
    }

    public BigIntImmutable getRangeShift() {
        return this.rangeShift;
    }

    public GPoly<BigIntImmutable, GPolyVar> getRangeShiftPoly() {
        return this.rangeShiftPoly;
    }

    public OPCRange<BigIntImmutable> getNormedCoeffRange() {
        return this.normedCoeffRange;
    }

    /**
     * The returned constraints may neither contain all quantified variables nor negative numbers
     * @param idpQUsableRules
     * @return
     */
    public Pair<Set<Pair<OrderPolyConstraint<BigIntImmutable>, OrderPoly<BigIntImmutable>>>, OrderPolyConstraint<BigIntImmutable>> getUsableRulesConstraintEquations(final IUsableRulesEstimation usableRules,
        final Abortion aborter) throws AbortionException {
        // System.err.println("usableRulesConstraints " + usableRules);
        final Set<OrderPolyConstraint<BigIntImmutable>> constraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        final Set<Pair<OrderPolyConstraint<BigIntImmutable>, OrderPoly<BigIntImmutable>>> constraintEquations =
            new LinkedHashSet<Pair<OrderPolyConstraint<BigIntImmutable>, OrderPoly<BigIntImmutable>>>();

        for (final Map.Entry<TRSTerm, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>> termEntry : this.termLogVars.entrySet()) {
            final TRSTerm term = termEntry.getKey();
            final Map<ConstantType, Set<OrderPolyConstraint<BigIntImmutable>>> constConstraints =
                new LinkedHashMap<ConstantType, Set<OrderPolyConstraint<BigIntImmutable>>>();
            for (final Map.Entry<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constEntry : termEntry.getValue().entrySet()) {
                if (constEntry.getKey().getIncreasing() != null && constEntry.getKey().getCsar() != null) {
                    constConstraints.put(constEntry.getKey(), new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>());
                }
            }
            if (constConstraints.isEmpty()) {
                continue;
            }

            final IdpQUsableRules activeCond = usableRules.getActiveConditions(term);
            // System.err.println("Active: "+ term);
            for (final Map.Entry<GeneralizedRule, IActiveCondition> ruleEntry : activeCond.getActive().entrySet()) {
                final PredefinedFunction<? extends Domain> func =
                    this.predefinedMap.getPredefinedFunction(ruleEntry.getKey().getLeft().getRootSymbol());
                if (func != null && func.isArithmetic()) {
                    // predefined arithmetic, because we have fixed interpretation
                    if (func.getFunc() != Func.Div && func.getFunc() != Func.Mod) {
                        continue;
                    }
                }
                // System.err.println(ruleEntry.getKey() + " : " + ruleEntry.getValue());
                final ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> active =
                    this.getIActiveConstraints(ruleEntry.getValue(), true);
                if (active.x.equals(this.constraintFactory.createTrue())
                    && active.y.equals(this.constraintFactory.createTrue())) {
                    continue;
                }
                final GeneralizedRule rule = ruleEntry.getKey();
                for (final Map.Entry<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constEntry : termEntry.getValue().entrySet()) {
                    if (constEntry.getKey().getIncreasing() == null || constEntry.getKey().getCsar() == null) {
                        // no usable constant
                        continue;
                    }
                    final ConstantType constType = constEntry.getKey();
                    constConstraints.get(constType).add(
                        this.constraintFactory.createAnd(
                            this.constraintFactory.createOr(active.y, this.getLogVarConstant(
                                this.resolveUsableConstraintType(constType.getIncreasing(), constType.getCsar()), rule)),
                            this.constraintFactory.createOr(active.x,
                                this.getLogVarConstant(
                                    this.resolveUsableConstraintType(!constType.getIncreasing(), constType.getCsar()),
                                    rule))));
                }
            }
            // System.err.println("####");
            for (final Map.Entry<ConstantType, Set<OrderPolyConstraint<BigIntImmutable>>> constEntry : constConstraints.entrySet()) {
                if (!constEntry.getValue().isEmpty()) {
                    constraints.add(this.constraintFactory.createOr(
                        this.constraintFactory.createNot(this.getLogVarConstant(constEntry.getKey(), term)),
                        this.constraintFactory.createAnd(constEntry.getValue())));
                }
            }
        }

        // encode active hierarchy
        final Set<ImmutablePair<FunctionSymbol, Integer>> usedVfis =
            new LinkedHashSet<ImmutablePair<FunctionSymbol, Integer>>();
        constraintFor: for (final Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>> node : this.activeHierarchy.getNodes()) {
            if (node.getObject().y == null) {
                // root...
                continue;
            }
            final Set<ImmutablePair<FunctionSymbol, Integer>> remaining =
                new LinkedHashSet<ImmutablePair<FunctionSymbol, Integer>>(node.getObject().x);
            final Set<ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>> usedPre =
                new LinkedHashSet<ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>();
            for (final Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>> pre : this.activeHierarchy.getIn(node)) {
                if (remaining.removeAll(pre.getObject().x)) {
                    usedPre.add(pre.getObject().y);
                    if (remaining.isEmpty()) {
                        break;
                    }
                }
            }
            ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> andConstraint =
                null;
            for (final ImmutablePair<FunctionSymbol, Integer> fConstraint : remaining) {
                if (this.predefinedMap.isUndefinedInt(fConstraint.x)) {
                    continue constraintFor;
                }
                usedVfis.add(fConstraint);
                if (andConstraint == null) {
                    andConstraint = this.getV_f_i(fConstraint.x, fConstraint.y, true);
                } else {
                    andConstraint = this.iActiveAnd(andConstraint, this.getV_f_i(fConstraint.x, fConstraint.y, false));
                }
            }
            for (final ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>> pre : usedPre) {
                if (andConstraint == null) {
                    andConstraint = pre;
                } else {
                    andConstraint = this.iActiveAnd(andConstraint, pre);
                }
            }
            if (andConstraint != null) {
                constraints.add(this.constraintFactory.createOr(this.constraintFactory.createNot(node.getObject().y.x),
                    andConstraint.x));
                constraints.add(this.constraintFactory.createOr(this.constraintFactory.createNot(node.getObject().y.y),
                    andConstraint.y));
            }
        }

        // encode v_f_i hierarchy
        for (final Map.Entry<FunctionSymbol, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>> fs_vfi : this.v_f_i_Encodings.entrySet()) {
            for (final Map.Entry<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>> i_vfi : fs_vfi.getValue().entrySet()) {
                if (i_vfi.getValue().x
                    || usedVfis.contains(new ImmutablePair<FunctionSymbol, Integer>(fs_vfi.getKey(), i_vfi.getKey()))) {
                    final ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>> vfi =
                        this.v_f_i.get(fs_vfi.getKey()).get(i_vfi.getKey());
                    constraints.add(this.constraintFactory.createOr(this.constraintFactory.createNot(vfi.x),
                        i_vfi.getValue().y.x));
                    constraints.add(this.constraintFactory.createOr(this.constraintFactory.createNot(vfi.y),
                        i_vfi.getValue().y.y));
                }
            }
        }

        for (final Map.Entry<GeneralizedRule, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>> ruleEntry : this.ruleLogVars.entrySet()) {
            // force filtering of relations
            final GeneralizedRule rule = ruleEntry.getKey();
            final FunctionSymbol lhsRoot = rule.getLeft().getRootSymbol();
            final PredefinedFunction func = this.predefinedMap.getPredefinedFunction(lhsRoot);
            ;
            if (func != null && (func.isRelation())) {
                // relation -> filter
                for (final Map.Entry<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constEntry : ruleEntry.getValue().entrySet()) {
                    constraints.add(this.constraintFactory.createNot(constEntry.getValue().z));
                    // System.err.println("*** Force filter: " + constEntry.getValue().x);
                }
            } else if (func != null && func.isArithmetic()) {
                // predefined arithmetic, because we have fixed interpretation
                for (final Map.Entry<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constEntry : ruleEntry.getValue().entrySet()) {
                    if (constEntry.getKey().getIncreasing() != null && constEntry.getKey().getCsar() != null) {
                        if (this.predefinedMap.isDivOrMod(lhsRoot)) {
                            switch (constEntry.getKey().total()) {
                            case Wild:
                                constraints.add(this.constraintFactory.createNot(constEntry.getValue().z));
                                break;
                            case Decreasing:
                                constraints.add(this.constraintFactory.createNot(constEntry.getValue().z));
                                break;
                            default:
                                constraints.add(constEntry.getValue().z);
                                break;
                            }
                        } else {
                            constraints.add(constEntry.getValue().z);
                            // System.err.println("*** Auto OK: " + constEntry.getValue().x);
                        }
                    }
                }
            } else {
                // everything else
                for (final Map.Entry<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constEntry : ruleEntry.getValue().entrySet()) {
                    final ConstantType constType = constEntry.getKey();
                    if (constType.getIncreasing() != null && constType.getCsar() != null) {
                        OrderPoly<BigIntImmutable> usableRule;
                        if (constType.getIncreasing()) {
                            usableRule =
                                this.factory.minus(this.interpretTerm(rule.getLeft(), constType.getCsar(), aborter),
                                    this.interpretTerm(rule.getRight(), constType.getCsar(), aborter));
                        } else {
                            usableRule =
                                this.factory.minus(this.interpretTerm(rule.getRight(), constType.getCsar(), aborter),
                                    this.interpretTerm(rule.getLeft(), constType.getCsar(), aborter));
                        }
                        final GPolyWithMinMaxExport<BigIntImmutable> visitor =
                            new GPolyWithMinMaxExport<BigIntImmutable>(this.fvInner, this.fvOuter,
                                this.factory.getFactory());
                        visitor.applyTo(usableRule);
                        // System.err.println(rule + ":" + constEntry.getValue().x + " @ " + constType + " --->>> " + visitor.export(new PLAIN_Util()));
                        constraintEquations.add(new Pair<OrderPolyConstraint<BigIntImmutable>, OrderPoly<BigIntImmutable>>(
                            this.constraintFactory.createNot(constEntry.getValue().z), usableRule));
                    }
                }
            }
            if (aborter != null) {
                aborter.checkAbortion();
            }
        }

        // System.err.println("contextUsableRulesConstraints " + contextUsableRulesConstraints);
        return new Pair<Set<Pair<OrderPolyConstraint<BigIntImmutable>, OrderPoly<BigIntImmutable>>>, OrderPolyConstraint<BigIntImmutable>>(
            constraintEquations, this.constraintFactory.createAnd(constraints));
    }

    protected ConstantType resolveUsableConstraintType(final boolean increasing, final RelDependency csar) {
        if (increasing) {
            switch (csar) {
            case Decreasing:
                return ConstantType.UsableInc_m1;
            case Independent:
                return ConstantType.UsableInc_0;
            case Increasing:
                return ConstantType.UsableInc_1;
            default:
                return ConstantType.UsableInc_2;
            }
        } else {
            switch (csar) {
            case Decreasing:
                return ConstantType.UsableDec_m1;
            case Independent:
                return ConstantType.UsableDec_0;
            case Increasing:
                return ConstantType.UsableDec_1;
            default:
                return ConstantType.UsableDec_2;
            }
        }
    }

    /**
     * The returned constraints may neither contain all quantified variables nor negative numbers
     * @return
     */
    public OrderPolyConstraint<BigIntImmutable> getUsableRulesConstraints() {

        return this.constraintFactory.createAnd(this.constraintFactory.createAnd(this.usableRulesConstraints),
            this.constraintFactory.createAnd(this.contextUsableRulesConstraints));
    }

    /**
     * <true iff increasing, true iff decreasing>
     * @param condition
     * @return
     */
    public ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> getIActiveConstraints(final IActiveCondition condition,
        final boolean forceEncoding) {
        // check for filtered
        boolean filtered = true;
        final OrderPolyConstraint<BigIntImmutable> TRUE = this.constraintFactory.createTrue();
        for (final ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> conjClause : condition.getSetRepresentation()) {
            boolean clauseFiltered = conjClause.isEmpty();
            for (final ImmutablePair<FunctionSymbol, Integer> atom : conjClause) {
                final ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>> vfi =
                    this.getV_f_i(atom.x, atom.y, forceEncoding);
                if (TRUE.equals(vfi.x) && TRUE.equals(vfi.y)) {
                    clauseFiltered = true;
                    break;
                }
            }
            if (!clauseFiltered) {
                filtered = false;
                break;
            }
        }
        if (filtered) {
            return new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(TRUE,
                TRUE);
        }
        ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> res =
            null;
        for (final ImmutableSet<ImmutablePair<FunctionSymbol, Integer>> cond : condition.getSetRepresentation()) {
            ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>> logVar = this.activeMapping.get(cond);
            if (logVar == null) {
                final OPCLogVar<BigIntImmutable> inc =
                    this.getNextLogVar(ConstantType.ActiveCondition.getPrefix() + "_inc");
                final OPCLogVar<BigIntImmutable> dec =
                    this.getNextLogVar(ConstantType.ActiveCondition.getPrefix() + "_dec");
                logVar = new ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>(inc, dec);
                this.activeMapping.put(cond, logVar);
                // compute parents
                final List<Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>>> parents =
                    new ArrayList<Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>>>();
                parents.add(this.activeRoot);
                int size = parents.size();
                for (int i = 0; i < size; i++) {
                    final Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>> current =
                        parents.get(i);
                    final Set<Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>>> succs =
                        this.activeHierarchy.getOut(current);
                    boolean changed = false;
                    for (final Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>> succ : succs) {
                        if (cond.containsAll(succ.getObject().x)) {
                            changed = true;
                            parents.add(succ);
                            size++;
                        }
                    }
                    if (changed) {
                        parents.remove(i);
                        size--;
                        i--;
                    }
                }
                // insert into hierarchy
                final Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>> newNode =
                    new Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>>(
                        new ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>(
                            cond, logVar));
                this.activeHierarchy.addNode(newNode);
                for (final Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>> parent : parents) {
                    for (final Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>> parentSucc : new ArrayList<Node<ImmutablePair<ImmutableSet<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<OPCLogVar<BigIntImmutable>, OPCLogVar<BigIntImmutable>>>>>(
                        this.activeHierarchy.getOut(parent))) {
                        if (parentSucc.getObject().x.containsAll(cond)) {
                            this.activeHierarchy.removeEdge(parent, parentSucc);
                            this.activeHierarchy.addEdge(newNode, parentSucc);
                        }
                    }
                    this.activeHierarchy.addEdge(parent, newNode);
                }
            }
            if (res == null) {
                res = logVar;
            } else {
                res = this.iActiveOr(res, logVar);
            }
        }
        if (res == null) {
            return new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
                this.constraintFactory.createTrue(), this.constraintFactory.createTrue());
        }
        return res;
    }

    /**
     * Creates a pair of variables that determine if the interpretation for f is
     * increasing / decreasing / ignoring / wild with respect to its i-th argument
     * @param f the function symbol
     * @param i the position
     * @param boolRange the boolean range
     * @return a pair of variables, x : increasing, y : decreasing
     */
    public ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>> getV_f_i(final FunctionSymbol f,
        final int i,
        final boolean forceEncode) {
        // check cache
        Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>> fEntry =
            this.v_f_i.get(f);
        Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>> f_EncEntry =
            this.v_f_i_Encodings.get(f);
        ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>> res = null;
        if (fEntry == null) {
            fEntry =
                new LinkedHashMap<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>();
            this.v_f_i.put(f, fEntry);
            f_EncEntry =
                new LinkedHashMap<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>();
            this.v_f_i_Encodings.put(f, f_EncEntry);
        } else {
            res = fEntry.get(i);
        }

        if (res != null) {
            assert (f_EncEntry.get(i) != null) : f + " / " + i;
            f_EncEntry.get(i).x = true;
            return res;
        }

        {
            final RelDependency d = this.getPredefinedV_f_i(f, i);
            if (d != null) {
                switch (d) {
                case Increasing:
                    res =
                        new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
                            this.constraintFactory.createTrue(), this.constraintFactory.createFalse());
                    break;
                case Decreasing:
                    res =
                        new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
                            this.constraintFactory.createFalse(), this.constraintFactory.createTrue());
                    break;
                case Independent:
                    res =
                        new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
                            this.constraintFactory.createTrue(), this.constraintFactory.createTrue());
                    break;
                default:
                    res =
                        new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
                            this.constraintFactory.createFalse(), this.constraintFactory.createFalse());
                }
                fEntry.put(i, res);
                f_EncEntry.put(
                    i,
                    new Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>(
                        false,
                        new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
                            this.constraintFactory.createTrue(), this.constraintFactory.createTrue())));
                return res;
            }
        }

        // add constraints
        final OrderPoly<BigIntImmutable> fPoly = this.get(f);
        assert (fPoly != null) : f;
        if (!fPoly.isFlat(this.polyRing, this.monoid)) {
            this.fvOuter.applyTo(fPoly);
        }
        final GPolyVar var = this.getVariableForFunctionSymbolArgument(i);

        final Set<OrderPolyConstraint<BigIntImmutable>> incConclusions =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        final Set<OrderPolyConstraint<BigIntImmutable>> decConclusions =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();

        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomial : fPoly.getMonomials(
            this.getOuterRingMonoid()).entrySet()) {
            final BigInteger exponent = monomial.getKey().getExponents().get(var);
            if (exponent != null) {
                // var occurs in monomial
                final BigInteger TWO = BigInteger.valueOf(2);
                final boolean evenExponent = exponent.mod(TWO).signum() == 0;
                boolean otherVarsWithOddExponent = false;
                if (!evenExponent) {
                    for (final Entry<GPolyVar, BigInteger> varExp : monomial.getKey().getExponents().entrySet()) {
                        if (!varExp.getKey().equals(var) && exponent.mod(TWO).signum() != 0) {
                            otherVarsWithOddExponent = true;
                            break;
                        }
                    }
                }
                final Pair<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> sortedCoeff =
                    SortNatPoly.sort(this, monomial.getValue());
                if (evenExponent || otherVarsWithOddExponent) {
                    final OrderPolyConstraint<BigIntImmutable> eqZero =
                        this.constraintFactory.createWithQuantifier(this.factory.buildFromCoeff(sortedCoeff.x),
                            this.factory.buildFromCoeff(sortedCoeff.y), ConstraintType.EQ);
                    incConclusions.add(eqZero);
                    decConclusions.add(eqZero);
                } else {
                    incConclusions.add(this.constraintFactory.createWithQuantifier(
                        this.factory.buildFromCoeff(sortedCoeff.x), this.factory.buildFromCoeff(sortedCoeff.y),
                        ConstraintType.GE));
                    decConclusions.add(this.constraintFactory.createWithQuantifier(
                        this.factory.buildFromCoeff(sortedCoeff.y), this.factory.buildFromCoeff(sortedCoeff.x),
                        ConstraintType.GE));
                }
            }
        }

        // create variables
        OrderPolyConstraint<BigIntImmutable> f_inc;
        OrderPolyConstraint<BigIntImmutable> f_dec;
        OrderPolyConstraint<BigIntImmutable> enc_inc;
        OrderPolyConstraint<BigIntImmutable> enc_dec;

        if (!incConclusions.isEmpty()) {
            f_inc = this.createVFILogVar(f, i, true);
            // f_inc > 0 => incConclusions
            enc_inc = this.constraintFactory.createAnd(incConclusions);
        } else {
            f_inc = this.constraintFactory.createTrue();
            enc_inc = f_inc;
        }

        if (!decConclusions.isEmpty()) {
            f_dec = this.createVFILogVar(f, i, false);
            // f_dec > 0 => decConclusions
            enc_dec = this.constraintFactory.createAnd(decConclusions);
        } else {
            f_dec = this.constraintFactory.createTrue();
            enc_dec = f_dec;
        }
        res =
            new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(f_inc, f_dec);
        // add to cache and return
        fEntry.put(i, res);
        f_EncEntry.put(
            i,
            new Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>(
                forceEncode,
                new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(enc_inc,
                    enc_dec)));
        /*
        // System.err.println("getV_f_i " + f + " / " +i + "\n" + constraintFactory.createOr(constraintFactory.createNot(f_inc),
                constraintFactory.createAnd(incConclusions)) + "\n" + constraintFactory.createOr(constraintFactory.createNot(f_dec),
                        constraintFactory.createAnd(decConclusions)));
                       */
        return res;
    }

    protected OPCLogVar<BigIntImmutable> createVFILogVar(final FunctionSymbol f, final int i, final boolean increasing) {
        return this.constraintFactory.createLogVar(IDPGInterpretation.V_f_i_PREFIX + f.getName() + "_" + i + (increasing ? "_inc" : "dec"));
    }

    public ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> iActiveAnd(final ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> x,
        final ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> y) {
        // result.x = x1^x2 v y1^y2 v x1^y1 v x2^y2
        // result.y = x1^x2 v y1^y2 v x1^y2 v x2^y1

        // shared = x1^x2 v y1^y2
        final OrderPolyConstraint<BigIntImmutable> shared =
            this.constraintFactory.createOr(this.constraintFactory.createAnd(x.x, x.y),
                this.constraintFactory.createAnd(y.x, y.y));

        final Set<OrderPolyConstraint<BigIntImmutable>> x_ors =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        x_ors.add(shared);
        x_ors.add(this.constraintFactory.createAnd(x.x, y.x));
        x_ors.add(this.constraintFactory.createAnd(x.y, y.y));

        final Set<OrderPolyConstraint<BigIntImmutable>> y_ors =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        y_ors.add(shared);
        y_ors.add(this.constraintFactory.createAnd(x.x, y.y));
        y_ors.add(this.constraintFactory.createAnd(x.y, y.x));

        return new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
            this.constraintFactory.createOr(x_ors), this.constraintFactory.createOr(y_ors));
    }

    public ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> iActiveOr(final ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> x,
        final ImmutablePair<? extends OrderPolyConstraint<BigIntImmutable>, ? extends OrderPolyConstraint<BigIntImmutable>> y) {
        // result.x = x1 & y1
        // result.y = x2 & y2

        return new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
            this.constraintFactory.createAnd(x.x, y.x), this.constraintFactory.createAnd(x.y, y.y));
    }

    public void setBoolConstantValue(final ConstantType constantType,
        final GeneralizedRule rule,
        final BigIntImmutable value) {
        final Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constantMap =
            this.boolConstants.get(constantType);
        this.getBoolConstant(constantType, rule);
        final Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> res = constantMap.get(rule);
        res.y = value;
        res.z = this.factory.getInnerFactory().buildFromCoeff(value);
    }

    public void resetBoolConstantValue(final ConstantType constantType, final GeneralizedRule rule) {
        final Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constantMap =
            this.boolConstants.get(constantType);
        this.getBoolConstant(constantType, rule);
        final Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> res = constantMap.get(rule);
        res.y = null;
        res.z = this.factory.getInnerFactory().buildFromVariable(res.x);
    }

    public BigIntImmutable getBoolConstantValue(final ConstantType constantType, final GeneralizedRule rule) {
        final Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constantMap =
            this.boolConstants.get(constantType);
        final Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> res = constantMap.get(rule);
        if (res == null) {
            return null;
        }
        return res.y;
    }

    public BigIntImmutable getBoolConstantValue(final ConstantType constantType, final TRSTerm term) {
        final Map<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constantMap =
            this.boolTermConstants.get(constantType);
        final Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> res = constantMap.get(term);
        if (res == null) {
            return null;
        }
        return res.y;
    }

    public GPoly<BigIntImmutable, GPolyVar> getBoolConstant(final ConstantType constantType, final GeneralizedRule rule) {
        final Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constantMap =
            this.boolConstants.get(constantType);
        Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> res = constantMap.get(rule);
        if (res == null) {
            final GPolyVar var = this.getNextCoeff(constantType.getPrefix(), this.boolRange);
            res =
                new Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>(var, null,
                    this.factory.getInnerFactory().buildFromVariable(var));
            constantMap.put(rule, res);
        }
        return res.z;
    }

    public ImmutableSet<GeneralizedRule> getBoolConstantRules(final ConstantType constantType) {
        return ImmutableCreator.create(new LinkedHashSet<GeneralizedRule>(this.boolConstants.get(constantType).keySet()));

    }

    public GPoly<BigIntImmutable, GPolyVar> getBoolConstant(final ConstantType constantType, final TRSTerm term) {
        final Map<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constantMap =
            this.boolTermConstants.get(constantType);
        Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> res = constantMap.get(term);
        if (res == null) {
            final GPolyVar var = this.getNextCoeff(constantType.getPrefix() + "_t", this.boolRange);
            /*
            if (constantType == ConstantType.CompareToNonInfConstant) {
                System.err.println("STRICT CONST: " + term + " = " + var);
            }*/
            res =
                new Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>(var, null,
                    this.factory.getInnerFactory().buildFromVariable(var));
            constantMap.put(term, res);
        }
        return res.z;
    }

    public GPoly<BigIntImmutable, GPolyVar> getBoolConstantVar(final ConstantType constantType,
        final GeneralizedRule rule) {
        final Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constantMap =
            this.boolConstants.get(constantType);
        Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> res = constantMap.get(rule);
        if (res == null) {
            final GPolyVar var = this.getNextCoeff(constantType.getPrefix(), this.boolRange);
            res =
                new Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>(var, null,
                    this.factory.getInnerFactory().buildFromVariable(var));
            constantMap.put(rule, res);
        }
        return this.factory.getInnerFactory().buildFromVariable(res.x);
    }

    public boolean getHasInitializedBoolConstant(final ConstantType constantType, final GeneralizedRule rule) {
        final Map<GeneralizedRule, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constantMap =
            this.boolConstants.get(constantType);
        return constantMap.containsKey(rule);
    }

    public boolean getHasInitializedBoolConstant(final ConstantType constantType, final TRSTerm term) {
        final Map<TRSTerm, Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>>> constantMap =
            this.boolTermConstants.get(constantType);
        return constantMap.containsKey(term);
    }

    public OrderPolyConstraint<BigIntImmutable> getLogVarConstant(final ConstantType constantType,
        final GeneralizedRule rule) {
        Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constantMap =
            this.ruleLogVars.get(rule);
        if (constantMap == null) {
            constantMap =
                new LinkedHashMap<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>();
            this.ruleLogVars.put(rule, constantMap);
        }
        Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>> res =
            constantMap.get(constantType);
        if (res == null) {
            final OPCLogVar<BigIntImmutable> var = this.getNextLogVar("r_" + rule + "_" + constantType.getPrefix());
            res = new Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>(var, null, var);
            constantMap.put(constantType, res);
        }
        return res.z;
    }

    public boolean getHasInitializedLogVar(final ConstantType constantType, final GeneralizedRule rule) {
        final Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constantMap =
            this.ruleLogVars.get(rule);
        if (constantMap == null) {
            return false;
        }
        final Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>> res =
            constantMap.get(constantType);
        if (res == null) {
            return false;
        }
        return true;
    }

    public Boolean getLogVarValue(final ConstantType constantType, final GeneralizedRule rule) {
        final Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constantMap =
            this.ruleLogVars.get(rule);
        if (constantMap == null) {
            return null;
        }
        final Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>> res =
            constantMap.get(constantType);
        if (res == null) {
            return null;
        }
        return res.y;
    }

    public OrderPolyConstraint<BigIntImmutable> getLogVarConstant(final ConstantType constantType, final TRSTerm t) {
        // System.err.println("getLogVarConstant " + constantType + " " + t);
        Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> constantMap =
            this.termLogVars.get(t);
        if (constantMap == null) {
            constantMap =
                new LinkedHashMap<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>();
            this.termLogVars.put(t, constantMap);
        }
        Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>> res =
            constantMap.get(constantType);
        if (res == null) {
            final OPCLogVar<BigIntImmutable> var = this.getNextLogVar("t_" + t + "_" + constantType.getPrefix());
            res = new Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>(var, null, var);
            constantMap.put(constantType, res);
        }
        return res.z;
    }

    /**
     *
     * @param constantType
     * @return must not be changed!
     */
    public Map<GeneralizedRule, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>> getLogVarRuleConstants() {
        return this.ruleLogVars;
    }

    public Set<OrderPolyConstraint<BigIntImmutable>> getRuleLogVars(final ConstantType constantType) {
        final LinkedHashSet<OrderPolyConstraint<BigIntImmutable>> res =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        for (final Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>> ruleMap : this.ruleLogVars.values()) {
            final Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>> logVar =
                ruleMap.get(constantType);
            if (logVar != null) {
                res.add(logVar.z);
            }
        }
        return ImmutableCreator.create(res);
    }

    public Set<GPoly<BigIntImmutable, GPolyVar>> getBoolConstants(final ConstantType constantType) {
        final LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>> res =
            new LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>>();
        for (final Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> pair : this.boolConstants.get(
            constantType).values()) {
            res.add(pair.z);
        }
        return ImmutableCreator.create(res);
    }

    public Set<GPoly<BigIntImmutable, GPolyVar>> getBoolUnknownConstants(final ConstantType constantType) {
        final LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>> res =
            new LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>>();
        for (final Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> pair : this.boolConstants.get(
            constantType).values()) {
            if (pair.y == null) {
                res.add(pair.z);
            }
        }
        return ImmutableCreator.create(res);
    }

    public Set<GPoly<BigIntImmutable, GPolyVar>> getBoolTermConstants(final ConstantType constantType) {
        final LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>> res =
            new LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>>();
        for (final Triple<GPolyVar, BigIntImmutable, GPoly<BigIntImmutable, GPolyVar>> pair : this.boolTermConstants.get(
            constantType).values()) {
            res.add(pair.z);
        }
        return ImmutableCreator.create(res);
    }

    private Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>> duplicatePathToRoot(final Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>> kPathToRoot) {
        if (kPathToRoot.y instanceof Immutable) {
            return new Pair<RelDependency, List<ImmutablePair<FunctionSymbol, Integer>>>(kPathToRoot.x, kPathToRoot.y);
        }
        final ArrayList<ImmutablePair<FunctionSymbol, Integer>> res =
            new ArrayList<ImmutablePair<FunctionSymbol, Integer>>(kPathToRoot.y);
        return new Pair<RelDependency, List<ImmutablePair<FunctionSymbol, Integer>>>(kPathToRoot.x,
            ImmutableCreator.create(res));
    }

    public OPCRange<BigIntImmutable> getBoolRange() {
        return this.boolRange;
    }

    public static String[] getContextExtensions() {
        return IDPGInterpretation.contextExtensions;
    }

    public boolean isNat() {
        return this.isNat;
    }

    public boolean isTupleNat() {
        return this.isTupleNat;
    }

    @Override
    protected String getDescription(final Export_Util eu) {
        if (this.isTupleNat) {
            return "Polynomial interpretation over integers with natural coefficients for all symbols "
                + eu.cite(Citation.NONINF);
        } else if (this.isNat) {
            return "Polynomial interpretation over integers with natural coefficients for non-tuple symbols "
                + eu.cite(Citation.NONINF);
        } else {
            return "Polynomial interpretation over integers";
        }
    }

    protected OrderPoly<BigIntImmutable> interpretAsArbitraryConstant(final TRSTerm term) {
        throw new UnsupportedOperationException("Use IDPNonInInterpretation for bound things");
    }

    public IDPRuleAnalysis getRuleAnalysis() {
        return this.ruleAnalysis;
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder result =
            new StringBuilder(this.getDescription(eu) + eu.cite(this.citations.toArray(new Citation[0])) + ":\n");

        final int size = this.pol.size();
        final List<String> rows = new ArrayList<String>(size);

        Map<FunctionSymbol, OrderPoly<BigIntImmutable>> sortedPol; // for ordered display
        sortedPol = new LinkedHashMap<FunctionSymbol, OrderPoly<BigIntImmutable>>(this.pol);
        for (final Map.Entry<FunctionSymbol, OrderPoly<BigIntImmutable>> entry : sortedPol.entrySet()) {
            String row = this.exportPoly(eu, entry.getKey(), entry.getValue(), null, null, null);
            // nasty hack for equidistant lines in HTML (and hence the GUI)
            if (eu instanceof HTML_Util) {
                row += "<sup>&nbsp;</sup> <sub>&nbsp;</sub>";
            }
            rows.add(row);
        }

        if (!this.contextPol.isEmpty()) {
            rows.add("");
            rows.add("Polynomial Interpretations with Context Sensitive Arithemetic Replacement");
            final StringBuilder legend = new StringBuilder();
            legend.append("POL(Term");
            legend.append(eu.sup("CSAR-Mode"));
            legend.append(" @ Context)");
            rows.add(legend.toString());
            rows.add("");
            Map<FunctionSymbol, Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>> sortedContextPol; // for ordered display
            sortedContextPol =
                new LinkedHashMap<FunctionSymbol, Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>>(
                    this.contextPol);
            for (final Map.Entry<FunctionSymbol, Map<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>>> entry : sortedContextPol.entrySet()) {
                for (final Map.Entry<Pair<RelDependency, ? extends List<ImmutablePair<FunctionSymbol, Integer>>>, Map<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>>> k_pathEntry : entry.getValue().entrySet()) {
                    for (final Map.Entry<List<? extends TRSTerm>, OrderPoly<BigIntImmutable>> argsEntry : k_pathEntry.getValue().entrySet()) {
                        String row =
                            this.exportPoly(eu, entry.getKey(), argsEntry.getValue(), k_pathEntry.getKey().x,
                                k_pathEntry.getKey().y, argsEntry.getKey());
                        // nasty hack for equidistant lines in HTML (and hence the GUI)
                        if (eu instanceof HTML_Util) {
                            row += "<sup>&nbsp;</sup> <sub>&nbsp;</sub>";
                        }
                        rows.add(row);
                    }
                }
            }
        }

        result.append(eu.set(rows, Export_Util.RULES));
        return result.toString();
    }

}
