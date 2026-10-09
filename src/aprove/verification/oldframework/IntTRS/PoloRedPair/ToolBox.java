package aprove.verification.oldframework.IntTRS.PoloRedPair;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.BoundedInts.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.PolynomialConstraint.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A collection of helper functions.
 * @author Matthias Hoelzel
 */
public abstract class ToolBox {
    /**
     * Predefined map
     */
    public static final IDPPredefinedMap PREDEFINED = IDPPredefinedMap.DEFAULT_MAP;

    /**
     * SMT engine to be used.
     */
    public static final SMTEngine SMT_ENGINE = new YicesEngine();

    /**
     * Zero as SMTLIBIntConstant.
     */
    public static final SMTLIBIntConstant SMT_INT_ZERO = SMTLIBIntConstant.create(BigInteger.ZERO);

    public static final TRSFunctionApplication ZERO = buildInt(0);
    public static final TRSFunctionApplication ONE = buildInt(1);

    /**
     * Rewrites a boolean int-term to polynomial constraints. The method only
     * generates constraints with PCT_GE, PCT_EQ, PCT_LE.
     * @param func Term to rewrite. The user has to ensure, that the term has
     * the correct structure!
     * @param ng a Name generator
     * @param aborter
     * @return List of PolynomialConstraints
     * @throws AbortionException
     */
    public static List<PolynomialConstraint> boolTermToPolynomialConstraints(final TRSFunctionApplication func,
        final FreshNameGenerator ng,
        final Abortion aborter) throws AbortionException {
        final List<PolynomialConstraint> result = new LinkedList<>();

        ToolBox.translateBoolTerm(func, result, ng, aborter);

        return result;
    }

    /**
     * Builds the term AND([t1], [t2])
     * @param t1 first term
     * @param t2 second term
     * @return a term
     */
    public static TRSFunctionApplication buildAnd(final TRSTerm t1, final TRSTerm t2) {
        return ToolBox.buildFunc(t1, Func.Land, t2, DomainFactory.BOOLEAN);
    }

    /**
     * Builds the term NOT t
     * @param t term
     * @return a term
     */
    public static TRSFunctionApplication buildNot(final TRSTerm t) {
        return TRSTerm.createFunctionApplication(IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Lnot, DomainFactory.BOOLEAN), t);
    }

    /**
     * Builds the conjunction of given formulas.
     * @param formulas list of formulas
     * @return a term
     */
    public static TRSTerm buildAnd(final Collection<? extends TRSTerm> formulas) {
        if (formulas.isEmpty()) {
            return ToolBox.buildTrue();
        } else {
            final Iterator<? extends TRSTerm> iter = formulas.iterator();
            TRSTerm result = iter.next();
            while (iter.hasNext()) {
                result = ToolBox.buildAnd(result, iter.next());
            }
            return result;
        }
    }

    public static TRSFunctionApplication buildInt(long i) {
        return buildInt(BigInteger.valueOf(i));
    }

    /**
     * Builds the term representing an integer.
     * @param value BigInteger
     * @return a term
     */
    public static TRSFunctionApplication buildInt(final BigInteger value) {
        return TRSTerm.createFunctionApplication(IDPPredefinedMap.DEFAULT_MAP.getIntSym(BigIntImmutable.create(value),
            DomainFactory.INTEGERS));
    }

    /**
     * @param terms - [t1, ..., tn] for some n >= 0
     * @return a term equivalent to t1 + ... + tn
     */
    public static TRSTerm buildSum(final Collection<? extends TRSTerm> terms) {
        return buildFold(terms, Func.Add, ZERO, DomainFactory.INTEGERS);
    }

    public static TRSTerm buildSum(TRSTerm... terms) {
        return buildSum(Arrays.asList(terms));
    }

    /**
     * @param terms - [t1, ..., tn] for some n >= 0
     * @return a term equivalent to t1 * ... * tn
     */
    public static TRSTerm buildProduct(final List<TRSTerm> terms) {
        return buildFold(terms, Func.Mul, ONE, DomainFactory.INTEGERS);
    }

    public static TRSTerm buildProduct(TRSTerm... terms) {
        return buildProduct(Arrays.asList(terms));
    }

    public static TRSTerm buildDiv(final TRSTerm t1, final TRSTerm t2) {
        return ToolBox.buildFunc(t1, Func.Div, t2, DomainFactory.INTEGERS);
    }

    /**
     * Builds the term OR([t1], [t2])
     * @param t1 first term
     * @param t2 second term
     * @return a term
     */
    public static TRSTerm buildOr(final TRSTerm t1, final TRSTerm t2) {
        return ToolBox.buildFunc(t1, Func.Lor, t2, DomainFactory.BOOLEAN);
    }

    /**
     * Builds the term [t1] <= [t2]
     * @param t1 first term
     * @param t2 second term
     * @return a term
     */
    public static TRSFunctionApplication buildLe(final TRSTerm t1, final TRSTerm t2) {
        return ToolBox.buildFunc(t1, Func.Le, t2, DomainFactory.INTEGERS);
    }

    /**
     * Builds the term [t1] < [t2]
     * @param t1 first term
     * @param t2 second term
     * @return a term
     */
    public static TRSFunctionApplication buildLt(final TRSTerm t1, final TRSTerm t2) {
        return ToolBox.buildFunc(t1, Func.Lt, t2, DomainFactory.INTEGERS);
    }

    /**
     * Builds the term [t1] >= [t2]
     * @param t1 first term
     * @param t2 second term
     * @return a term
     */
    public static TRSFunctionApplication buildGe(final TRSTerm t1, final TRSTerm t2) {
        return ToolBox.buildFunc(t1, Func.Ge, t2, DomainFactory.INTEGERS);
    }

    public static TRSFunctionApplication buildNonNegative(TRSTerm t) {
        return buildLe(ZERO, t);
    }

    public static TRSFunctionApplication buildNonPositive(TRSTerm t) {
        return buildLe(t, ZERO);
    }

    /**
     * Builds the term [t1] > [t2]
     * @param t1 first term
     * @param t2 second term
     * @return a term
     */
    public static TRSFunctionApplication buildGt(final TRSTerm t1, final TRSTerm t2) {
        return ToolBox.buildFunc(t1, Func.Gt, t2, DomainFactory.INTEGERS);
    }

    public static TRSFunctionApplication buildPositive(TRSTerm t) {
        return buildLt(ZERO, t);
    }

    public static TRSFunctionApplication buildNegative(TRSTerm t) {
        return buildLt(t, ZERO);
    }

    /**
     * Builds the term [t1] == [t2]
     * @param t1 first term
     * @param t2 second term
     * @return a term
     */
    public static TRSFunctionApplication buildEq(final TRSTerm t1, final TRSTerm t2) {
        return ToolBox.buildFunc(t1, Func.Eq, t2, DomainFactory.INTEGERS);
    }

    /**
     * It just builds TRUE as a term.
     * @return a Term
     */
    public static TRSFunctionApplication buildTrue() {
        return TRSTerm.createFunctionApplication(ToolBox.PREDEFINED.getBooleanTrue().getSym());
    }

    /**
     * It just builds FALSE as a term.
     * @return a Term
     */
    public static TRSTerm buildFalse() {
        return TRSTerm.createFunctionApplication(ToolBox.PREDEFINED.getBooleanFalse().getSym());
    }

    public static TRSTerm buildBool(final boolean value) {
        return value ? ToolBox.buildTrue() : ToolBox.buildFalse();
    }

    /**
     * @param t  a non-null term
     * @return (-1)*t
     */
    public static TRSTerm buildMinus(final TRSTerm t) {
        final TRSTerm minusOne = ToolBox.buildInt(BigInteger.valueOf(-1L));
        final TRSTerm res = ToolBox.buildFunc(minusOne, Func.Mul, t, DomainFactory.INTEGERS);
        return res;
    }

    /**
     * Builds a predefined term.
     * @param t1 first term
     * @param f some "Func"
     * @param t2 second term
     * @param d some domain
     * @return a term
     */
    private static TRSFunctionApplication buildFunc(final TRSTerm t1, final Func f, final TRSTerm t2, final Domain d) {
        final FunctionSymbol sym = ToolBox.PREDEFINED.getSym(f, d);
        assert sym.getArity() == 2;
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(2);
        args.add(t1);
        args.add(t2);
        return TRSTerm.createFunctionApplication(sym, args);
    }

    /**
     * Folds terms with f, the neutral element is used only if terms is empty.
     *
     * @param terms - [t1, ..., tn] for n >= 0
     * @param f - function beknownst to IDPPredefinedMap.DEFAULT_MAP
     * @param neutral - to be returned iff terms is empty (ignored otherwise)
     * @param d - the domain for f
     * @return neutral if terms is empty, otherwise (...((t1 f t2) f t3) ... tn)
     */
    private static TRSTerm buildFold(final Collection<? extends TRSTerm> terms, final Func f, final TRSTerm neutral, final Domain d) {
        if (terms.isEmpty()) {
            return neutral;
        }
        final Iterator<? extends TRSTerm> iter = terms.iterator();
        TRSTerm res = iter.next();
        while (iter.hasNext()) {
            final TRSTerm ti = iter.next();
            res = ToolBox.buildFunc(res, f, ti, d);
        }
        return res;
    }

    /**
     * Rewrite a boolean int-term to a list of SMT atoms.
     * @param bTerm boolean int-based term to be rewritten
     * @param ng name generator
     * @param formulas list of formulae to be completed [needed to express some
     * knowledge about non-linear arithmetic]
     * @param factory factory to build formulas
     * @param aborter
     * @return list of SMTLIBTheoryAtom
     * @throws AbortionException
     */
    public static List<SMTLIBTheoryAtom> boolTermToSMTTheoryAtoms(
        final TRSTerm bTerm,
        final FreshNameGenerator ng,
        final List<Formula<SMTLIBTheoryAtom>> formulas,
        final FormulaFactory<SMTLIBTheoryAtom> factory,
        final Abortion aborter) throws AbortionException {
        final LinkedList<SMTLIBTheoryAtom> result = new LinkedList<>();
        if (!bTerm.isVariable()) {
            assert bTerm instanceof TRSFunctionApplication : "Non-variable term should be function application!";
            final List<PolynomialConstraint> polyConstraints =
                    ToolBox.boolTermToPolynomialConstraints((TRSFunctionApplication) bTerm, ng, aborter);
            for (final PolynomialConstraint pc : polyConstraints) {
                result.add(pc.toSMT(formulas, factory, ng));
            }
            formulas.addAll(factory.buildTheoryAtoms(result));
        }

        return result;
    }

    /**
     * Rewrites a boolean int-term to polynomial constraints and fills them in
     * the list.
     * @param func FunctionApplication to rewrite
     * @param result List to fill in constraints
     * @param ng name generator
     * @param aborter
     * @throws AbortionException
     */
    private static void translateBoolTerm(final TRSFunctionApplication func,
        final List<PolynomialConstraint> result,
        final FreshNameGenerator ng,
        final Abortion aborter) throws AbortionException {
        aborter.checkAbortion();
        final FunctionSymbol symbol = func.getRootSymbol();
        if (ToolBox.PREDEFINED.isLand(symbol)) {
            ToolBox.translateBoolTerms(func.getArguments(), result, ng, aborter);
        } else if (ToolBox.PREDEFINED.isGt(symbol)) {
            result.add(PolynomialConstraint.create(
                ToolBox.intTermToPolynomial(func.getArgument(0), ng).minus(VarPolynomial.ONE),
                PolynomialConstraintType.PCT_GE, ToolBox.intTermToPolynomial(func.getArgument(1), ng), ng));
        } else if (ToolBox.PREDEFINED.isGe(symbol)) {
            result.add(PolynomialConstraint.create(ToolBox.intTermToPolynomial(func.getArgument(0), ng),
                PolynomialConstraintType.PCT_GE, ToolBox.intTermToPolynomial(func.getArgument(1), ng), ng));
        } else if (ToolBox.PREDEFINED.isLt(symbol)) {
            result.add(PolynomialConstraint.create(
                ToolBox.intTermToPolynomial(func.getArgument(0), ng).plus(VarPolynomial.ONE),
                PolynomialConstraintType.PCT_LE, ToolBox.intTermToPolynomial(func.getArgument(1), ng), ng));
        } else if (ToolBox.PREDEFINED.isLe(symbol)) {
            result.add(PolynomialConstraint.create(ToolBox.intTermToPolynomial(func.getArgument(0), ng),
                PolynomialConstraintType.PCT_LE, ToolBox.intTermToPolynomial(func.getArgument(1), ng), ng));
        } else if (ToolBox.PREDEFINED.isEq(symbol)) {
            result.add(PolynomialConstraint.create(ToolBox.intTermToPolynomial(func.getArgument(0), ng),
                PolynomialConstraintType.PCT_EQ, ToolBox.intTermToPolynomial(func.getArgument(1), ng), ng));
        } else if (ToolBox.PREDEFINED.isBooleanTrue(symbol)) {
            // Pass
            return;
        } else if (ToolBox.PREDEFINED.isBooleanFalse(symbol)) {
            result.add(PolynomialConstraint.create(VarPolynomial.ONE, PolynomialConstraintType.PCT_EQ, VarPolynomial.ZERO, ng));
        } else {
            assert false : "Unhandled symbol: " + symbol.toString() + "!";
        }
    }

    /**
     * Rewrites boolean int-terms to polynomial constraints and fills them in
     * the list.
     * @param terms List of terms to rewrite
     * @param result List to fill in constraints
     * @param ng name generator
     * @throws AbortionException
     */
    private static void translateBoolTerms(final List<TRSTerm> terms,
        final List<PolynomialConstraint> result,
        final FreshNameGenerator ng,
        final Abortion aborter) throws AbortionException {
        for (final TRSTerm t : terms) {
            assert t instanceof TRSFunctionApplication;
            ToolBox.translateBoolTerm((TRSFunctionApplication) t, result, ng, aborter);
        }
    }

    /**
     * Returns all the variables which occur in the given rule.
     * @param r a rule
     * @return set of variables
     */
    public static LinkedHashSet<TRSVariable> getVariables(final IGeneralizedRule r) {
        final LinkedHashSet<TRSVariable> result = new LinkedHashSet<TRSVariable>();
        result.addAll(r.getVariables());
        result.addAll(r.getCondVariables());
        return result;
    }

    /**
     * Returns all the variables which only occur in the condition.
     * @param r a rule
     * @return set of variables
     */
    public static LinkedHashSet<TRSVariable> getFreeVariables(final IGeneralizedRule r) {
        final Set<TRSVariable> condVars = r.getCondTerm().getVariables();
        final LinkedHashSet<TRSVariable> result = new LinkedHashSet<TRSVariable>(condVars);
        // getVariables from IGeneralizedRule returns for some reason only variable
        // which do not occur in the condition ..
        final Set<TRSVariable> ruleVariables = r.getVariables();
        result.removeAll(ruleVariables);
        return result;
    }

    /**
     * Adds n variable to the argument list. It also takes care of the arity.
     * @param funcy FunctionApplication
     * @param n int
     * @param ng NameGenerator
     * @return FunctionApplication
     */
    public static TRSFunctionApplication addVariables(final TRSFunctionApplication funcy,
        final int n,
        final FreshNameGenerator ng) {
        final ImmutableList<TRSTerm> args = funcy.getArguments();
        final List<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size() + n);
        newArgs.addAll(args);
        for (int i = 0; i < n; i++) {
            newArgs.add(TRSTerm.createVariable(ng.getFreshName("q", false)));
        }
        final FunctionSymbol oldSym = funcy.getRootSymbol();
        final FunctionSymbol newSym = FunctionSymbol.create(oldSym.getName(), newArgs.size());
        return TRSTerm.createFunctionApplication(newSym, newArgs);
    }

    /**
     * Rewrites a polynomial to an int-term.
     * Currently hardwired to use IDPPredefinedMap.DEFAULT_MAP
     * for the predefined integer function symbols.
     *
     * @param poly - a non-null polynomial where all coefficients are
     *  just concrete numbers (i.e., the SimplePolynomials for the
     *  coefficients are constants)
     * @return a term that is equivalent to poly in the ITRS setting,
     *  using IDPPredefinedMap.DEFAULT_MAP
     */
    public static TRSTerm polynomialToIntTerm(final VarPolynomial poly) {
        if (Globals.useAssertions) {
            assert poly.isConcrete() : "Only polynomials with concrete coefficients, please (no unknowns in there).";
        }
        final List<TRSTerm> addends = new ArrayList<TRSTerm>(poly.numberOfAddends());
        for (final Entry<IndefinitePart, SimplePolynomial> monomial : poly.getVarMonomials().entrySet()) {
            // shall contain explicitly all factors (there is no exponent
            // in the IDPPredefinedMap setting, so enumerate)
            final List<TRSTerm> factors = new ArrayList<TRSTerm>();

            // the first factor's a number ...
            final SimplePolynomial coeffPoly = monomial.getValue();
            final BigInteger coeffNumber = coeffPoly.getNumericalAddend();
            if (!coeffNumber.equals(BigInteger.ONE)) { // don't multiply with 1
                final TRSTerm coeffTerm = ToolBox.buildInt(coeffNumber);
                factors.add(coeffTerm);
            }

            // ... the later ones are variables
            final IndefinitePart varPart = monomial.getKey();
            for (final Entry<String, Integer> varToPower : varPart.getExponents().entrySet()) {
                final String varName = varToPower.getKey();
                final int power = varToPower.getValue();
                final TRSTerm varTerm = TRSTerm.createVariable(varName);
                for (int i = 0; i < power; ++i) {
                    factors.add(varTerm);
                }
            }

            // now we have all factors for the current addend, so multiply!
            final TRSTerm monomialTerm = ToolBox.buildProduct(factors);
            addends.add(monomialTerm);
        }

        // now we also have the addends, so add them up!
        final TRSTerm res = ToolBox.buildSum(addends);
        return res;
    }

    /**
     * Rewrites an int-term to a polynomial.
     * @param t a int-term
     * @param ng a name generator
     * @return a polynomial
     */
    public static VarPolynomial intTermToPolynomial(final TRSTerm t, final FreshNameGenerator ng) {
        if (t instanceof TRSVariable) {
            // Variables are not touched!
            final TRSVariable v = (TRSVariable) t;
            return VarPolynomial.createVariable(v.getName());
        } else {
            // Predefined function symbols have to be treated individually
            // 1. Get all information we need
            assert t instanceof TRSFunctionApplication : "Non-variable term should be function application!";
        final TRSFunctionApplication func = (TRSFunctionApplication) t;
        final FunctionSymbol sym = func.getRootSymbol();

        // 2. Rewrite arguments
        final List<VarPolynomial> arguments = new ArrayList<VarPolynomial>(func.getSize());
        for (final TRSTerm arg : func.getArguments()) {
            arguments.add(ToolBox.intTermToPolynomial(arg, ng));
        }

        // 3. What symbol do we have to handle?
        VarPolynomial result = null;
        if (PREDEFINED.isInt(sym, DomainFactory.INTEGERS)) {
            final BigInteger n = PREDEFINED.getInt(sym, DomainFactory.INTEGERS);
            result = VarPolynomial.create(n);
        } else if (PREDEFINED.isAdd(sym)) {
            result = VarPolynomial.plus(arguments);
        } else if (PREDEFINED.isSub(sym)) {
            result = arguments.get(0);
            for (int i = 1; i < arguments.size(); i++) {
                result = result.plus(arguments.get(i).negate());
            }
        } else if (PREDEFINED.isDivOrMod(sym)) {
            result = VarPolynomial.createVariable(ng.getFreshName("divOrMod", false));
        } else if (PREDEFINED.isMul(sym)) {
            result = arguments.get(0);
            for (int i = 1; i < arguments.size(); i++) {
                result = result.times(arguments.get(i));
            }
        } else if (BoundedSymbolFactory.isCastSymbol(sym)) {
            result = VarPolynomial.createVariable(ng.getFreshName("cast", false));
        }

        // 4. Check for failure
        if (result == null) {
            assert false : "Cannot handle symbol \"" + sym + "\"!";
        return null;
        } else {
            return result;
        }
        }
    }

    /**
     * Rewrites a boolean term to a SMT-IA-Formula. Calls
     * ToolBox.boolTermToSMT_QF_IA recursively!
     * @param t a boolean term
     * @param factory some formula factory
     * @param ng some name generator
     * @return Formula\<SMTLIBTheoryAtom\>
     */
    private static List<Formula<SMTLIBTheoryAtom>> argumentsToSMT_QF_IA(final TRSFunctionApplication t,
        final FormulaFactory<SMTLIBTheoryAtom> factory,
        final FreshNameGenerator ng) {
        final LinkedList<Formula<SMTLIBTheoryAtom>> resultList = new LinkedList<>();
        for (final TRSTerm arg : t.getArguments()) {
            resultList.add(ToolBox.boolTermToSMT_QF_IA(arg, factory, ng));
        }
        return resultList;
    }

    /**
     * Rewrites a boolean term to a SMT-IA-Formula. Uses VarPolynomial.toSMT().
     * @param t a boolean term
     * @param factory some formula factory
     * @param ng some name generator
     * @return Formula\<SMTLIBTheoryAtom\>
     */
    public static Formula<SMTLIBTheoryAtom> boolTermToSMT_QF_IA(final TRSTerm t,
        final FormulaFactory<SMTLIBTheoryAtom> factory,
        final FreshNameGenerator ng) {
        if (t == null) {
            // null always corresponds to the true formula:
            return ToolBox.boolTermToSMT_QF_IA(ToolBox.buildTrue(), factory, ng);
        }
        if (!(t instanceof TRSFunctionApplication)) {
            assert false : "Term is not a valid formula: " + t;
        return null;
        } else {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol rootSym = func.getRootSymbol();

            if (IDPPredefinedMap.DEFAULT_MAP.isLand(rootSym)) {
                return factory.buildAnd(ToolBox.argumentsToSMT_QF_IA(func, factory, ng));
            } else if (IDPPredefinedMap.DEFAULT_MAP.isLor(rootSym)) {
                return factory.buildOr(ToolBox.argumentsToSMT_QF_IA(func, factory, ng));
            } else if (IDPPredefinedMap.DEFAULT_MAP.isLnot(rootSym)) {
                return factory.buildNot(ToolBox.boolTermToSMT_QF_IA(func.getArgument(0), factory, ng));
            } else if (IDPPredefinedMap.DEFAULT_MAP.isBooleanTrue(rootSym)) {
                return factory.buildConstant(true);
            } else if (IDPPredefinedMap.DEFAULT_MAP.isBooleanFalse(rootSym)) {
                return factory.buildConstant(false);
            } else {
                assert rootSym.getArity() == 2 : "Unexcepted arity: " + rootSym;

                final VarPolynomial arg1 = ToolBox.intTermToPolynomial(func.getArgument(0), ng);
                final VarPolynomial arg2 = ToolBox.intTermToPolynomial(func.getArgument(1), ng);

                final SMTLIBIntValue val1 = arg1.toSMTLIB();
                final SMTLIBIntValue val2 = arg2.toSMTLIB();

                SMTLIBTheoryAtom atom;

                if (IDPPredefinedMap.DEFAULT_MAP.isGe(rootSym)) {
                    atom = SMTLIBIntGE.create(val1, val2);
                } else if (IDPPredefinedMap.DEFAULT_MAP.isGt(rootSym)) {
                    atom = SMTLIBIntGT.create(val1, val2);
                } else if (IDPPredefinedMap.DEFAULT_MAP.isLe(rootSym)) {
                    atom = SMTLIBIntLE.create(val1, val2);
                } else if (IDPPredefinedMap.DEFAULT_MAP.isLt(rootSym)) {
                    atom = SMTLIBIntLT.create(val1, val2);
                } else if (IDPPredefinedMap.DEFAULT_MAP.isEq(rootSym)) {
                    atom = SMTLIBIntEquals.create(val1, val2);
                } else if (IDPPredefinedMap.DEFAULT_MAP.isNeq(rootSym)) {
                    atom = SMTLIBIntEquals.create(val1, val2);
                    return factory.buildNot(factory.buildTheoryAtom(atom));
                } else {
                    assert rootSym.getArity() == 2 : "Unexcepted symbol: " + rootSym;
                    return null;
                }

                return factory.buildTheoryAtom(atom);
            }
        }
    }

    /**
     * Returns true IFF the current t is c
     * @param t a Term
     * @param c a BigInteger
     * @return boolean
     */
    static boolean isConcreteConstant(final TRSTerm t, final BigInteger c) {
        if (t.isConstant()) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (ToolBox.PREDEFINED.getInt(sym, DomainFactory.INTEGERS).compareTo(c) == 0) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns true IFF the current t is the ZERO constant
     * @param t a Term
     * @return boolean
     */
    static boolean isZEROTerm(final TRSTerm t) {
        return ToolBox.isConcreteConstant(t, BigInteger.ZERO);
    }

    /**
     * Returns true IFF the current t is the ZERO constant
     * @param t a Term
     * @return boolean
     */
    static boolean isONETerm(final TRSTerm t) {
        return ToolBox.isConcreteConstant(t, BigInteger.ONE);
    }

    /**
     * Returns true IFF [indef] equals 1.
     * @param indef an indefinite part
     * @return boolean
     */
    static boolean isOne(final IndefinitePart indef) {
        for (final Entry<String, Integer> entry : indef.getExponents().entrySet()) {
            if (entry.getValue().compareTo(0) == 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * Calculates n over k.
     * @param n an integer
     * @param k another integer
     * @return BigInteger
     */
    public static BigInteger calculateBinomialCoefficient(final int n, final int k) {
        BigInteger result = BigInteger.ONE;
        final int limit = k > n / 2 ? n - k : k;

        for (int i = 0; i < limit; i++) {
            result = result.multiply(BigInteger.valueOf(n - i)).divide(BigInteger.valueOf(i + 1));
        }

        return result;
    }

    /**
     * Creates the indefinite part [a]^[expa] * [b]^[expb]. This method is also
     * safe for expa = 0 or expb = 0. If expa <= 0, then we assume expa = 0.
     * (Analogous for expb.)
     * @param a first variable
     * @param expa first exponent
     * @param b second variable
     * @param expb second exponent
     * @return IndefinitePart
     */
    static IndefinitePart createIndefinitePart(final String a, final int expa, final String b, final int expb) {
        final IndefinitePart parta;
        if (expa > 0) {
            parta = IndefinitePart.create(a, expa);
        } else {
            parta = IndefinitePart.ONE;
        }

        final IndefinitePart partb;
        if (expb > 0) {
            partb = IndefinitePart.create(b, expb);
        } else {
            partb = IndefinitePart.ONE;
        }

        return parta.times(partb);
    }

    /**
     * Calculates ROUNDUP(x/y).
     * @param x a BigInteger
     * @param y another BigInteger, not zero.
     * @return a BigInteger
     */
    static BigInteger divideAndRoundUp(final BigInteger x, final BigInteger y) {
        final BigInteger[] arr = x.divideAndRemainder(y);
        assert arr.length == 2;

        final BigInteger div = arr[0];
        final BigInteger rest = arr[1];

        final int comparison = rest.compareTo(BigInteger.ZERO);

        if (comparison > 0) {
            return div.add(BigInteger.ONE);
        } else {
            return div;
        }
    }

    /**
     * Calculates ROUNDDOWN(x/y).
     * @param x a BigInteger
     * @param y another BigInteger, not zero.
     * @return a BigInteger
     */
    static BigInteger divideAndRoundDown(final BigInteger x, final BigInteger y) {
        final BigInteger[] arr = x.divideAndRemainder(y);
        assert arr.length == 2;

        final BigInteger div = arr[0];
        final BigInteger rest = arr[1];

        final int comparison = rest.compareTo(BigInteger.ZERO);

        if (comparison < 0) {
            return div.subtract(BigInteger.ONE);
        } else {
            return div;
        }
    }

    /**
     * Creates a polynomial (actually it is a monomial)
     * @param simple a simplePolynom, storing the coefficient
     * @param indef the indefinite part, storing the variables
     * @return a VarPolynomial
     */
    public static VarPolynomial createVarPolynomial(final SimplePolynomial simple, final IndefinitePart indef) {
        final LinkedHashMap<IndefinitePart, SimplePolynomial> map =
            new LinkedHashMap<IndefinitePart, SimplePolynomial>(1);
        map.put(indef, simple);
        if (simple.isZero()) {
            return VarPolynomial.ZERO;
        }
        return VarPolynomial.create(ImmutableCreator.create(map));
    }

    /**
     * Rewrites an indefinite part to a SMTLIBIntValue.
     * @param indef indefinite part to rewrite
     * @return corresponding SMTLIBIntValue
     */
    public static SMTLIBIntValue rewriteIndefinitePartToSMTLIBIntValue(final IndefinitePart indef) {
        final Set<Entry<String, Integer>> exponents = indef.getExponents().entrySet();
        final LinkedList<SMTLIBIntValue> arguments = new LinkedList<SMTLIBIntValue>();
        for (final Entry<String, Integer> exponent : exponents) {
            arguments.add(ToolBox.rewriteExponentToSMTLIBIntValue(exponent.getKey(), exponent.getValue()));
        }

        if (exponents.size() == 0) {
            return SMTLIBIntConstant.create(BigInteger.ONE);
        } else if (exponents.size() == 1) {
            return arguments.getFirst();
        } else {
            return SMTLIBIntMult.create(arguments);
        }
    }

    /**
     * Rewrites an indefinite part to a SMTLIBRatValue.
     * @param indef indefinite part to rewrite
     * @return corresponding SMTLIBRatValue
     */
    public static SMTLIBRatValue rewriteIndefinitePartToSMTLIBRatValue(final IndefinitePart indef) {
        final Set<Entry<String, Integer>> exponents = indef.getExponents().entrySet();
        final LinkedList<SMTLIBRatValue> arguments = new LinkedList<SMTLIBRatValue>();
        for (final Entry<String, Integer> exponent : exponents) {
            arguments.add(ToolBox.rewriteExponentToSMTLIBRatValue(exponent.getKey(), exponent.getValue()));
        }

        if (exponents.size() == 0) {
            return SMTLIBRatConstant.create(BigInteger.ONE);
        } else if (exponents.size() == 1) {
            return arguments.getFirst();
        } else {
            return SMTLIBRatMult.create(arguments);
        }
    }

    /**
     * Evaluates a given indefinite part.
     * @param indefPart {@link IndefinitePart}
     * @param interpretation maps variables (Strings) to Rationals
     * @return PreciseRational
     */
    static PreciseRational evaluateIndefinitePart(final IndefinitePart indefPart,
        final Map<String, PreciseRational> interpretation) {
        final PreciseRational one = new PreciseRational(BigInteger.ONE);
        PreciseRational result = one;

        for (final Entry<String, Integer> e : indefPart.getExponents().entrySet()) {
            PreciseRational val = one;
            final PreciseRational key = interpretation.get(e.getKey());
            for (int i = 0; i < e.getValue(); i++) {
                val = val.multiply(key);
            }
            result = result.multiply(val);
        }
        return result;
    }

    /**
     * Evaluates a given simple polynomial.
     * @param sp SimplePolynomial
     * @param interpretation maps variables (Strings) to PreciseRationals
     * @return PreciseRational
     */
    public static PreciseRational evaluateSimplePolynomial(final SimplePolynomial sp,
        final Map<String, PreciseRational> interpretation) {
        PreciseRational result = new PreciseRational(BigInteger.ZERO);
        for (final Entry<IndefinitePart, BigInteger> e : sp.getSimpleMonomials().entrySet()) {
            final BigInteger bi = e.getValue();
            final PreciseRational r =
                ToolBox.evaluateIndefinitePart(e.getKey(), interpretation).multiply(new PreciseRational(bi));
            result = result.add(r);
        }
        return result;
    }

    /**
     * Evaluates a polynomial.
     * @param vp polynomial
     * @param interpretation maps variables (Strings) to Rationals
     * @return Rational
     */
    public static PreciseRational evaluateVarPolynomial(final VarPolynomial vp,
        final Map<String, PreciseRational> interpretation) {
        PreciseRational result = new PreciseRational(BigInteger.ZERO);
        for (final Entry<IndefinitePart, SimplePolynomial> entry : vp.getVarMonomials().entrySet()) {
            final IndefinitePart indefPart = entry.getKey();
            final SimplePolynomial simplePart = entry.getValue();
            result =
                result.add(ToolBox.evaluateIndefinitePart(indefPart, interpretation).multiply(
                    ToolBox.evaluateSimplePolynomial(simplePart, interpretation)));
        }
        return result;
    }

    /**
     * Rewrites an indefinite part to a SMTLIBIntValue. Will replace non-linear
     * things by some alternative constructions.
     * @param indef indefinite part to rewrite
     * @param formulaList list of formulae to be completed
     * @param factory factory to build formulae
     * @param ng name generator
     * @return corresponding SMTLIBIntValue
     */
    static SMTLIBIntValue rewriteIndefinitePartToSMTLIBIntValueLinear(final IndefinitePart indef,
        final List<Formula<SMTLIBTheoryAtom>> formulaList,
        final FormulaFactory<SMTLIBTheoryAtom> factory,
        final FreshNameGenerator ng) {
        if (indef.isLinear()) {
            // The linear case is simple:
            return rewriteIndefinitePartToSMTLIBIntValue(indef);
        } else {
            // Generate constraints for being ZERO:
            final SMTLIBIntVariable resultVar = SMTLIBIntVariable.create(ng.getFreshName("r", false));
            final SMTLIBIntEquals resultIsZero = SMTLIBIntEquals.create(resultVar, SMT_INT_ZERO);
            final Formula<SMTLIBTheoryAtom> resultIsZeroFormula = factory.buildTheoryAtom(resultIsZero);

            Formula<SMTLIBTheoryAtom> oneExpoIsZero = null;

            for (final String exp : indef.getExponents().keySet()) {
                final SMTLIBIntVariable expVar = SMTLIBIntVariable.create(exp);
                final SMTLIBIntEquals expVarIsZero = SMTLIBIntEquals.create(expVar, SMT_INT_ZERO);
                final Formula<SMTLIBTheoryAtom> expVarIsZeroFormula = factory.buildTheoryAtom(expVarIsZero);

                // If one exponent is ZERO, then the whole thing is ZERO:
                formulaList.add(factory.buildImplication(expVarIsZeroFormula, resultIsZeroFormula));

                if (oneExpoIsZero == null) {
                    oneExpoIsZero = expVarIsZeroFormula;
                } else {
                    oneExpoIsZero = factory.buildOr(oneExpoIsZero, expVarIsZeroFormula);
                }
            }

            // If then whole thing is ZERO, then some exponents are ZERO:
            formulaList.add(factory.buildImplication(resultIsZeroFormula, oneExpoIsZero));

            // Generate constraints for GE/LE ZERO:
            SMTLIBIntVariable current = SMTLIBIntVariable.create(ng.getFreshName("h", false));
            final SMTLIBIntGE startValue = SMTLIBIntGE.create(current, SMT_INT_ZERO);
            formulaList.add(factory.buildTheoryAtom(startValue));

            // Every odd exponent has the possibility to flip the signum:
            for (final Entry<String, Integer> entry : indef.getExponents().entrySet()) {
                final Integer p = entry.getValue();
                if (p % 2 != 0) {
                    final String exp = entry.getKey();
                    final SMTLIBIntVariable expVar = SMTLIBIntVariable.create(exp);
                    final SMTLIBIntLE expVarLEZero = SMTLIBIntLE.create(expVar, SMT_INT_ZERO);
                    final Formula<SMTLIBTheoryAtom> expVarLEZeroFormula = factory.buildTheoryAtom(expVarLEZero);
                    final SMTLIBIntVariable next = SMTLIBIntVariable.create(ng.getFreshName("h", false));

                    final SMTLIBIntGE currentGEZero = SMTLIBIntGE.create(current, SMT_INT_ZERO);
                    final SMTLIBIntLE currentLEZero = SMTLIBIntLE.create(current, SMT_INT_ZERO);

                    final Formula<SMTLIBTheoryAtom> currentGEZeroFormula = factory.buildTheoryAtom(currentGEZero);
                    final Formula<SMTLIBTheoryAtom> currentLEZeroFormula = factory.buildTheoryAtom(currentLEZero);

                    final SMTLIBIntGE nextGEZero = SMTLIBIntGE.create(next, SMT_INT_ZERO);
                    final SMTLIBIntLE nextLEZero = SMTLIBIntLE.create(next, SMT_INT_ZERO);

                    final Formula<SMTLIBTheoryAtom> nextGEZeroFormula = factory.buildTheoryAtom(nextGEZero);
                    final Formula<SMTLIBTheoryAtom> nextLEZeroFormula = factory.buildTheoryAtom(nextLEZero);

                    formulaList.add(factory.buildImplication(
                        factory.buildAnd(expVarLEZeroFormula, currentGEZeroFormula), nextLEZeroFormula));
                    formulaList.add(factory.buildImplication(
                        factory.buildAnd(expVarLEZeroFormula, currentLEZeroFormula), nextGEZeroFormula));

                    current = next;
                }
            }

            final SMTLIBIntEquals currentEqResult = SMTLIBIntEquals.create(current, resultVar);
            formulaList.add(factory.buildTheoryAtom(currentEqResult));

            return resultVar;
        }
    }

    /**
     * Rewrites a VarPolynomial to a SMTLIBIntValue
     * @param vp VarPolynomial
     * @return SMTLIBIntValue
     */
    static SMTLIBIntValue rewriteVarPolynomialToSMTLIBIntValue(final VarPolynomial vp) {
        final LinkedList<SMTLIBIntValue> toAdd = new LinkedList<SMTLIBIntValue>();
        for (final Entry<IndefinitePart, SimplePolynomial> entry : vp.getVarMonomials().entrySet()) {
            final LinkedList<SMTLIBIntValue> toMultiply = new LinkedList<SMTLIBIntValue>();

            final IndefinitePart indefPart = entry.getKey();
            final SimplePolynomial simplePart = entry.getValue();

            if (!indefPart.equals(IndefinitePart.ONE)) {
                toMultiply.add(ToolBox.rewriteIndefinitePartToSMTLIBIntValue(indefPart));
            }
            if (simplePart.equals(SimplePolynomial.ZERO)) {
                break;
            } else if (!simplePart.equals(SimplePolynomial.ONE)) {
                toMultiply.add(ToolBox.rewriteSimplePolynomialToSMTLIBIntValue(simplePart));
            }

            switch (toMultiply.size()) {
            case 0:
                toAdd.add(SMTLIBIntConstant.create(BigInteger.ONE));
                break;
            case 1:
                toAdd.add(toMultiply.getFirst());
                break;
            default:
                toAdd.add(SMTLIBIntMult.create(toMultiply));
            }
        }

        switch (toAdd.size()) {
        case 0:
            return SMTLIBIntConstant.create(BigInteger.ZERO);
        case 1:
            return toAdd.getFirst();
        default:
            return SMTLIBIntPlus.create(toAdd);
        }
    }

    /**
     * Rewrites a VarPolynomial to a SMTLIBIntValue. Will replace non-linear
     * multiplications by fresh variables. Furthermore we generate some basic
     * constraint for these new variables. Former part will only work correctly
     * if the given polynomial is concrete. Therefore this function will crash
     * if you do such bad things.
     * @param vp VarPolynomial
     * @param formulaList list of atoms
     * @param factory builds formulae
     * @param ng name generator
     * @return SMTLIBIntValue
     */
    static SMTLIBIntValue rewriteVarPolynomialToSMTLIBIntValueLinear(final VarPolynomial vp,
        final List<Formula<SMTLIBTheoryAtom>> formulaList,
        final FormulaFactory<SMTLIBTheoryAtom> factory,
        final FreshNameGenerator ng) {
        assert vp.isConcrete() : "Polynomial must be concrete here!";

        final LinkedList<SMTLIBIntValue> toAdd = new LinkedList<SMTLIBIntValue>();
        for (final Entry<IndefinitePart, SimplePolynomial> entry : vp.getVarMonomials().entrySet()) {
            final LinkedList<SMTLIBIntValue> toMultiply = new LinkedList<SMTLIBIntValue>();

            // Since we assume the polynomial to be concrete, we only have to look
            // closer at the indefPart, but the simplePart will only be a constant.
            final IndefinitePart indefPart = entry.getKey();
            final SimplePolynomial simplePart = entry.getValue();

            if (!indefPart.equals(IndefinitePart.ONE)) {
                // Please note, that rewriteIndefinitePartToSMTLIBIntValueLinear is different than
                // rewriteIndefinitePartToSMTLIBIntValue !!
                toMultiply.add(ToolBox.rewriteIndefinitePartToSMTLIBIntValueLinear(indefPart, formulaList, factory, ng));
            }
            if (simplePart.equals(SimplePolynomial.ZERO)) {
                break;
            } else if (!simplePart.equals(SimplePolynomial.ONE)) {
                toMultiply.add(ToolBox.rewriteSimplePolynomialToSMTLIBIntValue(simplePart));
            }

            switch (toMultiply.size()) {
            case 0:
                toAdd.add(SMTLIBIntConstant.create(BigInteger.ONE));
                break;
            case 1:
                toAdd.add(toMultiply.getFirst());
                break;
            default:
                toAdd.add(SMTLIBIntMult.create(toMultiply));
            }
        }

        switch (toAdd.size()) {
        case 0:
            return SMTLIBIntConstant.create(BigInteger.ZERO);
        case 1:
            return toAdd.getFirst();
        default:
            return SMTLIBIntPlus.create(toAdd);
        }
    }

    /**
     * Rewrites a polynomial into a SMTLIBRatValue.
     * @param vp some polynomial
     * @return some SMTLIBRatValue
     */
    public static SMTLIBRatValue rewriteVarPolynomalIntoSMTLIBRatValue(final VarPolynomial vp) {
        SMTLIBRatValue v = null;
        for (final Entry<IndefinitePart, SimplePolynomial> e : vp.getVarMonomials().entrySet()) {
            final IndefinitePart indef = e.getKey();
            final SimplePolynomial simple = e.getValue();
            final SMTLIBRatValue smtIndef = ToolBox.rewriteIndefinitePartToSMTLIBRatValue(indef);
            final SMTLIBRatValue smtSimple = ToolBox.rewriteSimplePolynomialToSMTLIBRatValue(simple);
            final LinkedList<SMTLIBRatValue> paraList = new LinkedList<>();
            paraList.add(smtSimple);
            paraList.add(smtIndef);
            final SMTLIBRatMult factor = SMTLIBRatMult.create(paraList);

            if (v != null) {
                final LinkedList<SMTLIBRatValue> paraList2 = new LinkedList<>();
                paraList2.add(v);
                paraList2.add(factor);
                v = SMTLIBRatPlus.create(paraList2);
            } else {
                v = factor;
            }
        }
        v = v == null ? SMTLIBRatConstant.create(BigInteger.ZERO) : v;
        return v;
    }

    /**
     * Rewrites a SimplePolynomial to a SMTLIBRatValue
     * @param simple SimplePolynomial
     * @return SMTLIBRatValue
     */
    public static SMTLIBRatValue rewriteSimplePolynomialToSMTLIBRatValue(final SimplePolynomial simple) {
        final ImmutableMap<IndefinitePart, BigInteger> simpleMonomials = simple.getSimpleMonomials();
        final Set<Entry<IndefinitePart, BigInteger>> entrySet = simpleMonomials.entrySet();
        final LinkedList<SMTLIBRatValue> toAdd = new LinkedList<SMTLIBRatValue>();
        for (final Entry<IndefinitePart, BigInteger> entry : entrySet) {
            final IndefinitePart indef = entry.getKey();
            final BigInteger factor = entry.getValue();
            if (factor.equals(BigInteger.ZERO)) {
                continue;
            }

            if (indef.isEmpty()) {
                toAdd.add(SMTLIBRatConstant.create(factor));
            } else {
                final LinkedList<SMTLIBRatValue> args = new LinkedList<SMTLIBRatValue>();
                if (!factor.equals(BigInteger.ONE)) {
                    args.add(SMTLIBRatConstant.create(factor));
                }
                args.add(ToolBox.rewriteIndefinitePartToSMTLIBRatValue(indef));
                if (args.size() == 1) {
                    toAdd.add(args.get(0));
                } else {
                    toAdd.add(SMTLIBRatMult.create(args));
                }
            }
        }

        if (toAdd.isEmpty()) {
            return SMTLIBRatConstant.create(BigInteger.ZERO);
        } else {
            return SMTLIBRatPlus.create(toAdd);
        }
    }

    /**
     * Rewrites a SimplePolynomial to a SMTLIBIntValue
     * @param simple SimplePolynomial
     * @return SMTLIBIntValue
     */
    public static SMTLIBIntValue rewriteSimplePolynomialToSMTLIBIntValue(final SimplePolynomial simple) {
        final ImmutableMap<IndefinitePart, BigInteger> simpleMonomials = simple.getSimpleMonomials();
        final Set<Entry<IndefinitePart, BigInteger>> entrySet = simpleMonomials.entrySet();
        final LinkedList<SMTLIBIntValue> toAdd = new LinkedList<SMTLIBIntValue>();
        for (final Entry<IndefinitePart, BigInteger> entry : entrySet) {
            final IndefinitePart indef = entry.getKey();
            final BigInteger factor = entry.getValue();
            if (factor.equals(BigInteger.ZERO)) {
                continue;
            }

            if (indef.isEmpty()) {
                toAdd.add(SMTLIBIntConstant.create(factor));
            } else {
                final LinkedList<SMTLIBIntValue> args = new LinkedList<SMTLIBIntValue>();
                if (!factor.equals(BigInteger.ONE)) {
                    args.add(SMTLIBIntConstant.create(factor));
                }
                args.add(ToolBox.rewriteIndefinitePartToSMTLIBIntValue(indef));
                if (args.size() == 1) {
                    toAdd.add(args.get(0));
                } else {
                    toAdd.add(SMTLIBIntMult.create(args));
                }
            }
        }

        if (toAdd.isEmpty()) {
            return SMTLIBIntConstant.create(BigInteger.ZERO);
        } else {
            return SMTLIBIntPlus.create(toAdd);
        }
    }

    /**
     * Return the indefinite part with maximal degree.
     * @param varPolynomial a var polynomial
     * @return IndefinitePart
     */
    static IndefinitePart getStrongestMonomial(final VarPolynomial varPolynomial) {
        IndefinitePart result = null;

        final Set<IndefinitePart> candidates = varPolynomial.getVarMonomials().keySet();
        for (final IndefinitePart candidate : candidates) {
            if (result == null) {
                result = candidate;
            } else {
                if (candidate.getDegree() > result.getDegree()) {
                    result = candidate;
                }
            }
        }

        return result;
    }

    /**
     * Parses a rational from a string.
     * @param str a string
     * @return Rational
     */
    public static Rational parseRational(final String str) {
        final Rational r;
        if (str.indexOf('/') == (-1)) {
            final Integer i = Integer.parseInt(str);
            r = new Rational(i);
        } else {
            final int index = str.indexOf('/');
            final int numerator = Integer.parseInt(str.substring(0, index));
            final int denominator = Integer.parseInt(str.substring(index + 1, str.length()));
            r = new Rational(numerator, denominator);
        }
        return r;
    }

    /**
     * Parses a rational model. This is useful to "understand" the answer the
     * SMT-Solver gave you.
     * @param rawInterpretation maps Strings to Strings (the later encode the
     * rationals)
     * @return mapping from String to Rationals
     */
    public static Map<String, PreciseRational> parseRationalInterpretation(final Map<String, String> rawInterpretation) {
        final LinkedHashMap<String, PreciseRational> result = new LinkedHashMap<>(rawInterpretation.size());
        for (final Entry<String, String> e : rawInterpretation.entrySet()) {
            result.put(e.getKey(), PreciseRational.parseRational(e.getValue()));
        }
        return result;
    }

    /**
     * Rewrites an exponent to a SMTLIBIntValue.
     * @param x string
     * @param power integer
     * @return SMTLIBIntValue
     */
    static SMTLIBIntValue rewriteExponentToSMTLIBIntValue(final String x, final int power) {
        if (power == 0) {
            return SMTLIBIntConstant.create(BigInteger.ONE);
        } else if (power == 1) {
            return SMTLIBIntVariable.create(x);
        } else {
            final SMTLIBIntVariable v = SMTLIBIntVariable.create(x);
            final LinkedList<SMTLIBIntValue> toMultiply = new LinkedList<SMTLIBIntValue>();
            for (int i = 0; i < power; i++) {
                toMultiply.add(v);
            }
            return SMTLIBIntMult.create(toMultiply);
        }
    }

    /**
     * Rewrites an exponent to a SMTLIBRatValue.
     * @param x string
     * @param power integer
     * @return SMTLIBRatValue
     */
    static SMTLIBRatValue rewriteExponentToSMTLIBRatValue(final String x, final int power) {
        if (power == 0) {
            return SMTLIBRatConstant.create(BigInteger.ONE);
        } else if (power == 1) {
            return SMTLIBRatVariable.create(x);
        } else {
            final SMTLIBRatVariable v = SMTLIBRatVariable.create(x);
            final LinkedList<SMTLIBRatValue> toMultiply = new LinkedList<SMTLIBRatValue>();
            for (int i = 0; i < power; i++) {
                toMultiply.add(v);
            }
            return SMTLIBRatMult.create(toMultiply);
        }
    }

    /**
     * Renames the variables occurring in the given rule. This will also replace
     * a null condition term by TRUE, because I don't like null.
     * @param toRename rule to be renamed
     * @param ng a name generator
     * @return IGeneralizedRule
     */
    public static IGeneralizedRule renameVariablesInRule(final IGeneralizedRule toRename, final FreshNameGenerator ng) {
        final TRSFunctionApplication left = toRename.getLeft();
        final TRSTerm right = toRename.getRight();
        final TRSTerm condition = toRename.getCondTerm();

        final LinkedHashSet<TRSVariable> occuringVariables = new LinkedHashSet<TRSVariable>();
        occuringVariables.addAll(left.getVariables());
        occuringVariables.addAll(right.getVariables());
        if (condition != null) {
            occuringVariables.addAll(condition.getVariables());
        }

        final LinkedHashMap<TRSVariable, TRSVariable> newNamesMap =
            new LinkedHashMap<TRSVariable, TRSVariable>(occuringVariables.size());
        for (final TRSVariable oldVar : occuringVariables) {
            final TRSVariable newVar = TRSTerm.createVariable(ng.getFreshName("x", false));
            newNamesMap.put(oldVar, newVar);
        }

        final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(newNamesMap));

        final TRSFunctionApplication newLeft = left.applySubstitution(sigma);
        final TRSTerm newRight = right.applySubstitution(sigma);
        final TRSTerm newCondition =
            condition != null ? condition.applySubstitution(sigma) : ToolBox.PREDEFINED.getBooleanTrue().getTerm();
            final IGeneralizedRule resultRule = IGeneralizedRule.create(newLeft, newRight, newCondition);

            return resultRule;
    }

    /**
     * Moves constants from the left side into the condition.
     */
    public static IGeneralizedRule moveConstantsToCondition(final IGeneralizedRule rule, final FreshNameGenerator ng) {
        final TRSFunctionApplication leftSide = rule.getLeft();
        TRSTerm condition = rule.getCondTerm();
        condition = condition == null ? ToolBox.buildTrue() : condition;

        final Pair<TRSTerm, TRSTerm> p = ToolBox.eliminatePredefinedConstants(leftSide, condition, ng);
        assert p.x instanceof TRSFunctionApplication : "Excepted function application!";

        return IGeneralizedRule.create((TRSFunctionApplication) p.x, rule.getRight(), p.y);
    }

    public static Pair<TRSTerm, TRSTerm> eliminatePredefinedConstants(final TRSTerm term,
        final TRSTerm cond,
        final FreshNameGenerator ng) {
        if (term instanceof TRSVariable) {
            return new Pair<TRSTerm, TRSTerm>(term, cond);
        } else if (term instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) term;
            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(func.getRootSymbol())) {
                final TRSVariable v = TRSTerm.createVariable(ng.getFreshName("c", false));
                final TRSTerm newCond = ToolBox.buildAnd(cond, ToolBox.buildEq(v, func));
                return new Pair<TRSTerm, TRSTerm>(v, newCond);
            } else {
                final ArrayList<TRSTerm> newArgs = new ArrayList<>();
                TRSTerm currentCond = cond;
                for (final TRSTerm currentArg : func.getArguments()) {
                    final Pair<TRSTerm, TRSTerm> p = ToolBox.eliminatePredefinedConstants(currentArg, currentCond, ng);
                    newArgs.add(p.x);
                    currentCond = p.y;
                }
                return new Pair<TRSTerm, TRSTerm>(
                    TRSTerm.createFunctionApplication(func.getRootSymbol(), newArgs), currentCond);
            }
        } else {
            assert false : "Strange term!";
        return null;
        }
    }

    public static BigInteger max(final Collection<BigInteger> numbers) {
        BigInteger result = null;
        for (final BigInteger x : numbers) {
            if (result == null || result.compareTo(x) < 0) {
                result = x;
            }
        }
        return result;
    }


}
