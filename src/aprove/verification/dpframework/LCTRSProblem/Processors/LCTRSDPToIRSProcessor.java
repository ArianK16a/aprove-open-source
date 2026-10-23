package aprove.verification.dpframework.LCTRSProblem.Processors;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.LCTRSProblem.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Converts a dependency pair problem of an LCTRS into an integer rewrite system (IRS) by projecting
 * the pairs onto the sorts Int and Bool (Kulmer, Integer Term Rewriting via Projections): all arguments of
 * other sorts are removed, Booleans become the integers 1 (true) and 0 (false), and the guard of a pair
 * becomes the condition of the IRS rule.
 *
 * <p>The conversion is only correct for <em>innermost</em> chains, since it needs that the terms along a
 * chain are normal forms. So the processor is only applicable if the rules of the problem satisfy a
 * criterion under which innermost and full termination coincide. The criterion is: the rules are an
 * <em>overlay</em> system (no overlaps below the root), and
 * <ul>
 * <li>every rule is right-linear except for variables of its guard, and no variable occurs only in the
 * right-hand side, or</li>
 * <li>there are no critical pairs, i.e., the guards of two rules with unifiable left-hand sides are
 * contradictory.</li>
 * </ul>
 * </p>
 *
 * <p>The criterion is checked for the rules R of the problem, and the argument is: if the LCTRS is not
 * terminating, then it is not innermost terminating, so there is an infinite innermost chain of its
 * dependency pairs. Hence the processor must only be used on problems that were obtained from the
 * dependency pairs of R by processors that keep infinite innermost chains, such as the dependency graph,
 * and not after the sort projection, which does not keep them.</p>
 *
 * <p>It fails if a theory other than Core and Ints is used, or if a kept argument of the right-hand side
 * of a pair contains a term symbol (then the rules of the problem would be needed).</p>
 */
public class LCTRSDPToIRSProcessor extends Processor.ProcessorSkeleton {

    public static class Arguments {

        /** The time limit of the SMT solver for one check of two guards in milliseconds. */
        public int guardTimeout = 500;

        public void setGuardTimeout(final int guardTimeout) {
            this.guardTimeout = guardTimeout;
        }

    }

    private final Arguments arguments;

    @ParamsViaArgumentObject
    public LCTRSDPToIRSProcessor(final Arguments arguments) {
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
        for (final LCTRSTheory theory : signature.theories()) {
            if (theory != LCTRSTheory.CORE && theory != LCTRSTheory.INTS) {
                return ResultFactory.unsuccessful("Only the theories Core and Ints are supported.");
            }
        }
        final String criterion = this.checkCriterion(dp, aborter);
        if (!criterion.startsWith("overlay")) {
            return ResultFactory.unsuccessful(criterion);
        }

        final LCTRSToITRSProcessor.Converter converter = new LCTRSToITRSProcessor.Converter(signature);
        final Set<String> usedNames = new LinkedHashSet<>();
        for (final LCTRSRule pair : dp.getP()) {
            pair.left().getFunctionSymbols().forEach(f -> usedNames.add(f.getName()));
            pair.right().getFunctionSymbols().forEach(f -> usedNames.add(f.getName()));
            pair.left().getVariables().forEach(x -> usedNames.add(x.getName()));
            pair.right().getVariables().forEach(x -> usedNames.add(x.getName()));
            pair.guard().getVariables().forEach(x -> usedNames.add(x.getName()));
        }
        final FreshNameGenerator names = new FreshNameGenerator(usedNames, FreshNameGenerator.APPEND_NUMBERS);
        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        final Set<IGeneralizedRule> rules = new LinkedHashSet<>();
        try {
            for (final LCTRSRule pair : dp.getP()) {
                aborter.checkAbortion();
                final List<TRSTerm> leftArgs = new ArrayList<>();
                final List<TRSTerm> rightArgs = new ArrayList<>();
                TRSTerm condition = pair.hasGuard() ? this.formula(pair.guard(), converter, signature) : null;
                final Set<TRSVariable> seen = new LinkedHashSet<>();
                final LCTRSSortDeclaration leftDeclaration = signature.getDeclaration(pair.left().getRootSymbol());
                final LCTRSSortDeclaration rightDeclaration =
                    signature.getDeclaration(((TRSFunctionApplication) pair.right()).getRootSymbol());
                for (int i = 0; i < leftDeclaration.arity(); i++) {
                    final LCTRSSort sort = leftDeclaration.argumentSorts().get(i);
                    if (!sort.isTheorySort()) {
                        continue;
                    }
                    if (!LCTRSSort.INT.equals(sort) && !LCTRSSort.BOOL.equals(sort)) {
                        return ResultFactory.unsuccessful("The sort " + sort + " is not supported.");
                    }
                    final TRSTerm arg = pair.left().getArgument(i);
                    if (arg.isVariable() && seen.add((TRSVariable) arg)) {
                        leftArgs.add(arg);
                    } else {
                        // a value or a repeated variable: use a fresh variable and an equation
                        final TRSVariable fresh = TRSTerm.createVariable(names.getFreshName("v", false));
                        leftArgs.add(fresh);
                        final TRSTerm equation =
                            converter.apply(Func.Eq, DomainFactory.INTEGERS, fresh, this.number(arg, converter, signature));
                        condition = condition == null ? equation : converter.bool(Func.Land, condition, equation);
                    }
                }
                final TRSFunctionApplication right = (TRSFunctionApplication) pair.right();
                for (int i = 0; i < rightDeclaration.arity(); i++) {
                    final LCTRSSort sort = rightDeclaration.argumentSorts().get(i);
                    if (!sort.isTheorySort()) {
                        continue;
                    }
                    if (!LCTRSSort.INT.equals(sort) && !LCTRSSort.BOOL.equals(sort)) {
                        return ResultFactory.unsuccessful("The sort " + sort + " is not supported.");
                    }
                    final TRSTerm arg = right.getArgument(i);
                    if (!signature.isLogicalTerm(arg)) {
                        return ResultFactory.unsuccessful(
                            "The argument " + arg + " of " + pair + " contains a symbol that is not a theory symbol.");
                    }
                    if (LCTRSSort.BOOL.equals(sort) && !arg.isVariable() && !signature.isValue(((TRSFunctionApplication) arg).getRootSymbol())) {
                        // a Boolean expression: a fresh variable that is 1 iff the expression holds
                        final TRSVariable fresh = TRSTerm.createVariable(names.getFreshName("b", false));
                        final TRSTerm holds = this.formula(arg, converter, signature);
                        final TRSTerm one = converter.apply(Func.Eq, DomainFactory.INTEGERS, fresh, this.number(LCTRSRule.TRUE, converter, signature));
                        final TRSTerm zero = converter.apply(Func.Eq, DomainFactory.INTEGERS, fresh, this.number(FALSE, converter, signature));
                        final TRSTerm definition =
                            converter.bool(
                                Func.Lor,
                                converter.bool(Func.Land, holds, one),
                                converter.bool(Func.Land, converter.bool(Func.Lnot, holds), zero));
                        condition = condition == null ? definition : converter.bool(Func.Land, condition, definition);
                        rightArgs.add(fresh);
                    } else {
                        rightArgs.add(this.number(arg, converter, signature));
                    }
                }
                final FunctionSymbol leftSymbol = FunctionSymbol.create(pair.left().getRootSymbol().getName(), leftArgs.size());
                final FunctionSymbol rightSymbol = FunctionSymbol.create(right.getRootSymbol().getName(), rightArgs.size());
                final TRSFunctionApplication newLeft = TRSTerm.createFunctionApplication(leftSymbol, leftArgs);
                final TRSFunctionApplication newRight = TRSTerm.createFunctionApplication(rightSymbol, rightArgs);
                final TRSFunctionApplication condFA =
                    (TRSFunctionApplication) (condition == null
                        ? predefinedMap.getBooleanTrue().getTerm()
                        : condition);
                final TRSTerm killedNot = IRSwTFormatTransformer.killNOT(condFA, predefinedMap);
                final Set<TRSTerm> conditions =
                    killedNot.isVariable()
                        ? Collections.singleton(killedNot)
                        : IRSwTFormatTransformer.killOR(
                            IRSwTFormatTransformer.killNE((TRSFunctionApplication) killedNot, predefinedMap),
                            predefinedMap);
                for (final TRSTerm cond : conditions) {
                    rules.add(IGeneralizedRule.create(newLeft, newRight, cond));
                }
            }
        } catch (final LCTRSToITRSProcessor.UnsupportedSymbolException e) {
            return ResultFactory.unsuccessful(e.getMessage());
        }
        if (rules.isEmpty()) {
            return ResultFactory.proved(new LCTRSDPToIRSProof(criterion, rules));
        }
        return ResultFactory.proved(
            new IRSProblem(ImmutableCreator.create(rules)),
            YNMImplication.SOUND,
            new LCTRSDPToIRSProof(criterion, rules));
    }

    private static final TRSFunctionApplication FALSE = TRSTerm.createFunctionApplication(FunctionSymbol.create("false", 0));

    /**
     * @return a variable or value of the sort Int or Bool as an integer term (Booleans are 1 and 0)
     */
    private TRSTerm number(final TRSTerm term, final LCTRSToITRSProcessor.Converter converter, final LCTRSSignature signature)
        throws LCTRSToITRSProcessor.UnsupportedSymbolException
    {
        if (!term.isVariable() && LCTRSSort.BOOL.equals(signature.getValueSort(((TRSFunctionApplication) term).getRootSymbol()))) {
            // built directly, as 1 and 0 are no values of the signature if the theory Ints is not used
            final boolean value = ((TRSFunctionApplication) term).getRootSymbol().getName().equals("true");
            return PredefinedSemanticsFactory.getIntTerm(
                BigIntImmutable.create(value ? BigInteger.ONE : BigInteger.ZERO),
                DomainFactory.INTEGERS);
        }
        return term.isVariable() ? term : converter.convert(term);
    }

    /**
     * @return the Boolean term of the IRS for the logical term of sort Bool; a variable b of sort Bool is
     * an integer variable that is regarded as true iff it is 1
     */
    private TRSTerm formula(final TRSTerm term, final LCTRSToITRSProcessor.Converter converter, final LCTRSSignature signature)
        throws LCTRSToITRSProcessor.UnsupportedSymbolException
    {
        if (term.isVariable()) {
            return converter.apply(Func.Eq, DomainFactory.INTEGERS, term, this.number(LCTRSRule.TRUE, converter, signature));
        }
        final TRSFunctionApplication app = (TRSFunctionApplication) term;
        final FunctionSymbol f = app.getRootSymbol();
        if (signature.isValue(f)) {
            return converter.convert(term);
        }
        final LCTRSTheorySymbol symbol = signature.theorySymbols().get(f);
        final boolean booleanArguments =
            symbol != null && f.getArity() > 0 && LCTRSSort.BOOL.equals(symbol.declaration().argumentSorts().get(0));
        if (!booleanArguments) {
            return converter.convert(term);
        }
        final TRSTerm[] args = new TRSTerm[f.getArity()];
        for (int i = 0; i < args.length; i++) {
            args[i] = this.formula(app.getArgument(i), converter, signature);
        }
        switch (symbol.name() + "/" + f.getArity()) {
        case "not/1":
            return converter.bool(Func.Lnot, args[0]);
        case "and/2":
            return converter.bool(Func.Land, args[0], args[1]);
        case "or/2":
            return converter.bool(Func.Lor, args[0], args[1]);
        case "=>/2":
            return converter.bool(Func.Lor, converter.bool(Func.Lnot, args[0]), args[1]);
        case "=/2":
        case "xor/2":
        case "distinct/2": {
            final TRSTerm same =
                converter.bool(
                    Func.Lor,
                    converter.bool(Func.Land, args[0], args[1]),
                    converter.bool(Func.Land, converter.bool(Func.Lnot, args[0]), converter.bool(Func.Lnot, args[1])));
            return symbol.name().equals("=") ? same : converter.bool(Func.Lnot, same);
        }
        default:
            throw new LCTRSToITRSProcessor.UnsupportedSymbolException(f);
        }
    }

    // ===================================== THE CRITERION =====================================

    /**
     * @return a description starting with "overlay" if the criterion holds, and a reason why it does not hold
     * otherwise
     */
    private String checkCriterion(final LCTRSDPProblem dp, final Abortion aborter) throws AbortionException {
        final LCTRSSignature signature = dp.getSignature();
        final List<LCTRSRule> rules = dp.getR();
        for (final LCTRSRule rule : rules) {
            if (!signature.isTermSymbol(rule.left().getRootSymbol())) {
                return "The left-hand side of " + rule + " has a theory symbol at the root.";
            }
        }
        // renaming apart: the variables of the second rule get a suffix
        final List<LCTRSRule> renamed = new ArrayList<>();
        for (final LCTRSRule rule : rules) {
            renamed.add(LCTRSDPToIRSProcessor.rename(rule));
        }
        // overlay: no left-hand side unifies with a non-variable proper subterm of a left-hand side
        for (final LCTRSRule rule : rules) {
            for (final LCTRSRule other : renamed) {
                aborter.checkAbortion();
                for (final Pair<Position, TRSFunctionApplication> sub
                    : rule.left().getNonRootNonVariablePositionsWithSubTerms())
                {
                    if (sub.y.getMGU(other.left()) != null) {
                        return "The rules are no overlay system: " + rule + " has an overlap below the root with " + other + ".";
                    }
                }
            }
        }
        // right-linear except for guard variables, no variable only on the right
        String linear = null;
        for (final LCTRSRule rule : rules) {
            final Map<TRSVariable, Integer> occurrences = new LinkedHashMap<>();
            LCTRSDPToIRSProcessor.count(rule.right(), occurrences);
            for (final Map.Entry<TRSVariable, Integer> entry : occurrences.entrySet()) {
                if (!rule.left().getVariables().contains(entry.getKey())) {
                    linear = "the variable " + entry.getKey().getName() + " occurs only in the right-hand side of " + rule;
                    break;
                }
                if (entry.getValue() > 1 && !rule.guard().getVariables().contains(entry.getKey())) {
                    linear = "the variable " + entry.getKey().getName() + " occurs more than once in the right-hand side of " + rule
                        + " and not in its guard";
                    break;
                }
            }
            if (linear != null) {
                break;
            }
        }
        if (linear == null) {
            return "overlay and right-linear except for the variables of the guards";
        }
        // no critical pairs
        final LCTRSSmt smt = new LCTRSSmt(signature, this.arguments.guardTimeout);
        for (int i = 0; i < rules.size(); i++) {
            for (int j = i + 1; j < rules.size(); j++) {
                aborter.checkAbortion();
                final LCTRSRule first = rules.get(i);
                final LCTRSRule second = renamed.get(j);
                final TRSSubstitution mgu = first.left().getMGU(second.left());
                if (mgu == null) {
                    continue;
                }
                final Map<TRSVariable, LCTRSSort> sorts = new LinkedHashMap<>(first.variableSorts());
                sorts.putAll(second.variableSorts());
                final LCTRSSmt.Formula formula = smt.new Formula();
                formula.add(first.guard().applySubstitution(mgu), sorts, "");
                formula.add(second.guard().applySubstitution(mgu), sorts, "");
                if (!formula.isUnsatisfiable(aborter)) {
                    return "Not applicable, as " + linear + ", and the rules " + first + " and " + rules.get(j)
                        + " form a critical pair.";
                }
            }
        }
        return "overlay and no critical pairs (right-linearity fails: " + linear + ")";
    }

    private static LCTRSRule rename(final LCTRSRule rule) {
        final Map<TRSVariable, TRSVariable> map = new LinkedHashMap<>();
        final Map<TRSVariable, LCTRSSort> sorts = new LinkedHashMap<>();
        final Set<TRSVariable> all = new LinkedHashSet<>(rule.left().getVariables());
        all.addAll(rule.right().getVariables());
        all.addAll(rule.guard().getVariables());
        for (final TRSVariable x : all) {
            final TRSVariable y = TRSTerm.createVariable(x.getName() + "'");
            map.put(x, y);
            if (rule.variableSorts().containsKey(x)) {
                sorts.put(y, rule.variableSorts().get(x));
            }
        }
        return new LCTRSRule(
            rule.left().renameVariables(map),
            rule.right().renameVariables(map),
            rule.guard().renameVariables(map),
            sorts);
    }

    private static void count(final TRSTerm term, final Map<TRSVariable, Integer> occurrences) {
        if (term.isVariable()) {
            occurrences.merge((TRSVariable) term, 1, Integer::sum);
        } else {
            for (final TRSTerm arg : ((TRSFunctionApplication) term).getArguments()) {
                LCTRSDPToIRSProcessor.count(arg, occurrences);
            }
        }
    }

    /**
     * The proof of the conversion.
     */
    private static class LCTRSDPToIRSProof extends Proof.DefaultProof {

        private final String criterion;

        private final Set<IGeneralizedRule> rules;

        private LCTRSDPToIRSProof(final String criterion, final Set<IGeneralizedRule> rules) {
            this.criterion = criterion;
            this.rules = rules;
            this.setShortName("LCTRSDPToIRSProof");
            this.setLongName("LCTRS Dependency Pairs to IRS");
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append("Projected the dependency pairs onto the sort Int: the arguments of other sorts are removed ");
            res.append("and the guards become conditions. IRSs are evaluated innermost, which is no restriction ");
            res.append("here as the rules satisfy the criterion: ").append(o.escape(this.criterion)).append(".");
            res.append(o.linebreak()).append("The resulting IRS has ").append(this.rules.size()).append(" rules:");
            for (final IGeneralizedRule rule : this.rules) {
                res.append(o.linebreak()).append(o.escape(rule.toString()));
            }
            return res.toString();
        }

    }

}
