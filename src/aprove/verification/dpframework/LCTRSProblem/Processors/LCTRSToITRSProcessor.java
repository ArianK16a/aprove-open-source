package aprove.verification.dpframework.LCTRSProblem.Processors;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
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
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Converts an LCTRS over the integers into an ITRS by dropping the sorts.
 *
 * <p>The theory symbols of Core and Ints become the pre-defined symbols of the ITRS, the guard of a rule
 * becomes its condition (which is then encoded as usual for ITRSs), and user-defined theory symbols
 * (<code>define-fun</code>) are replaced by their bodies.</p>
 *
 * <p>This is a first, simple version with the following restrictions:</p>
 * <ul>
 * <li>An ITRS is evaluated innermost, so termination of the ITRS only shows <em>innermost</em> termination
 * of the LCTRS. No criterion is checked under which this implies termination.</li>
 * <li>The ITRS has more terms than the LCTRS, as it is unsorted. So only termination carries over
 * ({@link YNMImplication#SOUND}), and an entrypoint is ignored.</li>
 * <li>The processor fails for other theories than Core and Ints, for the theory symbols without
 * counterpart in ITRSs (<code>div</code> and <code>mod</code> round differently there; <code>abs</code>,
 * <code>ite</code>, <code>divisible</code>), for rules whose left-hand side contains a theory symbol that
 * is no value, and for rules whose left-hand side contains a defined symbol below the root. The latter
 * are excluded since the encoding of the conditions rewrites a term <code>f(...)</code> to a term
 * <code>Cond_f(...)</code> even if no rule of the LCTRS is applicable, so such a left-hand side could not
 * match anymore.</li>
 * </ul>
 */
public class LCTRSToITRSProcessor extends Processor.ProcessorSkeleton {

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof LCTRSProblem;
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        final LCTRSProblem lctrs = (LCTRSProblem) obl;
        for (final LCTRSTheory theory : lctrs.getSignature().theories()) {
            if (theory != LCTRSTheory.CORE && theory != LCTRSTheory.INTS) {
                return ResultFactory.unsuccessful(
                    "ITRSs only have Booleans and integers, but the LCTRS uses the theory " + theory.getSmtName()
                        + ".");
            }
        }
        final Set<FunctionSymbol> defined = lctrs.getDefinedSymbols();
        for (final LCTRSRule rule : lctrs.getRules()) {
            if (!lctrs.isStandard(rule)) {
                return ResultFactory.unsuccessful("The left-hand side of " + rule + " contains a theory symbol.");
            }
            for (final TRSTerm arg : rule.left().getArguments()) {
                if (!Collections.disjoint(arg.getFunctionSymbols(), defined)) {
                    return ResultFactory.unsuccessful(
                        "The left-hand side of " + rule + " contains a defined symbol below the root.");
                }
            }
        }
        final Converter converter = new Converter(lctrs);
        final Set<IGeneralizedRule> conditionalRules = new LinkedHashSet<>();
        try {
            for (final LCTRSRule rule : lctrs.getRules()) {
                aborter.checkAbortion();
                conditionalRules.add(converter.convert(rule));
            }
        } catch (final UnsupportedSymbolException e) {
            return ResultFactory.unsuccessful(e.getMessage());
        }
        final Set<GeneralizedRule> rules = IGeneralizedRule.removeConditions(conditionalRules, true);
        final Collection<String> usedNames = new LinkedHashSet<>();
        for (final GeneralizedRule rule : rules) {
            for (final FunctionSymbol f : rule.getFunctionSymbols()) {
                usedNames.add(f.getName());
            }
        }
        final IDPPredefinedMap predefinedMap =
            new IDPPredefinedMap(ImmutableCreator.create(converter.predefined), usedNames);
        final RuleAnalysis<GeneralizedRule> ruleAnalysis =
            new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(rules), predefinedMap);
        final IQTermSet q = new IQTermSet(new QTermSet(ruleAnalysis.getLeftHandSides()), predefinedMap);
        return ResultFactory.proved(
            ITRSProblem.create(ruleAnalysis, q),
            YNMImplication.SOUND,
            new LCTRSToITRSProof(converter.renaming, lctrs.getEntrypoint()));
    }

    /**
     * Thrown for a theory symbol that has no counterpart in ITRSs.
     */
    private static class UnsupportedSymbolException extends Exception {

        private static final long serialVersionUID = 1L;

        private UnsupportedSymbolException(final FunctionSymbol f) {
            super("The theory symbol " + f.getName() + " with " + f.getArity() + " arguments is not supported.");
        }

    }

    /**
     * Converts the terms and rules of one LCTRS and collects the pre-defined symbols that are used.
     */
    private static class Converter {

        /** The theory symbols with a direct counterpart on the Booleans, by <code>name/arity</code>. */
        private static final Map<String, Func> BOOLEAN =
            Map.of("not/1", Func.Lnot, "and/2", Func.Land, "or/2", Func.Lor);

        /** The theory symbols with a direct counterpart on the integers, by <code>name/arity</code>. */
        private static final Map<String, Func> INTEGER =
            Map.of(
                "-/1", Func.UnaryMinus, "+/2", Func.Add, "-/2", Func.Sub, "*/2", Func.Mul,
                "<=/2", Func.Le, "</2", Func.Lt, ">=/2", Func.Ge, ">/2", Func.Gt);

        private final LCTRSSignature signature;

        /** The pre-defined function symbols that occur in the converted terms, with their semantics. */
        private final Map<FunctionSymbol, PredefinedFunction<? extends Domain>> predefined = new LinkedHashMap<>();

        /** The term symbols that are renamed since their name is used by a pre-defined symbol. */
        private final Map<FunctionSymbol, FunctionSymbol> renaming = new LinkedHashMap<>();

        private Converter(final LCTRSProblem lctrs) {
            this.signature = lctrs.getSignature();
            final Set<String> reserved = new LinkedHashSet<>();
            reserved.add(PredefinedSemanticsFactory.BOOLEAN_FS_TRUE.getName());
            reserved.add(PredefinedSemanticsFactory.BOOLEAN_FS_FALSE.getName());
            for (final Func func : Func.values()) {
                reserved.add(func.getName());
            }
            final Set<String> used = new LinkedHashSet<>(reserved);
            for (final FunctionSymbol f : this.signature.functions().keySet()) {
                used.add(f.getName());
            }
            final FreshNameGenerator names = new FreshNameGenerator(used, FreshNameGenerator.APPEND_NUMBERS);
            for (final FunctionSymbol f : this.signature.functions().keySet()) {
                if (reserved.contains(f.getName())) {
                    this.renaming.put(f, FunctionSymbol.create(names.getFreshName(f.getName(), false), f.getArity()));
                }
            }
        }

        private IGeneralizedRule convert(final LCTRSRule rule) throws UnsupportedSymbolException {
            return IGeneralizedRule.create(
                (TRSFunctionApplication) this.convert(rule.left()),
                this.convert(rule.right()),
                rule.hasGuard() ? this.convert(rule.guard()) : null);
        }

        private TRSTerm convert(final TRSTerm term) throws UnsupportedSymbolException {
            if (term.isVariable()) {
                return term;
            }
            final TRSFunctionApplication app = (TRSFunctionApplication) term;
            final FunctionSymbol f = app.getRootSymbol();
            final LCTRSUserTheorySymbol userSymbol = this.signature.userTheorySymbols().get(f);
            if (userSymbol != null) {
                // replace the user-defined theory symbol by its body
                final Map<TRSVariable, TRSTerm> instance = new LinkedHashMap<>();
                for (int i = 0; i < f.getArity(); i++) {
                    instance.put(userSymbol.parameters().get(i), app.getArguments().get(i));
                }
                final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(instance));
                return this.convert(userSymbol.body().applySubstitution(sigma));
            }
            final TRSTerm[] args = new TRSTerm[f.getArity()];
            for (int i = 0; i < args.length; i++) {
                args[i] = this.convert(app.getArguments().get(i));
            }
            if (this.signature.isTermSymbol(f)) {
                return TRSTerm.createFunctionApplication(this.renaming.getOrDefault(f, f), args);
            }
            final LCTRSSort valueSort = this.signature.getValueSort(f);
            if (LCTRSSort.BOOL.equals(valueSort)) {
                return f.getName().equals("true")
                    ? PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE
                    : PredefinedSemanticsFactory.BOOLEAN_TERM_FALSE;
            }
            if (LCTRSSort.INT.equals(valueSort)) {
                return PredefinedSemanticsFactory.getIntTerm(
                    BigIntImmutable.create(new BigInteger(f.getName())),
                    DomainFactory.INTEGERS);
            }
            final LCTRSTheorySymbol symbol = this.signature.theorySymbols().get(f);
            final String key = symbol.name() + "/" + f.getArity();
            if (Converter.BOOLEAN.containsKey(key)) {
                return this.apply(Converter.BOOLEAN.get(key), DomainFactory.BOOLEAN, args);
            }
            if (Converter.INTEGER.containsKey(key)) {
                return this.apply(Converter.INTEGER.get(key), DomainFactory.INTEGERS, args);
            }
            switch (key) {
            case "=>/2":
                return this.bool(Func.Lor, this.bool(Func.Lnot, args[0]), args[1]);
            case "xor/2":
                return this.bool(Func.Lnot, this.equivalent(args[0], args[1]));
            case "=/2":
            case "distinct/2": {
                // these exist for Booleans and for integers
                final boolean equality = symbol.name().equals("=");
                if (LCTRSSort.BOOL.equals(symbol.declaration().argumentSorts().get(0))) {
                    final TRSTerm equivalent = this.equivalent(args[0], args[1]);
                    return equality ? equivalent : this.bool(Func.Lnot, equivalent);
                }
                return this.apply(equality ? Func.Eq : Func.Neq, DomainFactory.INTEGERS, args);
            }
            default:
                throw new UnsupportedSymbolException(f);
            }
        }

        /**
         * @return the term <code>(a && b) || (!a && !b)</code>
         */
        private TRSTerm equivalent(final TRSTerm a, final TRSTerm b) {
            return this.bool(
                Func.Lor,
                this.bool(Func.Land, a, b),
                this.bool(Func.Land, this.bool(Func.Lnot, a), this.bool(Func.Lnot, b)));
        }

        private TRSTerm bool(final Func func, final TRSTerm... args) {
            return this.apply(func, DomainFactory.BOOLEAN, args);
        }

        /**
         * @return the application of the pre-defined function on the given domain to the arguments
         */
        private TRSTerm apply(final Func func, final Domain domain, final TRSTerm... args) {
            final FunctionSymbol f = FunctionSymbol.create(func.getName(), func.getArity());
            this.predefined.computeIfAbsent(
                f,
                key -> PredefinedSemanticsFactory.getFunction(
                    func,
                    ImmutableCreator.create(Collections.nCopies(func.getArity(), domain))));
            return TRSTerm.createFunctionApplication(f, args);
        }

    }

    /**
     * The proof of the conversion.
     */
    private static class LCTRSToITRSProof extends Proof.DefaultProof {

        private final Map<FunctionSymbol, FunctionSymbol> renaming;

        private final FunctionSymbol entrypoint;

        private LCTRSToITRSProof(final Map<FunctionSymbol, FunctionSymbol> renaming, final FunctionSymbol entrypoint) {
            this.renaming = renaming;
            this.entrypoint = entrypoint;
            this.setShortName("LCTRSToITRSProof");
            this.setLongName("LCTRS to ITRS");
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append("Converted the LCTRS to an ITRS: the sorts are dropped, the theory symbols become the ");
            res.append("pre-defined symbols and the guards become conditions. ");
            res.append("Since ITRSs are evaluated innermost, termination of the ITRS only implies innermost ");
            res.append("termination of the LCTRS.");
            if (this.entrypoint != null) {
                res.append(" The entrypoint ").append(o.escape(this.entrypoint.getName()));
                res.append(" is ignored, i.e., all terms are regarded as start terms.");
            }
            if (!this.renaming.isEmpty()) {
                res.append(o.linebreak()).append("The following function symbols were renamed:");
                for (final Map.Entry<FunctionSymbol, FunctionSymbol> entry : this.renaming.entrySet()) {
                    res.append(o.linebreak()).append(o.escape(entry.getKey().getName())).append(" ");
                    res.append(o.rightarrow()).append(" ").append(o.escape(entry.getValue().getName()));
                }
            }
            return res.toString();
        }

    }

}
