package aprove.input.Programs.ariLctrs;

import java.util.*;

import aprove.input.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.LCTRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Builds an {@link LCTRSProblem} from the declarations of an LCTRS in the ARI format. The parser calls the
 * methods of this class in the order of the input, so that an identifier in a term can be resolved by the
 * declarations before it. All problems are collected as {@link ParseError}s.
 *
 * <p>Besides resolving identifiers, this removes the syntactic sugar of SMT-LIB (variadic uses of
 * associative, chainable and pairwise symbols), infers the sorts of the variables and checks that
 * everything is well-sorted. Quantifiers are not supported yet.</p>
 *
 * <p>While a rule or definition is read, a theory symbol is a function symbol with its name in SMT-LIB,
 * which may stand for several instances (<code>=</code> on Bool or on Int). Once the sorts are inferred,
 * {@link #resolve} replaces it by the function symbol of its instance.</p>
 */
public class LctrsBuilder {

    /** Theory symbols that may be applied to more than two arguments, associating to the left. */
    private static final Set<String> LEFT_ASSOCIATIVE =
        Set.of("and", "or", "xor", "-", "+", "*", "div", "/");

    /** Theory symbols where more than two arguments stand for the conjunction over neighbouring arguments. */
    private static final Set<String> CHAINABLE = Set.of("=", "<=", "<", ">=", ">");

    /** The reserved words of SMT-LIB 2.6 that cannot be used as names (besides values and theory symbols). */
    private static final Set<String> RESERVED = Set.of("as", "let", "forall", "exists", "match", "!", "_");

    private static final Set<String> THEORY_SORT_NAMES = Set.of("Bool", "Int", "Real");

    private static final int MAX_THEORY_ARITY = 3;

    /** Separates the name of a polymorphic theory symbol from the sort of its instance, as for ITRSs. */
    private static final char INSTANCE_SEPARATOR = '@';

    private final List<ParseError> errors = new ArrayList<>();

    /** Set if the theories are not usable. Then the other errors are just consequences and not reported. */
    private ParseError theoryError;

    /** The declarations so far; the collections of this signature grow while the input is read. */
    private final LCTRSSignature signature =
        new LCTRSSignature(
            new LinkedHashSet<>(),
            new LinkedHashSet<>(),
            new LinkedHashMap<>(),
            new LinkedHashMap<>(),
            new LinkedHashMap<>());

    /** The arities of the term symbols and the user-defined theory symbols by their names. */
    private final Map<String, Integer> arities = new LinkedHashMap<>();

    private final List<LCTRSRule> rules = new ArrayList<>();

    private String smtlibStandard;

    private FunctionSymbol entrypoint;

    public List<ParseError> getErrors() {
        return this.theoryError == null ? this.errors : List.of(this.theoryError);
    }

    /**
     * @return the LCTRS or null if there are errors
     */
    public LCTRSProblem build() {
        if (this.signature.theories().isEmpty()) {
            this.theoryError(1, "At least one theory must be declared.");
        }
        return this.getErrors().isEmpty()
            ? new LCTRSProblem(this.signature, this.rules, this.entrypoint, this.smtlibStandard)
            : null;
    }

    private void error(final int line, final String message) {
        final ParseError pe = new ParseError(ParseError.ERROR);
        pe.setLine(line);
        pe.setMessage(message);
        this.errors.add(pe);
    }

    private void theoryError(final int line, final String message) {
        if (this.theoryError == null) {
            this.error(line, message);
            this.theoryError = this.errors.get(this.errors.size() - 1);
        }
    }

    // ---------------------------------------------------------------------------------------------------
    // declarations
    // ---------------------------------------------------------------------------------------------------

    public void format(final String name, final String standard, final int line) {
        if (!name.equals("LCTRS")) {
            this.error(line, "Expected the format LCTRS but found " + name + ".");
        }
        this.smtlibStandard = standard;
    }

    public void theory(final String name, final int line) {
        final LCTRSTheory theory = LCTRSTheory.fromName(name);
        final Set<LCTRSTheory> theories = this.signature.theories();
        if (theory == null) {
            this.theoryError(line, "The theory " + name + " is not supported.");
        } else if (!theories.add(theory)) {
            this.error(line, "The theory " + name + " is declared twice.");
        } else if (theories.contains(LCTRSTheory.INTS) && theories.contains(LCTRSTheory.REALS)) {
            // an integer literal would be both an integer and a real number
            this.error(line, "The theories Ints and Reals cannot be combined, use Reals_Ints instead.");
        }
    }

    public void declareSort(final String name, final int line) {
        if (LctrsBuilder.THEORY_SORT_NAMES.contains(name)) {
            this.error(line, "The theory sort " + name + " cannot be declared.");
        } else if (!this.signature.sorts().add(LCTRSSort.user(name))) {
            this.error(line, "The sort " + name + " is declared twice.");
        }
    }

    /**
     * @param names the name of the sort or, for an indexed sort like <code>(_ BitVec 32)</code>, its parts
     * @return the sort or null (with an error) if it does not exist
     */
    public LCTRSSort sort(final List<String> names, final int line) {
        final String name = String.join(" ", names);
        // no theory with indexed sorts is supported
        final LCTRSSort sort =
            name.equals("Bool") ? LCTRSSort.BOOL
                : name.equals("Int") ? LCTRSSort.INT
                    : name.equals("Real") ? LCTRSSort.REAL : LCTRSSort.user(name);
        if (names.size() != 1 || !this.signature.hasSort(sort)) {
            this.error(line, "The sort " + name + " is neither declared nor a theory sort.");
            return null;
        }
        return sort;
    }

    /**
     * Adds a variable with its sort to the variables that are declared together (parameters or
     * <code>:var</code>).
     */
    public void variable(
        final Map<String, LCTRSSort> variables,
        final String name,
        final LCTRSSort sort,
        final int line)
    {
        if (this.arities.containsKey(name) || this.isTheoryName(name)) {
            this.error(line, "The variable " + name + " has the name of a function symbol or value.");
        } else if (variables.containsKey(name)) {
            this.error(line, "The variable " + name + " is declared twice.");
        } else if (sort != null) {
            variables.put(name, sort);
        }
    }

    /**
     * A declaration <code>(fun name sorts)</code> where the last sort is the sort of the result.
     */
    public void function(final String name, final List<LCTRSSort> sorts, final int line) {
        if (this.checkNewSymbol(name, line) && !sorts.contains(null)) {
            final int arity = sorts.size() - 1;
            this.arities.put(name, arity);
            this.signature.functions().put(
                FunctionSymbol.create(name, arity),
                new LCTRSSortDeclaration(sorts.subList(0, arity), sorts.get(arity)));
        }
    }

    /**
     * A definition <code>(define-fun name (parameters) resultSort body)</code> of a theory symbol.
     */
    public void define(
        final String name,
        final Map<String, LCTRSSort> parameters,
        final LCTRSSort resultSort,
        final TRSTerm body,
        final int line)
    {
        if (!this.checkNewSymbol(name, line) || resultSort == null || body == null) {
            return;
        }
        final Map<TRSVariable, LCTRSSort> variableSorts = LctrsBuilder.toVariables(parameters);
        final List<String> problems = new ArrayList<>();
        if (parameters.isEmpty()) {
            problems.add("It needs at least one parameter.");
        }
        if (!variableSorts.keySet().containsAll(body.getVariables())) {
            problems.add("Its body contains unknown identifiers.");
        }
        final List<LCTRSSort> sorts = new ArrayList<>(parameters.values());
        sorts.add(resultSort);
        if (!sorts.stream().allMatch(LCTRSSort::isTheorySort)) {
            problems.add("Its parameters and its result must have theory sorts.");
        }
        if (problems.isEmpty()) {
            this.sortOf(body, resultSort, variableSorts, problems);
        }
        for (final String problem : problems) {
            this.error(line, "In the definition of " + name + ": " + problem);
        }
        if (problems.isEmpty()) {
            final FunctionSymbol f = FunctionSymbol.create(name, parameters.size());
            this.arities.put(name, parameters.size());
            this.signature.userTheorySymbols().put(
                f,
                new LCTRSUserTheorySymbol(
                    f,
                    new ArrayList<>(variableSorts.keySet()),
                    new LCTRSSortDeclaration(sorts.subList(0, parameters.size()), resultSort),
                    this.resolve(body, variableSorts)));
        }
    }

    public void entrypoint(final String name, final int line) {
        final Integer arity = this.arities.get(name);
        final FunctionSymbol f = arity == null ? null : FunctionSymbol.create(name, arity);
        if (this.entrypoint != null) {
            this.error(line, "There is more than one entrypoint.");
        } else if (f == null || !this.signature.isTermSymbol(f)) {
            this.error(line, "The entrypoint " + name + " is not declared as function symbol.");
        } else {
            this.entrypoint = f;
        }
    }

    /**
     * @return true iff the name is used by the theories: as value, as theory symbol or as reserved word
     */
    private boolean isTheoryName(final String name) {
        boolean res = LctrsBuilder.RESERVED.contains(name) || this.signature.isValue(FunctionSymbol.create(name, 0));
        for (int arity = 1; arity <= LctrsBuilder.MAX_THEORY_ARITY; arity++) {
            res |= this.instantiate(name, new LCTRSSort[arity], null) != null;
        }
        // the function symbols for the instances of polymorphic theory symbols have names like =@Int
        final int separator = name.lastIndexOf(LctrsBuilder.INSTANCE_SEPARATOR);
        return res || separator > 0 && this.isTheoryName(name.substring(0, separator));
    }

    private boolean checkNewSymbol(final String name, final int line) {
        if (this.isTheoryName(name)) {
            this.error(line, "The name " + name + " is a value, a theory symbol or a reserved word.");
        } else if (this.arities.containsKey(name)) {
            this.error(line, "The symbol " + name + " is declared twice.");
        } else {
            return true;
        }
        return false;
    }

    private static Map<TRSVariable, LCTRSSort> toVariables(final Map<String, LCTRSSort> sorts) {
        final Map<TRSVariable, LCTRSSort> res = new LinkedHashMap<>();
        sorts.forEach((name, sort) -> res.put(TRSTerm.createVariable(name), sort));
        return res;
    }

    // ---------------------------------------------------------------------------------------------------
    // terms and rules
    // ---------------------------------------------------------------------------------------------------

    /**
     * Resolves an identifier (without arguments) or an application. An identifier that is neither declared
     * nor a value is a variable. Variadic uses of theory symbols are replaced by their meaning.
     *
     * @return the term or null (with an error, or since an argument is null) if there is none
     */
    public TRSTerm term(final String head, final List<TRSTerm> args, final int line) {
        if (args.contains(null)) {
            return null;
        }
        final int arity = args.size();
        final FunctionSymbol f = FunctionSymbol.create(head, arity);
        if (this.arities.containsKey(head)) {
            if (this.arities.get(head) != arity) {
                this.error(line, "The symbol " + head + " is applied to " + arity + " instead of "
                    + this.arities.get(head) + " arguments.");
                return null;
            }
            return TRSTerm.createFunctionApplication(f, args);
        }
        if (this.signature.isValue(f) || arity > 0 && this.instantiate(head, new LCTRSSort[arity], null) != null) {
            return TRSTerm.createFunctionApplication(f, args);
        }
        if (arity == 0 && !this.isTheoryName(head)) {
            return TRSTerm.createVariable(head);
        }
        // syntactic sugar: more than two arguments for a binary theory symbol
        final boolean binary = arity > 2 && this.instantiate(head, new LCTRSSort[2], null) != null;
        TRSTerm res = null;
        if (binary && LctrsBuilder.LEFT_ASSOCIATIVE.contains(head)) {
            res = args.get(0);
            for (int i = 1; i < arity; i++) {
                res = LctrsBuilder.apply(head, res, args.get(i));
            }
        } else if (binary && head.equals("=>")) {
            res = args.get(arity - 1);
            for (int i = arity - 2; i >= 0; i--) {
                res = LctrsBuilder.apply(head, args.get(i), res);
            }
        } else if (binary && (LctrsBuilder.CHAINABLE.contains(head) || head.equals("distinct"))) {
            // chainable: neighbouring arguments, distinct: all pairs
            for (int i = 0; i < arity - 1; i++) {
                for (int j = i + 1; j < (head.equals("distinct") ? arity : i + 2); j++) {
                    final TRSTerm atom = LctrsBuilder.apply(head, args.get(i), args.get(j));
                    res = res == null ? atom : LctrsBuilder.apply("and", res, atom);
                }
            }
        } else {
            this.error(line, "Unknown function symbol " + head + " with " + arity
                + " arguments (a variable or value cannot be applied).");
        }
        return res;
    }

    private static TRSTerm apply(final String name, final TRSTerm left, final TRSTerm right) {
        return TRSTerm.createFunctionApplication(FunctionSymbol.create(name, 2), left, right);
    }

    public TRSTerm quantifier(final String quantifier, final int line) {
        this.error(line, "Quantifiers are not supported yet (" + quantifier + ").");
        return null;
    }

    /**
     * A rule <code>(rule left right :guard guard :var (variables))</code>.
     *
     * @param guard {@link LCTRSRule#TRUE} if the rule has no guard
     * @param variables the declared sorts of variables or null if there is no <code>:var</code>
     */
    public void rule(
        final TRSTerm left,
        final TRSTerm right,
        final TRSTerm guard,
        final Map<String, LCTRSSort> variables,
        final int line)
    {
        if (left == null || right == null || guard == null) {
            return;
        }
        final List<String> problems = new ArrayList<>();
        if (left.isVariable() || !this.signature.isTermSymbol(((TRSFunctionApplication) left).getRootSymbol())) {
            problems.add("The left-hand side must have a declared function symbol at its root.");
        }
        if (!Collections.disjoint(guard.getFunctionSymbols(), this.signature.functions().keySet())) {
            problems.add("The guard must be a logical term, but it contains a declared function symbol.");
        }
        final Map<TRSVariable, LCTRSSort> variableSorts =
            variables == null ? new LinkedHashMap<>() : LctrsBuilder.toVariables(variables);
        if (problems.isEmpty()) {
            // infer sorts of variables until nothing changes, then report what is wrong
            int known;
            do {
                known = variableSorts.size();
                this.sortRule(left, right, guard, variableSorts, null);
            } while (variableSorts.size() > known);
            this.sortRule(left, right, guard, variableSorts, problems);
        }
        for (final String problem : new LinkedHashSet<>(problems)) {
            this.error(line, problem);
        }
        if (problems.isEmpty()) {
            final Set<TRSVariable> occurring = new LinkedHashSet<>(left.getVariables());
            occurring.addAll(right.getVariables());
            occurring.addAll(guard.getVariables());
            variableSorts.keySet().retainAll(occurring);
            this.rules.add(
                new LCTRSRule(
                    (TRSFunctionApplication) this.resolve(left, variableSorts),
                    this.resolve(right, variableSorts),
                    this.resolve(guard, variableSorts),
                    variableSorts));
        }
    }

    /**
     * Both sides of a rule have the same sort, and the guard has the sort Bool.
     */
    private void sortRule(
        final TRSTerm left,
        final TRSTerm right,
        final TRSTerm guard,
        final Map<TRSVariable, LCTRSSort> variableSorts,
        final Collection<String> problems)
    {
        final LCTRSSort leftSort = this.sortOf(left, null, variableSorts, problems);
        final LCTRSSort rightSort = this.sortOf(right, leftSort, variableSorts, problems);
        if (leftSort == null && rightSort != null) {
            this.sortOf(left, rightSort, variableSorts, problems);
        }
        this.sortOf(guard, LCTRSSort.BOOL, variableSorts, problems);
    }

    // ---------------------------------------------------------------------------------------------------
    // sorts
    // ---------------------------------------------------------------------------------------------------

    /**
     * @return the result of {@link LCTRSTheory#instantiate} for the declared theory that has such a symbol
     */
    private LCTRSSort[] instantiate(final String name, final LCTRSSort[] arguments, final LCTRSSort result) {
        final Set<LCTRSTheory> theories = this.signature.theories();
        for (final LCTRSTheory theory : theories) {
            // every other theory contains Core, where = would only be known for Bool
            final LCTRSSort[] instance =
                theory == LCTRSTheory.CORE && theories.size() > 1 ? null : theory.instantiate(name, arguments, result);
            if (instance != null) {
                return instance;
            }
        }
        return null;
    }

    /**
     * Replaces the theory symbols of a well-sorted term by the function symbols of their instances, which
     * are added to the signature.
     */
    private TRSTerm resolve(final TRSTerm term, final Map<TRSVariable, LCTRSSort> variableSorts) {
        if (term.isVariable()) {
            return term;
        }
        final TRSFunctionApplication app = (TRSFunctionApplication) term;
        final FunctionSymbol f = app.getRootSymbol();
        final int arity = f.getArity();
        final List<TRSTerm> args = new ArrayList<>();
        final LCTRSSort[] argumentSorts = new LCTRSSort[arity];
        for (int i = 0; i < arity; i++) {
            args.add(this.resolve(app.getArgument(i), variableSorts));
            argumentSorts[i] = this.signature.sortOf(args.get(i), variableSorts);
        }
        if (this.arities.containsKey(f.getName()) || this.signature.isValue(f)) {
            return TRSTerm.createFunctionApplication(f, args);
        }
        final LCTRSSort[] instance = this.instantiate(f.getName(), argumentSorts, null);
        // a polymorphic symbol has a sort that is only determined by the arguments
        final LCTRSSort[] general = this.instantiate(f.getName(), new LCTRSSort[arity], null);
        final int open = Arrays.asList(general).indexOf(null);
        final String name = open < 0 ? f.getName() : f.getName() + LctrsBuilder.INSTANCE_SEPARATOR + instance[open];
        final FunctionSymbol resolved = FunctionSymbol.create(name, arity);
        this.signature.theorySymbols().putIfAbsent(
            resolved,
            new LCTRSTheorySymbol(
                f.getName(),
                new LCTRSSortDeclaration(Arrays.asList(instance).subList(0, arity), instance[arity])));
        return TRSTerm.createFunctionApplication(resolved, args);
    }

    /**
     * Computes the sort of a term and infers sorts of variables on the way: a variable without sort gets
     * the sort that its context expects.
     *
     * @param expected the sort that the context of the term expects or null if it does not expect one
     * @param variableSorts the known sorts of the variables, inferred sorts are added
     * @param errors collects what makes the term ill-sorted, or null to only infer sorts. Variables whose
     * sort is unknown are only reported, i.e. this should be used once nothing is inferred anymore.
     * @return the sort of the term or null if it is not known (yet)
     */
    private LCTRSSort sortOf(
        final TRSTerm term,
        final LCTRSSort expected,
        final Map<TRSVariable, LCTRSSort> variableSorts,
        final Collection<String> errors)
    {
        final LCTRSSort sort = this.computeSort(term, expected, variableSorts, errors);
        if (errors != null && sort != null && expected != null && !sort.equals(expected)) {
            errors.add(LctrsBuilder.show(term) + " has the sort " + sort + ", but " + expected + " is expected.");
        }
        return sort;
    }

    private LCTRSSort computeSort(
        final TRSTerm term,
        final LCTRSSort expected,
        final Map<TRSVariable, LCTRSSort> variableSorts,
        final Collection<String> errors)
    {
        if (term.isVariable()) {
            final TRSVariable variable = (TRSVariable) term;
            if (!variableSorts.containsKey(variable) && expected != null) {
                variableSorts.put(variable, expected);
            } else if (!variableSorts.containsKey(variable) && errors != null) {
                errors.add("The sort of the variable " + variable.getName() + " cannot be inferred, declare it.");
            }
            return variableSorts.get(variable);
        }
        final TRSFunctionApplication app = (TRSFunctionApplication) term;
        final FunctionSymbol f = app.getRootSymbol();
        final List<TRSTerm> args = app.getArguments();
        // term symbols, user-defined theory symbols and values have fixed sorts
        final LCTRSSortDeclaration declaration = this.signature.getDeclaration(f);
        if (declaration != null) {
            for (int i = 0; i < args.size(); i++) {
                this.sortOf(args.get(i), declaration.argumentSorts().get(i), variableSorts, errors);
            }
            return declaration.resultSort();
        }
        // a theory symbol: its instance depends on the sorts of the arguments
        final LCTRSSort[] argumentSorts = new LCTRSSort[args.size()];
        for (int i = 0; i < args.size(); i++) {
            argumentSorts[i] = this.sortOf(args.get(i), null, variableSorts, errors);
        }
        LCTRSSort[] instance = this.instantiate(f.getName(), argumentSorts, expected);
        if (instance == null) {
            instance = this.instantiate(f.getName(), argumentSorts, null);
        }
        if (instance == null) {
            if (errors != null && !Arrays.asList(argumentSorts).contains(null)) {
                errors.add(
                    "The theory symbol " + f.getName() + " cannot be applied to arguments of the sorts "
                        + Arrays.toString(argumentSorts) + " in " + LctrsBuilder.show(term) + ".");
            }
            return null;
        }
        if (errors == null) {
            // the instance may tell the sorts of arguments that were not known
            for (int i = 0; i < args.size(); i++) {
                if (argumentSorts[i] == null && instance[i] != null) {
                    this.sortOf(args.get(i), instance[i], variableSorts, null);
                }
            }
        }
        return instance[args.size()];
    }

    private static String show(final TRSTerm term) {
        return LCTRSRule.exportTerm(term, new aprove.prooftree.Export.Utility.PLAIN_Util(), null);
    }

}
