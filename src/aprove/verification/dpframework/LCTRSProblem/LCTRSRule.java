package aprove.verification.dpframework.LCTRSProblem;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * A constrained rewrite rule <code>left -> right [guard]</code> of an LCTRS with the sorts of its variables.
 *
 * <p>The variables of the guard and the variables of the right-hand side that do not occur in the left-hand
 * side are the <em>logical variables</em>. The rule can only be applied with a substitution that maps these
 * to values and makes the guard valid (Kop and Nishida, Term Rewriting with Logical Constraints, 2013).</p>
 *
 * @param guard the guard, {@link #TRUE} for a rule without guard
 * @param variableSorts the sorts of all variables of the three terms
 */
public record LCTRSRule(
    TRSFunctionApplication left,
    TRSTerm right,
    TRSTerm guard,
    Map<TRSVariable, LCTRSSort> variableSorts) implements Immutable
{

    /** The guard of a rule that is given without a guard. */
    public static final TRSFunctionApplication TRUE =
        TRSTerm.createFunctionApplication(FunctionSymbol.create("true", 0));

    /** The names of the binary theory symbols that are printed infix. */
    private static final Set<String> INFIX =
        Set.of("+", "-", "*", "/", "div", "mod", "=", "<=", "<", ">=", ">", "and", "or", "xor", "=>");

    public LCTRSRule {
        variableSorts = Collections.unmodifiableMap(new LinkedHashMap<>(variableSorts));
    }

    public boolean hasGuard() {
        return !LCTRSRule.TRUE.equals(this.guard);
    }

    public Set<TRSVariable> logicalVariables() {
        final Set<TRSVariable> res = new LinkedHashSet<>(this.right.getVariables());
        res.removeAll(this.left.getVariables());
        res.addAll(this.guard.getVariables());
        return res;
    }

    /**
     * @return true iff all variables of the guard occur in the left-hand side
     */
    public boolean isRegular() {
        return this.left.getVariables().containsAll(this.guard.getVariables());
    }

    /**
     * @param signature see {@link #exportTerm}
     */
    public String export(final Export_Util eu, final LCTRSSignature signature) {
        final String rule =
            LCTRSRule.exportTerm(this.left, eu, signature) + " " + eu.rightarrow() + " "
                + LCTRSRule.exportTerm(this.right, eu, signature);
        return this.hasGuard() ? rule + " [" + LCTRSRule.exportTerm(this.guard, eu, signature) + "]" : rule;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util(), null);
    }

    /**
     * Exports a term of an LCTRS, where the binary theory symbols are written infix.
     *
     * @param signature provides the names of the theory symbols, see {@link LCTRSSignature#getName}; with
     * null the names of the function symbols are used
     */
    public static String exportTerm(final TRSTerm term, final Export_Util eu, final LCTRSSignature signature) {
        return eu.escape(LCTRSRule.toString(term, false, signature));
    }

    private static String toString(final TRSTerm term, final boolean nested, final LCTRSSignature signature) {
        if (term.isVariable()) {
            return ((TRSVariable) term).getName();
        }
        final TRSFunctionApplication app = (TRSFunctionApplication) term;
        final FunctionSymbol f = app.getRootSymbol();
        final String name = signature == null ? f.getName() : signature.getName(f);
        final List<TRSTerm> args = app.getArguments();
        if (args.isEmpty()) {
            return name;
        }
        if (args.size() == 2 && LCTRSRule.INFIX.contains(name)) {
            final String res =
                LCTRSRule.toString(args.get(0), true, signature) + " " + name + " "
                    + LCTRSRule.toString(args.get(1), true, signature);
            return nested ? "(" + res + ")" : res;
        }
        final StringJoiner res = new StringJoiner(", ", name + "(", ")");
        for (final TRSTerm arg : args) {
            res.add(LCTRSRule.toString(arg, false, signature));
        }
        return res.toString();
    }

}
