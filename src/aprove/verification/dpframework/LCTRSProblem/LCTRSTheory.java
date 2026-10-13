package aprove.verification.dpframework.LCTRSProblem;

import java.util.*;
import java.util.regex.*;

/**
 * The SMT-LIB 2.6 theories that are supported for LCTRSs, with their sorts, values and theory symbols.
 * Of the theories that the ARI format admits, FixedSizeBitVectors is missing. A new theory needs a constant
 * here with its sorts and symbols, and its literals in {@link #getValueSort}.
 *
 * <p>Some theory symbols are polymorphic, e.g. <code>=</code> exists for every theory sort. Such a symbol
 * is a single function symbol; its instance in a term is determined by the sorts of the arguments, see
 * {@link #instantiate}.</p>
 */
public enum LCTRSTheory {

    CORE("Core", List.of(), List.of(Symbols.CORE)),

    INTS("Ints", List.of(LCTRSSort.INT), List.of(Symbols.CORE, Symbols.ARITHMETIC, Symbols.INTEGER)),

    REALS("Reals", List.of(LCTRSSort.REAL), List.of(Symbols.CORE, Symbols.ARITHMETIC, Symbols.REAL)),

    REALS_INTS(
        "Reals_Ints",
        List.of(LCTRSSort.INT, LCTRSSort.REAL),
        List.of(Symbols.CORE, Symbols.ARITHMETIC, Symbols.INTEGER, Symbols.REAL, Symbols.CONVERSION));

    /**
     * The theory symbols, as maps from <code>name/arity</code> to a scheme like <code>nn>B</code>. A scheme
     * gives the sorts of the arguments and, after the <code>></code>, of the result: <code>B</code>,
     * <code>I</code> and <code>R</code> stand for Bool, Int and Real; a lower-case letter stands for one
     * arbitrary sort (<code>a</code>) or number sort (<code>n</code>) of the theory that is the same at all
     * its positions.
     */
    private static final class Symbols {

        static final Map<String, String> CORE =
            Symbols.table("B>B", "not", "BB>B", "and or xor =>", "aa>B", "= distinct", "Baa>a", "ite");

        static final Map<String, String> ARITHMETIC =
            Symbols.table("n>n", "-", "nn>n", "+ - *", "nn>B", "<= < >= >");

        static final Map<String, String> INTEGER = Symbols.table("I>I", "abs", "II>I", "div mod");

        static final Map<String, String> REAL = Symbols.table("RR>R", "/");

        static final Map<String, String> CONVERSION =
            Symbols.table("I>R", "to_real", "R>I", "to_int", "R>B", "is_int");

        /**
         * @param entries alternately a scheme and the names of the symbols with this scheme
         */
        private static Map<String, String> table(final String... entries) {
            final Map<String, String> res = new HashMap<>();
            for (int i = 0; i < entries.length; i += 2) {
                for (final String name : entries[i + 1].split(" ")) {
                    res.put(name + "/" + entries[i].indexOf('>'), entries[i]);
                }
            }
            return res;
        }

    }

    private static final Pattern INTEGER_LITERAL = Pattern.compile("-?[0-9]+");

    private static final Pattern DECIMAL_LITERAL = Pattern.compile("-?[0-9]+\\.[0-9]+");

    private static final Pattern DIVISIBLE = Pattern.compile("\\(_ divisible [1-9][0-9]*\\)");

    private final String smtName;

    /** The sorts of this theory besides Bool. */
    private final List<LCTRSSort> numberSorts;

    private final List<Map<String, String>> symbols;

    private LCTRSTheory(
        final String smtName,
        final List<LCTRSSort> numberSorts,
        final List<Map<String, String>> symbols)
    {
        this.smtName = smtName;
        this.numberSorts = numberSorts;
        this.symbols = symbols;
    }

    /**
     * @return the theory with this name in SMT-LIB or null if there is none
     */
    public static LCTRSTheory fromName(final String smtName) {
        for (final LCTRSTheory theory : LCTRSTheory.values()) {
            if (theory.smtName.equals(smtName)) {
                return theory;
            }
        }
        return null;
    }

    public String getSmtName() {
        return this.smtName;
    }

    public boolean hasSort(final LCTRSSort sort) {
        return sort.equals(LCTRSSort.BOOL) || this.numberSorts.contains(sort);
    }

    /**
     * @return the sort of the value that the literal denotes in this theory or null if it is no value of
     * this theory. In the theory Reals an integer literal is a real number.
     */
    public LCTRSSort getValueSort(final String literal) {
        if (literal.equals("true") || literal.equals("false")) {
            return LCTRSSort.BOOL;
        }
        if (LCTRSTheory.INTEGER_LITERAL.matcher(literal).matches() && !this.numberSorts.isEmpty()) {
            return this.numberSorts.get(0);
        }
        return LCTRSTheory.DECIMAL_LITERAL.matcher(literal).matches() && this.numberSorts.contains(LCTRSSort.REAL)
            ? LCTRSSort.REAL
            : null;
    }

    /**
     * Determines the instance of a theory symbol of this theory from the sorts that are known.
     *
     * @param name the name of the symbol, for an indexed symbol in the form <code>(_ name index ...)</code>
     * @param arguments the sorts of the arguments where null stands for a sort that is not known
     * @param result the sort of the result or null if it is not known
     * @return the sorts of the arguments followed by the sort of the result, where null stands for a sort
     * that the given sorts do not determine; or null if this theory has no symbol with this name and number
     * of arguments that is compatible with the given sorts
     */
    public LCTRSSort[] instantiate(final String name, final LCTRSSort[] arguments, final LCTRSSort result) {
        final int arity = arguments.length;
        String scheme = null;
        for (final Map<String, String> table : this.symbols) {
            scheme = scheme == null ? table.get(name + "/" + arity) : scheme;
        }
        if (this.numberSorts.contains(LCTRSSort.INT) && arity == 1 && LCTRSTheory.DIVISIBLE.matcher(name).matches()) {
            scheme = "I>B";
        }
        if (scheme == null) {
            return null;
        }
        final LCTRSSort[] sorts = Arrays.copyOf(arguments, arity + 1);
        sorts[arity] = result;
        final String slots = scheme.replace(">", "");
        // the sorts that the lower-case letter of the scheme may stand for, and the one it stands for
        final List<LCTRSSort> admissible = new ArrayList<>(this.numberSorts);
        if (scheme.indexOf('a') >= 0) {
            admissible.add(LCTRSSort.BOOL);
        }
        LCTRSSort common = admissible.size() == 1 ? admissible.get(0) : null;
        for (int i = 0; i <= arity; i++) {
            final char slot = slots.charAt(i);
            final LCTRSSort fixed =
                slot == 'B' ? LCTRSSort.BOOL : slot == 'I' ? LCTRSSort.INT : slot == 'R' ? LCTRSSort.REAL : null;
            if (fixed != null) {
                if (sorts[i] != null && !sorts[i].equals(fixed)) {
                    return null;
                }
                sorts[i] = fixed;
            } else if (sorts[i] != null) {
                if (!admissible.contains(sorts[i])) {
                    return null;
                }
                common = sorts[i];
                admissible.retainAll(List.of(common));
            }
        }
        for (int i = 0; i <= arity; i++) {
            sorts[i] = sorts[i] == null ? common : sorts[i];
        }
        return sorts;
    }

}
