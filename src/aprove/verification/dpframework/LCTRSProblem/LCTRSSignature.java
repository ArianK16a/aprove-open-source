package aprove.verification.dpframework.LCTRSProblem;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * The signature of an LCTRS. It consists of the <em>term symbols</em>, which are declared with their sorts,
 * and the <em>theory symbols</em>, which have a fixed interpretation: the symbols and values of the SMT-LIB
 * theories and the symbols that the input defines by a logical term. The values belong to both parts.
 *
 * <p>Terms are ordinary {@link TRSTerm}s. A value is a constant whose name is the literal, e.g.
 * <code>-3</code> or <code>true</code>; the values are not listed. Every function symbol has fixed sorts:
 * the instances of a polymorphic theory symbol like <code>=</code> are different function symbols.</p>
 *
 * <p>The collections are not copied, see {@link #copy()}.</p>
 *
 * @param theories the declared SMT-LIB theories
 * @param sorts the sorts that are declared by the user
 * @param functions the term symbols (except the values) with their sorts
 * @param theorySymbols the symbols of the SMT-LIB theories that are used, with their sorts
 * @param userTheorySymbols the theory symbols that the input defines by a logical term (define-fun)
 */
public record LCTRSSignature(
    Set<LCTRSTheory> theories,
    Set<LCTRSSort> sorts,
    Map<FunctionSymbol, LCTRSSortDeclaration> functions,
    Map<FunctionSymbol, LCTRSTheorySymbol> theorySymbols,
    Map<FunctionSymbol, LCTRSUserTheorySymbol> userTheorySymbols)
{

    /**
     * @return an unmodifiable copy that keeps the order of the declarations
     */
    public LCTRSSignature copy() {
        return new LCTRSSignature(
            Collections.unmodifiableSet(new LinkedHashSet<>(this.theories)),
            Collections.unmodifiableSet(new LinkedHashSet<>(this.sorts)),
            Collections.unmodifiableMap(new LinkedHashMap<>(this.functions)),
            Collections.unmodifiableMap(new LinkedHashMap<>(this.theorySymbols)),
            Collections.unmodifiableMap(new LinkedHashMap<>(this.userTheorySymbols)));
    }

    public boolean hasSort(final LCTRSSort sort) {
        return this.sorts.contains(sort) || this.theories.stream().anyMatch(theory -> theory.hasSort(sort));
    }

    public boolean isTermSymbol(final FunctionSymbol f) {
        return this.functions.containsKey(f);
    }

    /**
     * @return the sort of f if it is a value of one of the theories, otherwise null
     */
    public LCTRSSort getValueSort(final FunctionSymbol f) {
        if (f.getArity() != 0 || this.isTermSymbol(f)) {
            return null;
        }
        for (final LCTRSTheory theory : this.theories) {
            final LCTRSSort sort = theory.getValueSort(f.getName());
            if (sort != null) {
                return sort;
            }
        }
        return null;
    }

    public boolean isValue(final FunctionSymbol f) {
        return this.getValueSort(f) != null;
    }

    /**
     * @return true iff f is a value, a symbol of one of the theories or defined by a logical term
     */
    public boolean isTheorySymbol(final FunctionSymbol f) {
        return this.theorySymbols.containsKey(f) || this.userTheorySymbols.containsKey(f) || this.isValue(f);
    }

    /**
     * @return true iff the term only consists of theory symbols and variables
     */
    public boolean isLogicalTerm(final TRSTerm term) {
        return term.getFunctionSymbols().stream().allMatch(this::isTheorySymbol);
    }

    /**
     * @return true iff the term only consists of term symbols, values and variables
     */
    public boolean isProperTerm(final TRSTerm term) {
        return term.getFunctionSymbols().stream().allMatch(f -> this.isTermSymbol(f) || this.isValue(f));
    }

    /**
     * @return the sorts of f or null if f is no symbol of this signature
     */
    public LCTRSSortDeclaration getDeclaration(final FunctionSymbol f) {
        if (this.functions.containsKey(f)) {
            return this.functions.get(f);
        }
        if (this.theorySymbols.containsKey(f)) {
            return this.theorySymbols.get(f).declaration();
        }
        if (this.userTheorySymbols.containsKey(f)) {
            return this.userTheorySymbols.get(f).declaration();
        }
        final LCTRSSort valueSort = this.getValueSort(f);
        return valueSort == null ? null : new LCTRSSortDeclaration(List.of(), valueSort);
    }

    /**
     * @return the name of f in the input, which differs from the name of the function symbol for the
     * instances of polymorphic theory symbols
     */
    public String getName(final FunctionSymbol f) {
        return this.theorySymbols.containsKey(f) ? this.theorySymbols.get(f).name() : f.getName();
    }

    /**
     * @return the sort of a well-sorted term for the given sorts of its variables
     */
    public LCTRSSort sortOf(final TRSTerm term, final Map<TRSVariable, LCTRSSort> variableSorts) {
        if (term.isVariable()) {
            return variableSorts.get(term);
        }
        final LCTRSSortDeclaration declaration = this.getDeclaration(((TRSFunctionApplication) term).getRootSymbol());
        return declaration == null ? null : declaration.resultSort();
    }

}
