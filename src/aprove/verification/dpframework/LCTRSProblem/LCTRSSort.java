package aprove.verification.dpframework.LCTRSProblem;

import immutables.*;

/**
 * A sort of an LCTRS: a sort of an SMT-LIB theory (<code>Bool</code>, <code>Int</code>, <code>Real</code>)
 * or a sort declared by the user.
 *
 * @param isTheorySort false iff the user declared the sort
 */
public record LCTRSSort(String name, boolean isTheorySort) implements Immutable {

    public static final LCTRSSort BOOL = new LCTRSSort("Bool", true);

    public static final LCTRSSort INT = new LCTRSSort("Int", true);

    public static final LCTRSSort REAL = new LCTRSSort("Real", true);

    public static LCTRSSort user(final String name) {
        return new LCTRSSort(name, false);
    }

    @Override
    public String toString() {
        return this.name;
    }

}
