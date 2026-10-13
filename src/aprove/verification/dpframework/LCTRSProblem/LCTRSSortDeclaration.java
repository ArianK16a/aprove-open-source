package aprove.verification.dpframework.LCTRSProblem;

import java.util.*;
import java.util.stream.*;

import immutables.*;

/**
 * The sort declaration <code>[s_1 x ... x s_n] => s</code> of a function symbol of an LCTRS.
 */
public record LCTRSSortDeclaration(List<LCTRSSort> argumentSorts, LCTRSSort resultSort) implements Immutable {

    public LCTRSSortDeclaration {
        argumentSorts = List.copyOf(argumentSorts);
    }

    public int arity() {
        return this.argumentSorts.size();
    }

    @Override
    public String toString() {
        if (this.argumentSorts.isEmpty()) {
            return this.resultSort.toString();
        }
        return this.argumentSorts.stream().map(LCTRSSort::toString).collect(Collectors.joining(" x ", "[", "] => "))
            + this.resultSort;
    }

}
