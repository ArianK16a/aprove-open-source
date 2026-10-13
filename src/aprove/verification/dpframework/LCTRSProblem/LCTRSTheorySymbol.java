package aprove.verification.dpframework.LCTRSProblem;

import immutables.*;

/**
 * An instance of a symbol of an SMT-LIB theory, e.g. <code>=</code> on Int. Different instances of a
 * polymorphic symbol are different function symbols, which are named like <code>=@Int</code>.
 *
 * @param name the name of the symbol in SMT-LIB
 */
public record LCTRSTheorySymbol(String name, LCTRSSortDeclaration declaration) implements Immutable {
}
