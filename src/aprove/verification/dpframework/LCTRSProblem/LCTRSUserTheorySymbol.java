package aprove.verification.dpframework.LCTRSProblem;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * A user-defined theory symbol: a theory symbol that the input defines by
 * <code>(define-fun f ((x_1 s_1) ... (x_n s_n)) s body)</code>. Its interpretation is given by the body, a
 * logical term over the parameters, so it can be replaced by its body.
 */
public record LCTRSUserTheorySymbol(
    FunctionSymbol symbol,
    List<TRSVariable> parameters,
    LCTRSSortDeclaration declaration,
    TRSTerm body) implements Immutable
{

    public LCTRSUserTheorySymbol {
        parameters = List.copyOf(parameters);
        if (symbol.getArity() != parameters.size() || symbol.getArity() != declaration.arity()) {
            throw new IllegalArgumentException("Wrong number of parameters for " + symbol);
        }
    }

    public String export(final Export_Util eu, final LCTRSSignature signature) {
        final StringJoiner params = new StringJoiner(", ", "(", ")");
        for (int i = 0; i < this.parameters.size(); i++) {
            params.add(this.parameters.get(i).getName() + " : " + this.declaration.argumentSorts().get(i));
        }
        return eu.escape(this.symbol.getName() + params + " : " + this.declaration.resultSort() + " := ")
            + LCTRSRule.exportTerm(this.body, eu, signature);
    }

}
