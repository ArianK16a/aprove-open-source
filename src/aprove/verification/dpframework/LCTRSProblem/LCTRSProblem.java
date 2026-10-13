package aprove.verification.dpframework.LCTRSProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * A logically constrained term rewrite system (LCTRS) as defined by Kop and Nishida (Term Rewriting with
 * Logical Constraints, FroCoS 2013) and as given in the ARI format: a many-sorted TRS whose rules
 * <code>l -> r [phi]</code> have a guard phi, a term of sort Bool over the theory symbols.
 *
 * <p>There are two kinds of rewrite steps: a rule step with a rule and a substitution that maps the logical
 * variables of the rule to values and satisfies the guard, and a calculation step that replaces a theory
 * symbol applied to values by its value.</p>
 */
public final class LCTRSProblem extends DefaultBasicObligation {

    private final LCTRSSignature signature;

    private final List<LCTRSRule> rules;

    private final FunctionSymbol entrypoint;

    private final String smtlibStandard;

    /**
     * @param entrypoint the term symbol at the root of the start terms or null if all terms are start terms.
     * This is an extension of the ARI format that is used for integer transition systems.
     * @param smtlibStandard the SMT-LIB standard of the theories (e.g. <code>2.6</code>) or null if the
     * input does not state it
     */
    public LCTRSProblem(
        final LCTRSSignature signature,
        final Collection<LCTRSRule> rules,
        final FunctionSymbol entrypoint,
        final String smtlibStandard)
    {
        super("LCTRS", "Logically Constrained TRS");
        this.signature = signature.copy();
        this.rules = List.copyOf(rules);
        this.entrypoint = entrypoint;
        this.smtlibStandard = smtlibStandard;
    }

    public LCTRSSignature getSignature() {
        return this.signature;
    }

    public List<LCTRSRule> getRules() {
        return this.rules;
    }

    public FunctionSymbol getEntrypoint() {
        return this.entrypoint;
    }

    public String getSmtlibStandard() {
        return this.smtlibStandard;
    }

    /**
     * @return the term symbols that occur at the root of a left-hand side
     */
    public Set<FunctionSymbol> getDefinedSymbols() {
        final Set<FunctionSymbol> res = new LinkedHashSet<>();
        for (final LCTRSRule rule : this.rules) {
            res.add(rule.left().getRootSymbol());
        }
        return res;
    }

    /**
     * @return true iff the left-hand side of the rule is a proper term. Then no calculation step can overlap
     * with the rule.
     */
    public boolean isStandard(final LCTRSRule rule) {
        return this.signature.isProperTerm(rule.left());
    }

    @Override
    public String export(final Export_Util o) {
        final StringJoiner theories = new StringJoiner(", ");
        this.signature.theories().forEach(theory -> theories.add(theory.getSmtName()));
        final StringJoiner sorts = new StringJoiner(", ");
        this.signature.sorts().forEach(sort -> sorts.add(sort.toString()));
        final List<String> lines = new ArrayList<>();
        lines.add(
            o.escape(
                "LCTRS over " + theories + (this.smtlibStandard == null ? "" : " of SMT-LIB " + this.smtlibStandard)));
        if (!this.signature.sorts().isEmpty()) {
            lines.add(o.escape("Sorts: " + sorts));
        }
        if (!this.signature.userTheorySymbols().isEmpty()) {
            lines.add("User-defined theory symbols:");
            for (final LCTRSUserTheorySymbol userSymbol : this.signature.userTheorySymbols().values()) {
                lines.add(userSymbol.export(o, this.signature));
            }
        }
        lines.add("Signature:");
        this.signature.functions().forEach((f, declaration) -> lines.add(o.escape(f.getName() + " : " + declaration)));
        lines.add("Rules:");
        this.rules.forEach(rule -> lines.add(rule.export(o, this.signature)));
        if (this.entrypoint != null) {
            lines.add(o.escape("Entrypoint: " + this.entrypoint.getName()));
        }
        return String.join(o.linebreak(), lines) + o.linebreak();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    @Override
    public String getStrategyName() {
        return "lctrs";
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

}
