package aprove.verification.dpframework.LCTRSProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * A dependency pair problem (P, R) of an LCTRS: a set P of dependency pairs and a set R of rules, both with
 * guards. The root symbols of the pairs are the tuple symbols, whose result sort is the sort
 * {@link #getDPSort()}.
 *
 * <p>The problem is finite if there is no infinite (P, R)-chain, i.e. no infinite sequence
 * <code>s_1 -> t_1 [phi_1], s_2 -> t_2 [phi_2], ...</code> of variable-renamed pairs from P with a
 * substitution gamma that respects all of them (it maps their logical variables to values and satisfies
 * their guards) such that <code>t_i gamma</code> rewrites to <code>s_(i+1) gamma</code> with R and
 * calculation steps. Chains are neither required to be innermost nor minimal. An LCTRS is terminating iff
 * its dependency pairs have no infinite chain (Kop, Termination of LCTRSs, WST 2013).</p>
 */
public final class LCTRSDPProblem extends DefaultBasicObligation {

    private final LCTRSSignature signature;

    private final LCTRSSort dpSort;

    private final List<LCTRSRule> pairs;

    private final List<LCTRSRule> rules;

    /**
     * @param signature the signature, whose term symbols include the tuple symbols
     * @param dpSort the result sort of the tuple symbols
     */
    public LCTRSDPProblem(
        final LCTRSSignature signature,
        final LCTRSSort dpSort,
        final Collection<LCTRSRule> pairs,
        final Collection<LCTRSRule> rules)
    {
        super("LCTRS DP", "Dependency Pair Problem of a Logically Constrained TRS");
        this.signature = signature.copy();
        this.dpSort = dpSort;
        this.pairs = List.copyOf(pairs);
        this.rules = List.copyOf(rules);
    }

    public LCTRSSignature getSignature() {
        return this.signature;
    }

    public LCTRSSort getDPSort() {
        return this.dpSort;
    }

    public List<LCTRSRule> getP() {
        return this.pairs;
    }

    public List<LCTRSRule> getR() {
        return this.rules;
    }

    /**
     * @return the term symbols that occur at the root of a left-hand side of R
     */
    public Set<FunctionSymbol> getDefinedSymbols() {
        final Set<FunctionSymbol> res = new LinkedHashSet<>();
        for (final LCTRSRule rule : this.rules) {
            res.add(rule.left().getRootSymbol());
        }
        return res;
    }

    @Override
    public String export(final Export_Util o) {
        final StringJoiner theories = new StringJoiner(", ");
        this.signature.theories().forEach(theory -> theories.add(theory.getSmtName()));
        final List<String> lines = new ArrayList<>();
        lines.add(o.escape("LCTRS dependency pair problem over " + theories));
        if (!this.signature.userTheorySymbols().isEmpty()) {
            lines.add("User-defined theory symbols:");
            for (final LCTRSUserTheorySymbol userSymbol : this.signature.userTheorySymbols().values()) {
                lines.add(userSymbol.export(o, this.signature));
            }
        }
        lines.add("Signature:");
        this.signature.functions().forEach((f, declaration) -> lines.add(o.escape(f.getName() + " : " + declaration)));
        lines.add(this.pairs.isEmpty() ? "P is empty." : "Pairs:");
        this.pairs.forEach(pair -> lines.add(pair.export(o, this.signature)));
        lines.add(this.rules.isEmpty() ? "R is empty." : "Rules:");
        this.rules.forEach(rule -> lines.add(rule.export(o, this.signature)));
        return String.join(o.linebreak(), lines) + o.linebreak();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Finiteness");
    }

    @Override
    public String getStrategyName() {
        return "lctrsdp";
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

}
