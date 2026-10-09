package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;
import java.util.function.*;

import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Result of converting an IDP problem into another problem whose rules can be
 * traced back to the nodes of the IDP graph.
 *
 * @param <R>
 *            the rule type of the target problem
 */
public final class IDPConversion<R> {

    private final BasicObligation target;
    private final CollectionMap<R, Node> origin;
    private final Function<BasicObligation, Collection<? extends R>> remainingRules;
    private final Proof proof;

    /**
     * @param target
     *            the converted problem
     * @param origin
     *            maps each rule of the target problem to the IDP nodes it was
     *            created from
     * @param remainingRules
     *            extracts the rules of an obligation derived from
     *            <code>target</code>, or returns <code>null</code> if the
     *            obligation is not of the expected type
     * @param proof
     *            the proof of the conversion step
     */
    public IDPConversion(final BasicObligation target, final CollectionMap<R, Node> origin,
            final Function<BasicObligation, Collection<? extends R>> remainingRules, final Proof proof) {
        this.target = target;
        this.origin = origin;
        this.remainingRules = remainingRules;
        this.proof = proof;
    }

    public BasicObligation getTarget() {
        return this.target;
    }

    public Proof getProof() {
        return this.proof;
    }

    /**
     * Collects the IDP nodes of all rules that remain in the given obligations.
     *
     * @return the IDP nodes, or <code>null</code> if some obligation or rule
     *         cannot be traced back to the IDP, e.g. because a processor
     *         rewrote a rule instead of deleting it
     */
    public Set<Node> getOriginNodes(final Collection<BasicObligationNode> obligations) {
        final Set<Node> nodes = new LinkedHashSet<>();
        for (final BasicObligationNode bon : obligations) {
            final Collection<? extends R> rules = this.remainingRules.apply(bon.getBasicObligation());
            if (rules == null) {
                return null;
            }
            for (final R rule : rules) {
                final Collection<Node> ruleNodes = this.origin.get(rule);
                if (ruleNodes == null || ruleNodes.isEmpty()) {
                    return null;
                }
                nodes.addAll(ruleNodes);
            }
        }
        return nodes;
    }
}
