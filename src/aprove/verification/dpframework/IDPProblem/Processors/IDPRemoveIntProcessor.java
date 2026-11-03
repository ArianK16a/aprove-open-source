package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.Node;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Converts an IDP into a QDP by removing all integer and boolean arguments,
 * see {@link IDPProjection}. This helps if termination does not depend on the
 * integers, and it also works with restricted integers and bitwise
 * operations. The result is only SOUND.
 *
 * <p>Unless only arguments of tuple symbols are removed, the QDP is analysed
 * for full termination and it is not minimal.</p>
 *
 * <p>With <code>TempFilter</code>, the QDP is only used to remove nodes from
 * the IDP, see {@link IDPTemporaryFilter}.</p>
 */
public class IDPRemoveIntProcessor extends IDPProcessor {

    private final boolean tempFilter;
    private final UserStrategy strategy;
    private final int time;

    @ParamsViaArgumentObject
    public IDPRemoveIntProcessor(final Arguments arguments) {
        this.tempFilter = arguments.tempFilter;
        this.strategy = arguments.strategy;
        this.time = arguments.time;
    }

    /**
     * Applicable to every IDP, as restricted integers and bitwise operations
     * are removed.
     */
    @Override
    public boolean isIDPApplicable(final IDPProblem iDP) {
        return true;
    }

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter) {
        // Not used, as process passes the runtime information
        throw new UnsupportedOperationException();
    }

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {
        final IDPProjection projection = IDPProjection.removeIntsAndBools(iDP);
        if (projection == null) {
            return ResultFactory.unsuccessful("The IDP is not well-typed.");
        }
        if (projection.isIdentity()) {
            // The QDP would be the same as the one of IDPtoQDP
            return ResultFactory.unsuccessful("There are no integer or boolean arguments.");
        }
        final IDPConversion<Rule> conversion = IDPRemoveIntProcessor.toQDP(iDP, projection);
        if (conversion == null) {
            return ResultFactory.unsuccessful("A free variable remains after the removal.");
        }
        if (!this.tempFilter) {
            return ResultFactory.proved(conversion.getTarget(), YNMImplication.SOUND, conversion.getProof());
        }
        return IDPTemporaryFilter.run(iDP, conversion, this.strategy, this.time, aborter, rti, this);
    }

    /**
     * @return the QDP together with the mapping back to the IDP nodes, or
     *         <code>null</code> if a rule has a free variable
     */
    private static IDPConversion<Rule> toQDP(final IDPProblem iDP, final IDPProjection projection) {
        final Set<Rule> rules = new LinkedHashSet<Rule>();
        for (final GeneralizedRule rule : projection.getRules()) {
            if (!rule.getLeft().getVariables().containsAll(rule.getRight().getVariables())) {
                return null;
            }
            rules.add(Rule.create(rule.getLeft(), rule.getRight()));
        }

        // The pairs keep the edges of the IDP graph
        final CollectionMap<Rule, Node> inverseNodes = new CollectionMap<>();
        final Graph<Rule, ?> graph = new Graph<Rule, Void>();
        final IIDependencyGraph idpGraph = iDP.getIdpGraph();
        final Map<Node, aprove.verification.oldframework.Utility.Graph.Node<Rule>> graphNodes = new LinkedHashMap<>();
        for (final Map.Entry<Node, GeneralizedRule> entry : projection.getPairs().entrySet()) {
            final GeneralizedRule pair = entry.getValue();
            if (!pair.getLeft().getVariables().containsAll(pair.getRight().getVariables())) {
                return null;
            }
            final Rule rule = Rule.create(pair.getLeft(), pair.getRight());
            final aprove.verification.oldframework.Utility.Graph.Node<Rule> graphNode =
                new aprove.verification.oldframework.Utility.Graph.Node<Rule>(rule);
            graphNodes.put(entry.getKey(), graphNode);
            graph.addNode(graphNode);
            inverseNodes.add(rule, entry.getKey());
        }
        for (final Node node : idpGraph.getNodes()) {
            for (final Node succ : idpGraph.getSuccessors(node).keySet()) {
                graph.addEdge(graphNodes.get(node), graphNodes.get(succ));
            }
        }

        final Set<TRSFunctionApplication> qTerms = projection.isInnermost()
            ? iDP.getQ().getExplicitTerms() : new LinkedHashSet<TRSFunctionApplication>();
        final QDPProblem qDP = QDPProblem.create(graph,
                QTRSProblem.create(ImmutableCreator.create(rules), qTerms),
                iDP.isMinimal() && projection.isInnermost());
        if (qDP == null) {
            return null;
        }
        return new IDPConversion<>(qDP, inverseNodes,
                obl -> obl instanceof QDPProblem ? ((QDPProblem) obl).getP() : null,
                new IDPRemoveIntProof(projection));
    }

    public static class IDPRemoveIntProof extends DefaultProof {
        private final IDPProjection projection;

        public IDPRemoveIntProof(final IDPProjection projection) {
            this.projection = projection;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder(this.projection.export(o));
            if (!this.projection.isInnermost()) {
                result.append("As arguments below the root of the pairs were removed, ");
                result.append("the QDP is analysed for full termination.");
            }
            return result.toString();
        }
    }

    public static class Arguments {
        /**
         * Whether the QDP is only used to remove nodes from the IDP. If true,
         * `strategy` is executed on the QDP and the nodes whose pairs it
         * removed are removed from the IDP. If false, the QDP is returned.
         */
        boolean tempFilter = false;

        /** Strategy to execute on the QDP if `tempFilter` is set. */
        UserStrategy strategy;

        /** Time limit for `strategy`. */
        int time = 42042;

        public void setTempFilter(final boolean tempFilter) {
            this.tempFilter = tempFilter;
        }

        public void setStrategy(final String strategyName) {
            this.strategy = new VariableStrategy(strategyName);
        }

        public void setTime(final int timeVal) {
            this.time = timeVal;
        }
    }
}
