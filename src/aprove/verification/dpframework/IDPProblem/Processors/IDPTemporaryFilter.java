package aprove.verification.dpframework.IDPProblem.Processors;

import immutables.*;

import java.util.*;

import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Temporarily converts an IDP problem into another problem, runs a strategy on
 * it and removes those IDP nodes whose rules were deleted by that strategy.
 */
public final class IDPTemporaryFilter {

    private IDPTemporaryFilter() {
    }

    /**
     * @param iDP
     *            the original problem
     * @param conversion
     *            the converted problem with a mapping back to the IDP nodes
     * @param strategy
     *            the strategy to run on the converted problem; it should only
     *            delete rules
     * @param time
     *            time limit for the strategy
     * @param processor
     *            the processor performing the filtering
     */
    public static Result run(final IDPProblem iDP, final IDPConversion<?> conversion, final UserStrategy strategy,
            final int time, final Abortion aborter, final RuntimeInformation rti, final IDPProcessor processor)
            throws AbortionException {
        final BasicObligationNode newOblNode = new BasicObligationNode(conversion.getTarget());

        final Abortion childAbortion = aborter.createChild(time);
        final StrategyExecutionHandle handle = Machine.theMachine.startSubMachine(strategy, rti.getProgram(),
                newOblNode, null, childAbortion.getClocks(), false);

        try {
            handle.waitForFinish();
        } catch (final InterruptedException e) {
            throw new AbortionException(processor.getClass().getSimpleName() + " interrupted: " + e.getMessage());
        }

        if (!handle.isFinished()) {
            return ResultFactory.unsuccessful();
        }
        final ExecutableStrategy execStrat = handle.getResult();
        if (execStrat == null || execStrat.isFail() || !(execStrat instanceof Success)) {
            return ResultFactory.unsuccessful();
        }

        if (newOblNode.getTruthValue().equals(YNM.YES)) {
            return ResultFactory.provedWithNewStrategy(newOblNode, YNMImplication.SOUND, conversion.getProof(),
                    Success.EMPTY);
        }

        final ImmutableList<BasicObligationNode> positions = ((Success) execStrat).getPositions();
        if (positions.isEmpty()) {
            return ResultFactory.unsuccessful("Could not remove any rules!");
        }

        // The remaining nodes are those of all open obligations together
        final Set<Node> remainingNodes = conversion.getOriginNodes(positions);
        if (remainingNodes == null) {
            return ResultFactory.unsuccessful("Could not map the remaining rules back to the IDP!");
        }
        if (remainingNodes.containsAll(iDP.getIdpGraph().getNodes())) {
            return ResultFactory.unsuccessful("Could not remove any rules!");
        }

        if (remainingNodes.isEmpty()) {
            newOblNode.recursiveRepropagateTruthValues();
            return ResultFactory.provedWithNewStrategy(newOblNode, YNMImplication.SOUND, conversion.getProof(),
                    Success.EMPTY);
        }

        final IDPPredefinedMap predefinedMap = iDP.getRuleAnalysis().getPreDefinedMap();
        final IIDependencyGraph newIdpGraph = iDP.getIdpGraph().restrictToNodes(remainingNodes, YNM.MAYBE,
                processor);
        final IDPProblem newIdp = IDPProblem.create(newIdpGraph,
                new RuleAnalysis<GeneralizedRule>(iDP.getR(), predefinedMap), iDP.getQ(), iDP.isMinimal());
        return ResultFactory.proved(newIdp, YNMImplication.SOUND,
                new IDPTemporaryFilterProof(conversion.getProof(), newOblNode));
    }

    /**
     * Proof of a temporary filtering step: the conversion proof together with
     * the proof generated on the converted problem.
     */
    public static class IDPTemporaryFilterProof extends DefaultProof {
        private final Proof conversionProof;

        /** Obligation node where the strategy has been applied. */
        private final BasicObligationNode subBon;

        public IDPTemporaryFilterProof(final Proof conversionProof, final BasicObligationNode subBon) {
            this.conversionProof = conversionProof;
            this.subBon = subBon;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();

            result.append(this.conversionProof.export(o, level));
            result.append(o.cond_linebreak());

            result.append("The following proof was generated: ");
            final GenericExportManager subproof = new GenericExportManager(this.subBon, "filtering result", false);
            result.append(o.preFormatted(subproof.export(new PLAIN_Util())));

            return result.toString();
        }
    }
}
