/**
 *
 * @author 
 * @version $Id$
 */

package aprove.DPFramework.IDPProblem.Processors;

import immutables.Immutable.*;

import java.util.*;
import java.util.Map.*;
import java.util.logging.*;

import aprove.Complexity.LowerBounds.Types.*;
import aprove.DPFramework.*;
import aprove.DPFramework.BasicStructures.*;
import aprove.DPFramework.DPProblem.*;
import aprove.DPFramework.IDPProblem.*;
import aprove.DPFramework.IDPProblem.PfManager.*;
import aprove.DPFramework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.DPFramework.IDPProblem.idpGraph.*;
import aprove.DPFramework.IDPProblem.idpGraph.Node;
import aprove.DPFramework.IDPProblem.utility.*;
import aprove.DPFramework.TRSProblem.*;
import aprove.Framework.BasicStructures.*;
import aprove.Framework.IRSwT.Processors.FilterProcessors.IRSwTTempSortFilterProcessor.*;
import aprove.Framework.IntTRS.*;
import aprove.Framework.Logic.*;
import aprove.Framework.Utility.*;
import aprove.Framework.Utility.GenericStructures.*;
import aprove.Framework.Utility.Graph.*;
import aprove.GraphUserInterface.Factories.Solvers.*;
import aprove.Probabilistic.Termination.ADPProblem.AST.Processors.AST_ADPReductionPairProcessor.*;
import aprove.ProofTree.Export.*;
import aprove.ProofTree.Export.Utility.*;
import aprove.ProofTree.Obligations.*;
import aprove.ProofTree.Proofs.Proof.DefaultProof;
import aprove.Strategies.Abortions.*;
import aprove.Strategies.Annotations.*;
import aprove.Strategies.ExecutableStrategies.*;
import aprove.Strategies.UserStrategies.*;

/**
 * Converts an ITRSProblem to an QTRSProblem.
 *
 * This is done by removing positions whose type is integer.
 */
public class IDPRemoveIntProcessor extends IDPProcessor {
    // ================================================================================
    // Properties
    // ================================================================================

    private final UserStrategy strategy;
    private final int time;
    private final static Logger log = Logger
            .getLogger("aprove.DPFramework.IDPProblem.Processors.IDPRemoveIntProcessor");
    private Map<Rule, Node> inverseNodes = new LinkedHashMap<>();

    // ================================================================================
    // Constructors and Creators
    // ================================================================================
    @ParamsViaArgumentObject
    public IDPRemoveIntProcessor(final Arguments arguments) {
        this.strategy = arguments.strategy;
        this.time = arguments.time;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    /**
     * Checks if this processor is applicable to the IDP.
     */
    @Override
    public boolean isIDPApplicable(final IDPProblem iDP) {

        // TODO
        // Currently, we rely on sane updates to the node labels
        // by the processors and on the edge labels containing
        // (rhs(source) ->^* lhs(target)) as conjuncts to be able to switch
        // from IDP to QDP by dropping edge labels. In case some processor
        // appears in the history that does not satisfy this property, we need
        // to revise the applicability check.

        final IDPRuleAnalysis ruleA = iDP.getRuleAnalysis();

        return !ruleA.hasBitwiseOps();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter) throws AbortionException {
        final Set<Rule> rules = new LinkedHashSet<Rule>();

        final ImmutableSet<TRSFunctionApplication> explicitOrigQTerms = iDP.getQ().getExplicitTerms();
        final ImmutableSet<GeneralizedRule> idpPRules = iDP.getP();
        final ImmutableSet<GeneralizedRule> idpRRules = iDP.getR();
        final IDPPredefinedMap predefinedMap = iDP.getRuleAnalysis().getPreDefinedMap();

        // Build the filter which collects all integer positions
        Set<GeneralizedRule> allRules = new LinkedHashSet<GeneralizedRule>();
        allRules.addAll(idpRRules);
        allRules.addAll(idpPRules);

        TrsTypes types = runTypeInference(allRules);
        CollectionMap<FunctionSymbol, Integer> filter = new CollectionMap<FunctionSymbol, Integer>();
        for (final FunctionSymbol sym : CollectionUtils.getFunctionSymbols(allRules)) {
            List<Type> argTypes = types.getArgumentTypes(sym);
            for (int i = 0; i < argTypes.size(); i++) {
                if (argTypes.get(i) == Type.Nats || argTypes.get(i) == Type.Bool) {
                    filter.add(sym, i);
                }
            }
        }

        final Set<HasFunctionSymbols> forbiddenSymbols = new LinkedHashSet<HasFunctionSymbols>();
        forbiddenSymbols.addAll(explicitOrigQTerms);
        forbiddenSymbols.addAll(idpPRules);
        forbiddenSymbols.addAll(idpRRules);
        final Set<FunctionSymbol> takenSymbols = CollectionUtils.getFunctionSymbols(forbiddenSymbols);

        final Map<FunctionSymbol, FunctionSymbol> freshNameMap = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

        // Apply filter to R rules
        for (final GeneralizedRule r : idpRRules) {
            final TRSFunctionApplication newL = (TRSFunctionApplication) HelperClass.remove(r.getLeft(), filter,
                    freshNameMap, takenSymbols, predefinedMap);
            final TRSTerm newR = HelperClass.remove(r.getRight(), filter, freshNameMap, takenSymbols, predefinedMap);

            if (!newL.getVariables().containsAll(newR.getVariables())) {
                return null;
            }
            final Rule rule = Rule.create(newL, newR);

            rules.add(rule);
        }

        final Graph<Rule, ?> qdpGraph = this.createQDPGraph(iDP, freshNameMap, takenSymbols, filter);
        if (qdpGraph == null) {
            return null;
        }

        // Apply filter to Q terms
        final Set<TRSFunctionApplication> qTerms = new LinkedHashSet<TRSFunctionApplication>(explicitOrigQTerms.size());
        for (final TRSFunctionApplication origQTerm : explicitOrigQTerms) {
            final TRSFunctionApplication newQTerm = (TRSFunctionApplication) HelperClass.remove(origQTerm, filter,
                    freshNameMap, takenSymbols, predefinedMap);
            qTerms.add(newQTerm);
        }

        QTRSProblem qtrsProblem = QTRSProblem.create(ImmutableCreator.create(rules), qTerms);
        final QDPProblem qDP = QDPProblem.create(qdpGraph, qtrsProblem, iDP.isMinimal());
        if (qDP == null) {
            return ResultFactory.unsuccessful();
        }

        final BasicObligationNode newOblNode = new BasicObligationNode(qDP);

        final Abortion childAbortion = aborter.createChild(this.time);
        final StrategyExecutionHandle handle = Machine.theMachine.startSubMachine(this.strategy, this.rti.getProgram(),
                newOblNode, null, childAbortion.getClocks(), false);

        try {
            handle.waitForFinish();
        } catch (final InterruptedException e) {
            throw new AbortionException("IDPRemoveIntProcessor interrupted: " + e.getMessage());
        }

        if (handle.isFinished()) {
            final ExecutableStrategy execStrat = handle.getResult();

            if (execStrat != null && !execStrat.isFail() && execStrat instanceof Success) {
                final Success s = (Success) execStrat;
                final ImmutableList<BasicObligationNode> positions = s.getPositions();

                if (positions.isEmpty() && !newOblNode.getTruthValue().equals(YNM.YES)) {
                    return ResultFactory.unsuccessful("Could not remove any rules!");
                }

                final LinkedHashSet<Node> newIdpNodes = new LinkedHashSet<>();
                for (final BasicObligationNode bon : positions) {
                    final BasicObligation bo = bon.getBasicObligation();
                    QDPProblem newQDP = ((QDPProblem) bo);

                    for (final Rule r : newQDP.getP()) {
                        newIdpNodes.add(this.inverseNodes.get(r));
                    }

                    IIDependencyGraph newIdpGraph = iDP.getIdpGraph().restrictToNodes(newIdpNodes, YNM.MAYBE, this);
                    final IDPProblem newIdp = IDPProblem.create(newIdpGraph, newIdpGraph.getNodeAnalysis(), iDP.getQ(),
                            iDP.isMinimal());

                    boolean done = newIdpNodes.isEmpty();

                    final IDPRemoveIntProof proof = new IDPRemoveIntProof(newIdp, filter, newOblNode, done);

                    if (done) {
                        newOblNode.recursiveRepropagateTruthValues();
                        final ExecutableStrategy succStrategy = Success.EMPTY;
                        return ResultFactory.provedWithNewStrategy(newOblNode, YNMImplication.SOUND, proof,
                                succStrategy);

                    } else {
                        return ResultFactory.proved(newIdp, YNMImplication.SOUND, proof);
                    }

                }
            }
        }

        return ResultFactory.unsuccessful();
    }

    /**
     * create QDP graph from IDP graph
     * 
     * @param takenSymbols
     * @param freshNameMap
     * @param filter
     */
    private Graph<Rule, ?> createQDPGraph(final IDPProblem iDP, final Map<FunctionSymbol, FunctionSymbol> freshNameMap,
            final Set<FunctionSymbol> takenSymbols, final CollectionMap<FunctionSymbol, Integer> filter) {
        final Graph<Rule, ?> qdpGraph = new Graph<Rule, Void>();
        final IIDependencyGraph idpGraph = iDP.getIdpGraph();
        final ImmutableSet<Node> idpNodes = idpGraph.getNodes();
        final ImmutableSet<IdpEdge> idpEdges = idpGraph.getEdges();
        final IDPPredefinedMap predefinedMap = iDP.getRuleAnalysis().getPreDefinedMap();

        final Map<Node, aprove.Framework.Utility.Graph.Node<Rule>> i2qNodes = new LinkedHashMap<Node, aprove.Framework.Utility.Graph.Node<Rule>>(
                idpNodes.size());

        for (final Node idpNode : idpNodes) {
            final TRSFunctionApplication newLhs = (TRSFunctionApplication) HelperClass.remove(idpNode.rule.getLeft(),
                    filter, freshNameMap, takenSymbols, predefinedMap);
            final TRSTerm newRhs = HelperClass.remove(idpNode.rule.getRight(), filter, freshNameMap, takenSymbols,
                    predefinedMap);
            if (!newLhs.getVariables().containsAll(newRhs.getVariables())) {
                return null;
            }
            final Rule qdpRule = Rule.create(newLhs, newRhs);
            final aprove.Framework.Utility.Graph.Node<Rule> qdpNode = new aprove.Framework.Utility.Graph.Node<Rule>(
                    qdpRule);
            i2qNodes.put(idpNode, qdpNode);
            qdpGraph.addNode(qdpNode);
            this.inverseNodes.put(qdpRule, idpNode);
        }

        for (final IdpEdge edge : idpEdges) {
            qdpGraph.addEdge(i2qNodes.get(edge.getFrom()), i2qNodes.get(edge.getTo()));
        }
        return qdpGraph;
    }

    private TrsTypes runTypeInference(final Set<GeneralizedRule> rules) {
        Set<FunctionSymbol> allSymbols = CollectionUtils.getFunctionSymbols(rules);
        Set<FunctionSymbol> definedSymbols = CollectionUtils.getRootSymbols(rules);

        // Predefined symbols don't occur as root symbols but are defined too
        for (final FunctionSymbol fun : allSymbols) {
            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(fun)) {
                definedSymbols.add(fun);
            }
        }

        // Convert the rules to the type expected for TypeInference
        Set<aprove.Complexity.LowerBounds.BasicStructures.Rule> newRules = new LinkedHashSet<>();
        for (final GeneralizedRule rule : rules) {
            newRules.add(new aprove.Complexity.LowerBounds.BasicStructures.Rule(rule.getLeft(), rule.getRight()));
        }

        return TypeInference.infer(newRules, allSymbols, definedSymbols);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public class IDPRemoveIntProof extends DefaultProof implements DOT_Able {
        private final IDPProblem idp;
        private final CollectionMap<FunctionSymbol, Integer> filter;
        /** Obligation node where substrategy has been applied. */
        private final BasicObligationNode subBon;
        private final boolean done;

        public IDPRemoveIntProof(final IDPProblem idp, final CollectionMap<FunctionSymbol, Integer> filter,
                BasicObligationNode bon, boolean done) {
            this.idp = idp;
            this.filter = filter;
            this.subBon = bon;
            this.done = done;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("The following positions were removed because their type is integer:");
            result.append(o.linebreak());
            for (Entry<FunctionSymbol, Collection<Integer>> entry : this.filter.entrySet()) {
                result.append(
                        "function symbol: " + entry.getKey().getName() + ", removed positions: " + entry.getValue());
                result.append(o.cond_linebreak());
            }
            if (!done) {
                result.append("The following proof was generated: ");
                final GenericExportManager subproof = new GenericExportManager(IDPRemoveIntProof.this.subBon,
                        "filtering result", false);
                result.append(o.preFormatted(subproof.export(new PLAIN_Util())));
            }

            return result.toString();
        }

        @Override
        public String toDOT() {
            return this.idp.getIdpGraph().toDOT();
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

    public static class Arguments {
        /** Strategy to execute. */
        UserStrategy strategy;

        /** Time to live! */
        int time = 42042;

        public void setStrategy(final String strategyName) {
            this.strategy = new VariableStrategy(strategyName);
        }

        public void setTime(final int timeVal) {
            this.time = timeVal;
        }
    }
}
