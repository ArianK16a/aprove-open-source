/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfManager.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.Node;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/** Converts an ITRSProblem to an QTRSProblem.
 *
 * This is done by converting integers (and the predefined functions)
 * to a pos-neg representation.
 *
 * With <code>TempFilter</code>, the QDP is only used to remove nodes from the
 * IDP, see {@link IDPTemporaryFilter}.
 */
public class IDPtoQDPProcessor extends IDPProcessor {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.IDPProblem.Processors.IDPtoQDPProcessor");

    /**
     * On which IDP problems do we want to be applicable?
     */
    private final ToTermApplicability apply;

    /**
     * What is the highest absolute value of an integer literal allowed for
     * explicit conversion?
     */
    private final int limit;

    private final boolean tempFilter;
    private final UserStrategy strategy;
    private final int time;

    @ParamsViaArgumentObject
    public IDPtoQDPProcessor(final Arguments arguments) {
        this.apply = arguments.apply;
        this.limit = arguments.limit;
        this.tempFilter = arguments.tempFilter;
        this.strategy = arguments.strategy;
        this.time = arguments.time;
    }

    /** Checks if this processor is applicable to the IDP.
     *
     * At the moment, this is true for all IDP containing only integers
     * over the mathematical integers Z.
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
        switch (this.apply) {
        case NOPREDEFS: {
            if (! (ruleA.getPAnalysis().getPredefinedFunctions().isEmpty() &&
                   ruleA.getRAnalysis().getPredefinedFunctions().isEmpty())) {
                return false;
            }
            break;
        }
        case CONSTONLY: {
            if (ruleA.hasPredefinedDefSymbols()) {
                return false;
            }
            break;
        }
        case ALWAYS: {
            break;
        }
        case ALWAYSFILTER: {
            break;
        }
        default:
            throw new aprove.verification.oldframework.Exceptions.NotYetHandledException("Check for "
                    + this.apply + " not handled yet!");
        }
        return !ruleA.hasRestrictedInt()
            && !ruleA.hasBitwiseOps()
            && (this.apply == ToTermApplicability.ALWAYSFILTER || ruleA.satVarCondition());
    }

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter)
            throws AbortionException {
        try {
            final IDPConversion<Rule> conversion = this.IDPtoQDP(iDP);
            if (conversion == null) {
                return ResultFactory.unsuccessful();
            }
            if (!this.tempFilter) {
                return ResultFactory.proved(conversion.getTarget(), YNMImplication.SOUND, conversion.getProof());
            }
            return IDPTemporaryFilter.run(iDP, conversion, this.strategy, this.time, aborter, this.rti, this);
        } catch (final IntOutOfRangeException e) {
            final String message = "Transformation failed, because some integers" +
                    "were too big to be converted into pos/neg notation." +
                    "The offending value was " + e.getOffending() +
                    ", the limit was " + e.getLimit() + ".";
            IDPtoQDPProcessor.log.warning(message);
            return ResultFactory.error(message);
        }
    }

    private IDPConversion<Rule> IDPtoQDP(final IDPProblem iDP)
            throws IntOutOfRangeException {
        // Use linked sets here just for user-friendliness. We want the
        // transformed "real" rules first and the generated rules last.
        final Set<Rule> rules = new LinkedHashSet<Rule>();

        final ImmutableSet<TRSFunctionApplication> explicitOrigQTerms =
            iDP.getQ().getExplicitTerms();

        final ImmutableSet<GeneralizedRule> idpPRules = iDP.getP();
        final ImmutableSet<GeneralizedRule> idpRRules = iDP.getR();
        final IDPPredefinedMap predefinedMap = iDP.getRuleAnalysis().getPreDefinedMap();
        final boolean iDPisMinimal = iDP.isMinimal();

        CollectionMap<FunctionSymbol, Integer> filter = null;
        if (this.apply == ToTermApplicability.ALWAYSFILTER) {
            filter = FreeVariableTermRemover.getPositionFilter(
                    idpPRules, idpRRules, predefinedMap, true, true,
                    Integer.MAX_VALUE);
        }
        if (filter == null) {
            filter = new CollectionMap<FunctionSymbol, Integer>();
        }

        // beware of name clashes
        final Set<HasFunctionSymbols> forbiddenSymbols = new LinkedHashSet<HasFunctionSymbols>();
        forbiddenSymbols.addAll(explicitOrigQTerms);
        forbiddenSymbols.addAll(idpPRules);
        forbiddenSymbols.addAll(idpRRules);

        final PredefinedFunctionsManagerNegPos npMan =
            PredefinedFunctionsManagerNegPos.create(predefinedMap, forbiddenSymbols, this.limit);

        final Map<FunctionSymbol, FunctionSymbol> freshNameMap =
            new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        final Set<FunctionSymbol> takenSymbols =
                CollectionUtils.getFunctionSymbols(forbiddenSymbols);

        for (final GeneralizedRule r : idpRRules) {
            final TRSFunctionApplication newL =
                    (TRSFunctionApplication) npMan.extractTerm(HelperClass.remove(
                            r.getLeft(), filter, freshNameMap, takenSymbols, predefinedMap));
            final TRSTerm newR =
                    npMan.extractTerm(HelperClass.remove(
                            r.getRight(), filter, freshNameMap, takenSymbols, predefinedMap));

            if (!newL.getVariables().containsAll(newR.getVariables())) {
                return null;
            }
            final Rule rule = Rule.create(newL, newR);

            rules.add(rule);
        }

        // Maps each QDP pair back to the IDP nodes it was created from
        final CollectionMap<Rule, Node> inverseNodes = new CollectionMap<>();
        final Graph<Rule, ?> qdpGraph =
            this.createQDPGraph(iDP, npMan, freshNameMap, takenSymbols, filter, inverseNodes);
        if (qdpGraph == null) {
            return null;
        }
        final Set<TRSFunctionApplication> qTerms = this.createQdpQTerms(explicitOrigQTerms, npMan, predefinedMap, freshNameMap, takenSymbols, filter);

        // The generated rules do not add new PAIRS, but we need to add the
        // rules generated for the PAIRS to the RULES section too.
        final Set<Rule> rulesForPredefs = npMan.getGeneratedRules();
        rules.addAll(rulesForPredefs);
        qTerms.addAll(CollectionUtils.getLeftHandSides(rulesForPredefs));

        final QDPProblem qDP = QDPProblem.create(qdpGraph,
                QTRSProblem.create(ImmutableCreator.create(rules), qTerms),
                iDPisMinimal);
        if (qDP == null) {
            return null;
        }
        return new IDPConversion<>(qDP, inverseNodes,
                obl -> obl instanceof QDPProblem ? ((QDPProblem) obl).getP() : null,
                new IDPtoQDPProof(qDP));
    }

    /**
     * creates QTerms for QDPProblem
     * @param predefinedMap
     * @param filter
     * @param takenSymbols
     * @param freshNameMap
     */
    private Set<TRSFunctionApplication> createQdpQTerms(
            final ImmutableSet<TRSFunctionApplication> explicitOrigQTerms,
            final PredefinedFunctionsManagerNegPos npMan,
            final IDPPredefinedMap predefinedMap,
            final Map<FunctionSymbol, FunctionSymbol> freshNameMap,
            final Set<FunctionSymbol> takenSymbols,
            final CollectionMap<FunctionSymbol, Integer> filter)
            throws IntOutOfRangeException {
        // build Q
        final Set<TRSFunctionApplication> qTerms =
            new LinkedHashSet<TRSFunctionApplication>(explicitOrigQTerms.size());

        // postprocess those qTerms by npMan, too
        for (final TRSFunctionApplication origQTerm : explicitOrigQTerms) {
            final TRSFunctionApplication newQTerm =
                    (TRSFunctionApplication) npMan.extractTerm(HelperClass.remove(
                            origQTerm, filter, freshNameMap, takenSymbols, predefinedMap));
            qTerms.add(newQTerm);
        }
        return qTerms;
    }

    /**
     * create QDP graph from IDP graph
     * @param takenSymbols
     * @param freshNameMap
     * @param filter
     * @param inverseNodes is filled with the IDP nodes each QDP pair was created from
     */
    private Graph<Rule, ?> createQDPGraph(final IDPProblem iDP, final PredefinedFunctionsManagerNegPos npMan, final Map<FunctionSymbol, FunctionSymbol> freshNameMap, final Set<FunctionSymbol> takenSymbols, final CollectionMap<FunctionSymbol, Integer> filter, final CollectionMap<Rule, Node> inverseNodes)
            throws IntOutOfRangeException {

        final Graph<Rule, ?> qdpGraph = new Graph<Rule, Void>();
        final IIDependencyGraph idpGraph = iDP.getIdpGraph();
        final ImmutableSet<Node> idpNodes = idpGraph.getNodes();
        final IDPPredefinedMap predefinedMap = iDP.getRuleAnalysis().getPreDefinedMap();

        final Map<Node, aprove.verification.oldframework.Utility.Graph.Node<Rule>> i2qNodes =
            new LinkedHashMap<Node, aprove.verification.oldframework.Utility.Graph.Node<Rule>>(idpNodes.size());

        for (final Node idpNode : idpNodes) {
            final TRSFunctionApplication newLhs =
                    (TRSFunctionApplication) npMan.extractTerm(HelperClass.remove(
                            idpNode.rule.getLeft(), filter, freshNameMap, takenSymbols, predefinedMap));
            final TRSTerm newRhs =
                    npMan.extractTerm(HelperClass.remove(
                            idpNode.rule.getRight(), filter, freshNameMap, takenSymbols, predefinedMap));
            if (!newLhs.getVariables().containsAll(newRhs.getVariables())) {
                return null;
            }
            final Rule qdpRule = Rule.create(newLhs, newRhs);
            final aprove.verification.oldframework.Utility.Graph.Node<Rule> qdpNode =
                new aprove.verification.oldframework.Utility.Graph.Node<Rule>(qdpRule);
            i2qNodes.put(idpNode, qdpNode);
            qdpGraph.addNode(qdpNode);
            inverseNodes.add(qdpRule, idpNode);
        }

        for (final Node idpNode : idpNodes) {
            final ImmutableMap<Node, IdpEdge> succMap =
                idpGraph.getSuccessors(idpNode);
            for(final Node succNode : succMap.keySet()) {
                qdpGraph.addEdge(i2qNodes.get(idpNode), i2qNodes.get(succNode));
            }
        }

        return qdpGraph;
    }


    public class IDPtoQDPProof extends DefaultProof implements DOT_Able {

        private final QDPProblem qdp;

        public IDPtoQDPProof(final QDPProblem qdp) {
            this.qdp = qdp;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            // FIXME: Make a real proof?
            return "Represented integers and predefined function symbols by Terms";
        }

        @Override
        public String toDOT() {
            return this.qdp.getDependencyGraph().toDOT();
        }
    }

    public static class Arguments {
        // when do we want to be applicable?
        public ToTermApplicability apply = ToTermApplicability.ALWAYS;

        // max absolute value of integer literal accepted for conversion
        public int limit = 1023;

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
