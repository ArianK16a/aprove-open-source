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
 * Converts an IDPProblem to a smaller IDPProblem where only integer positions
 * remain.
 *
 * This is done by removing positions whose type is integer.
 */
public class IDPRemoveTermProcessor extends IDPProcessor {
    // ================================================================================
    // Properties
    // ================================================================================

    private final UserStrategy strategy;
    private final int time;
    private final static Logger log = Logger
            .getLogger("aprove.DPFramework.IDPProblem.Processors.IDPRemoveTermProcessor");
    private CollectionMap<Rule, Node> inverseNodes = new CollectionMap<>();
    private Map<Node, Node> nodeMap = new LinkedHashMap<>();

    // ================================================================================
    // Constructors and Creators
    // ================================================================================
    @ParamsViaArgumentObject
    public IDPRemoveTermProcessor(final Arguments arguments) {
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
        final Set<GeneralizedRule> rules = new LinkedHashSet<>();

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
                if (argTypes.get(i) != Type.Nats && argTypes.get(i) != Type.Bool) {
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
                // if the rhs includes variables not occurring in the lhs, the
                // rule must have the form f(x_1, ..., x_n) -> v where x_i != v
                // because if f would occur inside another term it would also be
                // removed due to it being an integer or boolean position of the
                // function symbol it occurs under
                continue;
            }
            final Rule rule = Rule.create(newL, newR);

            rules.add(rule);
        }

        // Apply filter to Q terms
        final Set<TRSFunctionApplication> qTerms = new LinkedHashSet<TRSFunctionApplication>(explicitOrigQTerms.size());
        for (final TRSFunctionApplication origQTerm : explicitOrigQTerms) {
            final TRSFunctionApplication newQTerm = (TRSFunctionApplication) HelperClass.remove(origQTerm, filter,
                    freshNameMap, takenSymbols, predefinedMap);
            qTerms.add(newQTerm);
        }
        
        final IQTermSet newIqTermSet = new IQTermSet(new QTermSet(qTerms), predefinedMap);

        // Create new idp graph
        final Set<Node> newIdpNodes = new LinkedHashSet<>();
        final Set<IdpEdge> newIdpEdges = new LinkedHashSet<>();
        int maxNodeId = 0;
        for (final Node node : iDP.getIdpGraph().getNodes()) {
            final GeneralizedRule rule = node.getRule();
            
            final TRSFunctionApplication newL = (TRSFunctionApplication) HelperClass.remove(rule.getLeft(), filter,
                    freshNameMap, takenSymbols, predefinedMap);
            final TRSTerm newR = HelperClass.remove(rule.getRight(), filter, freshNameMap, takenSymbols, predefinedMap);

            final Node newNode = new Node(Rule.create(newL, newR), node.id, node.loopSubstitution);
            newIdpNodes.add(newNode);
            nodeMap.put(node, newNode);
            if (node.id > maxNodeId) {
                maxNodeId = node.id;
            }
        }
        
        for (final IdpEdge edge : iDP.getIdpGraph().getEdges()) {
            final IdpEdge newEdge = IdpEdge.create(nodeMap.get(edge.getFrom()), nodeMap.get(edge.getTo()), edge.getItpf(), this);
            newIdpEdges.add(newEdge);
        }
        
        final RuleAnalysis<GeneralizedRule> newRuleAnalysis = new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(rules), predefinedMap);
        
        final IIDependencyGraph newIdpGraph = IDependencyGraph.create(newRuleAnalysis, ImmutableCreator.create(newIdpNodes), ImmutableCreator.create(newIdpEdges), maxNodeId, null, this);

        final IDPProblem newIdpProblem = IDPProblem.create(newIdpGraph, newRuleAnalysis, newIqTermSet, iDP.isMinimal());

        return ResultFactory.proved(newIdpProblem, YNMImplication.SOUND, new IDPRemoveTermProof(newIdpProblem, filter));

//        return ResultFactory.unsuccessful();
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

    public class IDPRemoveTermProof extends DefaultProof implements DOT_Able {
        private final IDPProblem idp;
        private final CollectionMap<FunctionSymbol, Integer> filter;
        /** Obligation node where substrategy has been applied. */

        public IDPRemoveTermProof(final IDPProblem idp, final CollectionMap<FunctionSymbol, Integer> filter) {
            this.idp = idp;
            this.filter = filter;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("The following positions were removed because their type is not integer:");
            result.append(o.linebreak());
            for (Entry<FunctionSymbol, Collection<Integer>> entry : this.filter.entrySet()) {
                result.append(
                        "function symbol: " + entry.getKey().getName() + ", removed positions: " + entry.getValue());
                result.append(o.cond_linebreak());
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
