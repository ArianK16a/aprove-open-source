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
import aprove.DPFramework.IDPProblem.PfFunctions.*;
import aprove.DPFramework.IDPProblem.PfFunctions.domains.*;
import aprove.DPFramework.IDPProblem.PfManager.*;
import aprove.DPFramework.IDPProblem.Processors.IDPRemoveIntProcessor.*;
import aprove.DPFramework.IDPProblem.Processors.IDPToIRSProcessor.*;
import aprove.DPFramework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.DPFramework.IDPProblem.idpGraph.*;
import aprove.DPFramework.IDPProblem.idpGraph.Node;
import aprove.DPFramework.IDPProblem.utility.*;
import aprove.DPFramework.TRSProblem.*;
import aprove.Framework.BasicStructures.*;
import aprove.Framework.Bytecode.Processors.ToIDPv1.*;
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
    private CollectionMap<IGeneralizedRule, Node> inverseNodes = new CollectionMap<>();
    private Map<Node, Node> nodeMap = new LinkedHashMap<>();
    private Map<Node, Node> inverseNodeMap = new LinkedHashMap<>();

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

        Set<TRSVariable> lockedVariables = new LinkedHashSet<>();

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
            lockedVariables.addAll(rule.getVariables());
            rules.add(rule);
        }

        // Apply filter to Q terms
        final Set<TRSFunctionApplication> qTerms = new LinkedHashSet<TRSFunctionApplication>(explicitOrigQTerms.size());
        for (final TRSFunctionApplication origQTerm : explicitOrigQTerms) {
            final TRSFunctionApplication newQTerm = (TRSFunctionApplication) HelperClass.remove(origQTerm, filter,
                    freshNameMap, takenSymbols, predefinedMap);
            qTerms.add(newQTerm);
            lockedVariables.addAll(newQTerm.getVariables());
        }

        final IQTermSet newIqTermSet = new IQTermSet(new QTermSet(qTerms), predefinedMap);

        // Create new idp graph
        final Set<Node> newIdpNodes = new LinkedHashSet<>();
        final Set<IdpEdge> newIdpEdges = new LinkedHashSet<>();
        final Set<GeneralizedRule> newIdpPRules = new LinkedHashSet<>();
        int maxNodeId = 0;
        for (final Node node : iDP.getIdpGraph().getNodes()) {
            final GeneralizedRule rule = node.getRule();

            final TRSFunctionApplication newL = (TRSFunctionApplication) HelperClass.remove(rule.getLeft(), filter,
                    freshNameMap, takenSymbols, predefinedMap);
            final TRSTerm newR = HelperClass.remove(rule.getRight(), filter, freshNameMap, takenSymbols, predefinedMap);

            final Node newNode = new Node(Rule.create(newL, newR), node.id, node.loopSubstitution);
            newIdpNodes.add(newNode);
            lockedVariables.addAll(newNode.getRule().getVariables());
            newIdpPRules.add(newNode.getRule());
            nodeMap.put(node, newNode);
            inverseNodeMap.put(newNode, node);
            if (node.id > maxNodeId) {
                maxNodeId = node.id;
            }
        }

        for (final IdpEdge edge : iDP.getIdpGraph().getEdges()) {
            final IdpEdge newEdge = IdpEdge.create(nodeMap.get(edge.getFrom()), nodeMap.get(edge.getTo()),
                    edge.getItpf(), this);
            newIdpEdges.add(newEdge);
        }

        final RuleAnalysis<GeneralizedRule> newPRuleAnalysis = new RuleAnalysis<GeneralizedRule>(
                ImmutableCreator.create(newIdpPRules), predefinedMap);

        final RuleAnalysis<GeneralizedRule> newRRuleAnalysis = new RuleAnalysis<GeneralizedRule>(
                ImmutableCreator.create(rules), predefinedMap);

        final IIDependencyGraph newIdpGraph = IDependencyGraph.create(newPRuleAnalysis,
                ImmutableCreator.create(newIdpNodes), ImmutableCreator.create(newIdpEdges), maxNodeId,
                ImmutableCreator.create(lockedVariables), this);

        final IDPProblem newIdpProblem = IDPProblem.create(newIdpGraph, newRRuleAnalysis, newIqTermSet,
                iDP.isMinimal());

        final IRSProblem irsProblem = this.IDPToIRSProblem(newIdpProblem);

        final BasicObligationNode newOblNode = new BasicObligationNode(irsProblem);

        final Abortion childAbortion = aborter.createChild(this.time);
        final StrategyExecutionHandle handle = Machine.theMachine.startSubMachine(this.strategy, this.rti.getProgram(),
                newOblNode, null, childAbortion.getClocks(), false);

        try {
            handle.waitForFinish();
        } catch (final InterruptedException e) {
            throw new AbortionException("IDPRemoveTermProcessor interrupted: " + e.getMessage());
        }

        if (handle.isFinished()) {
            final ExecutableStrategy execStrat = handle.getResult();

            if (execStrat != null && !execStrat.isFail() && execStrat instanceof Success) {
                final Success s = (Success) execStrat;
                final ImmutableList<BasicObligationNode> positions = s.getPositions();

                if (newOblNode.getTruthValue().equals(YNM.YES)) {
                    final IDPRemoveTermProof proof = new IDPRemoveTermProof(newIdpProblem, filter, newOblNode, true);
                    final ExecutableStrategy succStrategy = Success.EMPTY;
                    return ResultFactory.provedWithNewStrategy(newOblNode, YNMImplication.SOUND, proof, succStrategy);
                }
                if (positions.isEmpty()) {
                    return ResultFactory.unsuccessful("Could not remove any rules!");
                }

                final LinkedHashSet<Node> resultingIdpNodes = new LinkedHashSet<>();
                for (final BasicObligationNode bon : positions) {
                    final BasicObligation bo = bon.getBasicObligation();
                    IRSProblem irsResult = ((IRSProblem) bo);

                    for (final IGeneralizedRule r : irsResult.getRules()) {
                        resultingIdpNodes.addAll(this.inverseNodes.get(r));
                    }

                    if (resultingIdpNodes.containsAll(iDP.getIdpGraph().getNodes())) {
                        return ResultFactory.unsuccessful("Could not remove any rules!");
                    }

                    IIDependencyGraph resultingIdpGraph = iDP.getIdpGraph().restrictToNodes(resultingIdpNodes,
                            YNM.MAYBE, this);
                    final IDPProblem newIdp = IDPProblem.create(resultingIdpGraph,
                            new RuleAnalysis<GeneralizedRule>(idpRRules, predefinedMap), iDP.getQ(), iDP.isMinimal());

                    boolean done = resultingIdpNodes.isEmpty();

                    final IDPRemoveTermProof proof = new IDPRemoveTermProof(newIdp, filter, newOblNode, done);

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

        // return ResultFactory.proved(newIdpProblem, YNMImplication.SOUND, new
        // IDPRemoveTermProof(newIdpProblem, filter, newOblNode, false));

        return ResultFactory.unsuccessful();
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

    private class ArithmeticElimination {
        public TRSTerm condition;
        public TRSTerm replacement;

        public ArithmeticElimination(TRSTerm condition, TRSTerm replacement) {
            this.condition = condition;
            this.replacement = replacement;
        }
    }

    /**
     * 
     * @param term
     * @return the constraint necessary to replace term by
     */
    private ArithmeticElimination eliminateNestedArithmetic(TRSTerm term, FreshNameGenerator fng) {
        if (term instanceof TRSVariable) {
            return new ArithmeticElimination(null, term);
        }

        TRSVariable var = TRSTerm.createVariable(fng.getFreshName(term.getName(), false));
        // If any nested function symbol is not pre-defined, return a free
        // variable
        for (FunctionSymbol symbol : term.getFunctionSymbols()) {
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(symbol)) {
                return new ArithmeticElimination(null, var);
            }
        }

        assert term instanceof TRSFunctionApplication;
        TRSFunctionApplication funApp = (TRSFunctionApplication) term;
        assert IDPPredefinedMap.DEFAULT_MAP.isPredefined(funApp.getFunctionSymbol());

        // +(a,b)...
        if (IDPPredefinedMap.DEFAULT_MAP.isArithmeticFunction(funApp.getFunctionSymbol())) {
            // the new variables used in the constraint
            List<TRSTerm> newArgs = new ArrayList<>();
            List<TRSTerm> subConstraints = new ArrayList<>();

            for (TRSTerm arg : funApp.getArguments()) {
                ArithmeticElimination childElim = this.eliminateNestedArithmetic(arg, fng);
                newArgs.add(childElim.replacement);
                if (childElim.condition != null) {
                    subConstraints.add(childElim.condition);
                }
            }

            TRSTerm constraintRhs = TRSTerm.createFunctionApplication(funApp.getRootSymbol(), newArgs);

            TRSTerm constraint = TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    constraintRhs);

            for (TRSTerm subConstraint : subConstraints) {
                constraint = IDPv2ToIDPv1Utilities.getConjunction(constraint, subConstraint);
            }
            return new ArithmeticElimination(constraint, var);
        }

        // >(a,b)...
        if (IDPPredefinedMap.DEFAULT_MAP.isIntegerRelation(funApp.getFunctionSymbol())) {
            // replace with constant true or false and add appropriate
            // condition

            // the new variables used in the constraint
            List<TRSTerm> newArgs = new ArrayList<>();
            List<TRSTerm> subConstraints = new ArrayList<>();

            for (TRSTerm arg : funApp.getArguments()) {
                ArithmeticElimination childElim = this.eliminateNestedArithmetic(arg, fng);
                newArgs.add(childElim.replacement);
                if (childElim.condition != null) {
                    subConstraints.add(childElim.condition);
                }
            }

            TRSTerm constraint = TRSTerm.createFunctionApplication(funApp.getRootSymbol(), newArgs);

            for (TRSTerm subConstraint : subConstraints) {
                constraint = IDPv2ToIDPv1Utilities.getConjunction(constraint, subConstraint);
            }

            // TODO also add false with negated condition?
            return new ArithmeticElimination(constraint, IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getTerm());
        }

        // 6, 7,...
        if (IDPPredefinedMap.DEFAULT_MAP.isInt(funApp.getFunctionSymbol(), DomainFactory.INTEGERS)) {
            return new ArithmeticElimination(null, term);
        }

        return new ArithmeticElimination(null, var);
    }

    private final IRSProblem IDPToIRSProblem(final IDPProblem iDP) {
        final Set<IGeneralizedRule> rules = new LinkedHashSet<>();
        Set<String> usedNames = new LinkedHashSet<>();
        usedNames.addAll(CollectionUtils.getNames(CollectionUtils.getFunctionSymbols(iDP.getP())));
        usedNames.addAll(CollectionUtils.getNames(CollectionUtils.getVariables(iDP.getP())));
        FreshNameGenerator fng = new FreshNameGenerator(usedNames, FreshNameGenerator.APPEND_NUMBERS);

        // transform iDP to rules with no nested functions but with conditions
        for (Node node : iDP.getIdpGraph().getNodes()) {
            final GeneralizedRule rule = node.getRule();
            List<TRSTerm> args = new ArrayList<>();
            TRSTerm condition = null;

            if (rule.getRight() instanceof TRSFunctionApplication) {
                TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
                // eliminate nested function calls:
                // if an argument is an arithmetic function with constant or
                // variable arguments, move it to the constraint
                // otherwise replace it by a fresh variable
                for (TRSTerm arg : rhs.getArguments()) {
                    ArithmeticElimination elim = this.eliminateNestedArithmetic(arg, fng);
                    args.add(elim.replacement);
                    if (elim.condition == null) {
                        continue;
                    }
                    condition = IDPv2ToIDPv1Utilities.getConjunction(condition, elim.condition);

                }
                TRSTerm newRhs = TRSTerm.createFunctionApplication(rhs.getRootSymbol(), ImmutableCreator.create(args));

                final IGeneralizedRule iRule = IGeneralizedRule.create(rule.getLeft(), newRhs, condition);
                rules.add(iRule);
                inverseNodes.add(iRule, inverseNodeMap.get(node));

            }
        }

        return new IRSProblem(ImmutableCreator.create(rules));
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public class IDPRemoveTermProof extends DefaultProof implements DOT_Able {
        private final IDPProblem idp;
        private final CollectionMap<FunctionSymbol, Integer> filter;
        private final BasicObligationNode subBon;
        private final boolean done;

        /** Obligation node where substrategy has been applied. */

        public IDPRemoveTermProof(final IDPProblem idp, final CollectionMap<FunctionSymbol, Integer> filter,
                BasicObligationNode bon, boolean done) {
            this.idp = idp;
            this.filter = filter;
            this.subBon = bon;
            this.done = done;
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
            if (!done) {
                result.append(o.cond_linebreak());
                result.append("Created the following IDP without terms:");
                result.append(o.cond_linebreak());
                result.append(idp);
                result.append(o.cond_linebreak());

                result.append("The following proof was generated: ");
                final GenericExportManager subproof = new GenericExportManager(IDPRemoveTermProof.this.subBon,
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
