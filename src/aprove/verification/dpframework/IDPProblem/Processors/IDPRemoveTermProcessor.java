/**
 *
 * @author 
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.Processors;

import immutables.*;
import immutables.Immutable.*;

import java.util.*;
import java.util.Map.*;
import java.util.logging.*;

import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

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

    private final boolean tempFilter;
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
        this.tempFilter = arguments.tempFilter;
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

            final GeneralizedRule rule = GeneralizedRule.create(newL, newR);
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

            final Node newNode = new Node(GeneralizedRule.create(newL, newR), node.id, node.loopSubstitution);
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

        if (!this.tempFilter) {
            return ResultFactory.proved(irsProblem, YNMImplication.SOUND, new IDPRemoveTermProof(filter));

        }

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
                    final IDPRemoveTermProof proof = new IDPRemoveTermProof(filter);
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

                    if (resultingIdpNodes.isEmpty()) {
                        final IDPRemoveTermProof proof = new IDPRemoveTermProof(filter);
                        newOblNode.recursiveRepropagateTruthValues();
                        final ExecutableStrategy succStrategy = Success.EMPTY;
                        return ResultFactory.provedWithNewStrategy(newOblNode, YNMImplication.SOUND, proof,
                                succStrategy);

                    } else {
                        final IDPRemoveTermProof proof = new IDPTempRemoveTermProof(filter, newOblNode);
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
        Set<aprove.verification.complexity.LowerBounds.BasicStructures.Rule> newRules = new LinkedHashSet<>();
        for (final GeneralizedRule rule : rules) {
            newRules.add(new aprove.verification.complexity.LowerBounds.BasicStructures.Rule(rule.getLeft(), rule.getRight()));
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

        // The fresh variable
        TRSVariable var = TRSTerm.createVariable(fng.getFreshName("var_" + term.getName(), false));

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

        // A constant value v is replaced by a fresh variable x and the
        // constraint
        // v = x. Boolean constants (true and false) are replaced by integer
        // variables with value 1 or 0.
        // This is only necessary for the lhs, but doesn't harm to also have for
        // the rhs.
        if (IDPPredefinedMap.DEFAULT_MAP.isBooleanTrue(funApp.getFunctionSymbol())) {
            return new ArithmeticElimination(
                    TRSTerm.createFunctionApplication(
                            IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq,
                                    DomainFactory.INTEGER_INTEGER),
                            var,
                            PredefinedSemanticsFactory.getInt(BigIntImmutable.ONE, DomainFactory.INTEGERS).getTerm()),
                    var);
        } else if (IDPPredefinedMap.DEFAULT_MAP.isBooleanFalse(funApp.getFunctionSymbol())) {
            return new ArithmeticElimination(
                    TRSTerm.createFunctionApplication(
                            IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq,
                                    DomainFactory.INTEGER_INTEGER),
                            var,
                            PredefinedSemanticsFactory.getInt(BigIntImmutable.ZERO, DomainFactory.INTEGERS).getTerm()),
                    var);
        } else if (IDPPredefinedMap.DEFAULT_MAP.isInt(funApp.getFunctionSymbol(), DomainFactory.INTEGERS)) {
            return new ArithmeticElimination(TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    funApp), var);
        }

        // +(a,b)...
        // Arithmetic functions are moved 1:1 to the constraint and a fresh
        // variable is inserted.
        if (IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(funApp.getFunctionSymbol()).isArithmetic()) {
            TRSTerm constraint = TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    funApp);

            return new ArithmeticElimination(constraint, var);
        }

        // >(a,b)...
        // Relations/Boolean functions return a boolean, but IRSs only allow
        // integers.
        // Replace them by a new integer variable which is fixed to 1 if the
        // relation holds, and 0 otherwise.
        if (IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(funApp.getFunctionSymbol()).isRelation()
                || IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(funApp.getFunctionSymbol()).isBoolean()) {
            // replace with constant true, represented as 1, or false,
            // represented as 0, and add appropriate conditions

            // a > b holds
            // the variable replacing a > b is replaced by 1 (treated as true,
            // must also be replaced in the lhs of all rules)
            TRSTerm varIsTrue = TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    PredefinedSemanticsFactory.getInt(BigIntImmutable.ONE, DomainFactory.INTEGERS).getTerm());
            TRSTerm varIsFalse = TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER), var,
                    PredefinedSemanticsFactory.getInt(BigIntImmutable.ZERO, DomainFactory.INTEGERS).getTerm());

            TRSTerm relationIsTrue = IDPv2ToIDPv1Utilities.getConjunction(funApp, varIsTrue);
            TRSTerm relationIsFalse = IDPv2ToIDPv1Utilities.getConjunction(IDPv2ToIDPv1Utilities.negate(funApp),
                    varIsFalse);

            TRSTerm condition = IDPv2ToIDPv1Utilities.getDisjunction(relationIsTrue, relationIsFalse);
            // return new ArithmeticElimination(relationIsTrue, var);
            return new ArithmeticElimination(condition, var);
        }

        assert false : "encountered predefined but unhandled function symbol: " + funApp.getFunctionSymbol().toString();

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
            List<TRSTerm> rhsArgs = new ArrayList<>();
            List<TRSTerm> lhsArgs = new ArrayList<>();
            TRSTerm condition = IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getTerm();

            if (rule.getRight() instanceof TRSFunctionApplication) {
                TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
                TRSFunctionApplication lhs = (TRSFunctionApplication) rule.getLeft();
                // eliminate nested function calls:
                // if an argument is an arithmetic function with constant or
                // variable arguments, move it to the constraint
                // otherwise replace it by a fresh variable
                for (TRSTerm arg : rhs.getArguments()) {
                    ArithmeticElimination elim = this.eliminateNestedArithmetic(arg, fng);
                    rhsArgs.add(elim.replacement);
                    condition = IDPv2ToIDPv1Utilities.getConjunction(condition, elim.condition);

                }
                TRSTerm newRhs = TRSTerm.createFunctionApplication(rhs.getRootSymbol(),
                        ImmutableCreator.create(rhsArgs));

                for (TRSTerm arg : lhs.getArguments()) {
                    ArithmeticElimination elim = this.eliminateNestedArithmetic(arg, fng);
                    lhsArgs.add(elim.replacement);
                    condition = IDPv2ToIDPv1Utilities.getConjunction(condition, elim.condition);

                }
                TRSFunctionApplication newLhs = TRSTerm.createFunctionApplication(lhs.getRootSymbol(),
                        ImmutableCreator.create(lhsArgs));

                IDPPredefinedMap predefinedMap = iDP.getRuleAnalysis().getPreDefinedMap();
                final TRSFunctionApplication condFA = (TRSFunctionApplication) condition;

                TRSTerm killedNot = IRSwTFormatTransformer.killNOT(condFA, predefinedMap);
                final Set<TRSTerm> newConds = killedNot.isVariable() ? Collections.singleton(killedNot)
                        : IRSwTFormatTransformer.killOR(
                                IRSwTFormatTransformer.killNE((TRSFunctionApplication) killedNot, predefinedMap),
                                predefinedMap);
                for (TRSTerm cond : newConds) {
                    IGeneralizedRule iRule = IGeneralizedRule.create(newLhs, newRhs, cond);
                    // iRule = IDPv2ToIDPv1Utilities.shuffleMatchings(iRule);
                    rules.add(iRule);
                    inverseNodes.add(iRule, inverseNodeMap.get(node));
                }
            }
        }

        return new IRSProblem(ImmutableCreator.create(rules));
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public class IDPRemoveTermProof extends DefaultProof {
        private final CollectionMap<FunctionSymbol, Integer> filter;

        /** Obligation node where substrategy has been applied. */

        public IDPRemoveTermProof(final CollectionMap<FunctionSymbol, Integer> filter) {
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
    }

    public class IDPTempRemoveTermProof extends IDPRemoveTermProof {
        private final BasicObligationNode subBon;

        /** Obligation node where substrategy has been applied. */

        public IDPTempRemoveTermProof(final CollectionMap<FunctionSymbol, Integer> filter, BasicObligationNode bon) {
            super(filter);
            this.subBon = bon;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result = new StringBuilder();

            result.append(super.export(o, level));
            result.append(o.linebreak());

            result.append("The following proof was generated: ");
            final GenericExportManager subproof = new GenericExportManager(IDPTempRemoveTermProof.this.subBon,
                    "filtering result", false);
            result.append(o.preFormatted(subproof.export(new PLAIN_Util())));

            return result.toString();
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

    public static class Arguments {
        /**
         * Whether the processor filters temporarily or jumps to an IRS. If
         * true, `strategy` is executed and removed rules will be removed from
         * the IDP. If false, an IRSProblem will be returned
         */
        boolean tempFilter = false;

        /** Strategy to execute. */
        UserStrategy strategy;

        /** Time to live! */
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
