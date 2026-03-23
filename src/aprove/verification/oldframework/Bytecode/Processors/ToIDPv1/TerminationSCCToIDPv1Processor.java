package aprove.verification.oldframework.Bytecode.Processors.ToIDPv1;

import java.io.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.Node;
import aprove.verification.oldframework.Bytecode.Processors.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.TerminationSCCToIDPv2Processor.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IntTRS.Compression.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import immutables.*;

/**
 * This processor takes the information provided in the FI Graph and puts this
 * information into ITRS problems. For each SCC in the graph an ITRS problem is
 * created.
 *
 * To create an ITRS problem, each edge of an SCC is translated into a rule.
 *
 * @author Christian von Essen, Marc Brockschmidt
 */
public class TerminationSCCToIDPv1Processor extends Processor.ProcessorSkeleton {

    // Needed to check whether conditions of rules are satisfiable in some cases.
    private static FreshNameGenerator fng = new FreshNameGenerator(new AppendNameGenerator(3, 0));

    private static FormulaFactory<SMTLIBTheoryAtom> formulaFactory = new FullSharingFactory<>();

    private static SMTEngine smtSolver = new SMTLIBEngine();

    /**
     * Applies integer constraint simplifications to rules.
     * @param rules set of rules
     * @param dontRemove set of function symbols whose rules shall not be removed
     * @param forceMaxAway decides if the internally used MAX symbol should be removed in the constraint cleaning
     * @param kittelsupport decides if the constraints should be simplified for KITTeL-style termination-proving (i.e.
     * normalized multiplications, ...)
     * @param predefinedMap the predefined map
     * @param aborter some aborter
     * @return simplified set of rules
     * @throws AbortionException as soon as the aborter kicks in.
     */
    public static Set<IGeneralizedRule> cleanConstraints(
        final Set<IGeneralizedRule> rules,
        final boolean forceMaxAway,
        final boolean kittelsupport,
        final IDPPredefinedMap predefinedMap,
        final Abortion aborter
    ) throws AbortionException {
        return cleanConstraints(rules, Collections.emptySet(), forceMaxAway, kittelsupport, predefinedMap, aborter);
    }

    /**
     * Applies integer constraint simplifications to rules.
     * @param rules set of rules
     * @param dontRemove set of function symbols whose rules shall not be removed
     * @param forceMaxAway decides if the internally used MAX symbol should be removed in the constraint cleaning
     * @param kittelsupport decides if the constraints should be simplified for KITTeL-style termination-proving (i.e.
     * normalized multiplications, ...)
     * @param predefinedMap the predefined map
     * @param aborter some aborter
     * @return simplified set of rules
     * @throws AbortionException as soon as the aborter kicks in.
     */
    public static Set<IGeneralizedRule> cleanConstraints(
        final Set<IGeneralizedRule> rules,
        final Set<FunctionSymbol> dontRemove,
        final boolean forceMaxAway,
        final boolean kittelsupport,
        final IDPPredefinedMap predefinedMap,
        final Abortion aborter
    ) throws AbortionException {
        final Set<IGeneralizedRule> result = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : rules) {
            final IGeneralizedRule newRule = IRSwTFormatTransformer.moveArithmeticToConstrains(rule, predefinedMap);
            final TRSTerm constraint = newRule.getCondTerm();
            if (constraint == null) {
                result.add(rule);
            } else {
                boolean condSuperfluous = false;
                boolean ruleSuperfluous = false;
                // does not contain variables that just occur in the condition
                Set<TRSVariable> usedVars = rule.getVariables();
                Set<TRSVariable> usedCondVars = new LinkedHashSet<>(rule.getCondVariables());
                usedCondVars.retainAll(usedVars);
                // If there are no variables in the condition that also occur in the rule, then we
                // can drop the condition if it is satisfiable. Otherwise, we can drop the rule.
                if (usedCondVars.isEmpty()) {
                    YNM sat = TerminationSCCToIDPv1Processor.checkSat(constraint, aborter);
                    switch (sat) {
                        case YES:
                            condSuperfluous = true;
                            break;
                        case NO:
                            ruleSuperfluous = true;
                            break;
                        default: // nothing to do
                    }
                }
                if (condSuperfluous) {
                    result.add(IGeneralizedRule.create(rule.getLeft(), rule.getRight(), null));
                } else if (!ruleSuperfluous || dontRemove.contains(rule.getLeft().getFunctionSymbol())) {
                    try {
                        final Pair<TRSTerm, TRSSubstitution> cleanRes =
                            IntegerConstraintCleaner.clean(
                                constraint,
                                forceMaxAway,
                                kittelsupport,
                                aborter
                            );
                        final TRSFunctionApplication cleanedLeft = newRule.getLeft().applySubstitution(cleanRes.y);
                        final TRSTerm cleanedRight = newRule.getRight().applySubstitution(cleanRes.y);
                        if (
                            cleanRes.x == null
                            || cleanRes.x.isVariable()
                            || !((TRSFunctionApplication)cleanRes.x).getRootSymbol().equals(
                                predefinedMap.getBooleanFalse().getSym()
                            )
                            || dontRemove.contains(cleanedLeft.getFunctionSymbol())
                        ) {
                            result.add(IGeneralizedRule.create(cleanedLeft, cleanedRight, cleanRes.x));
                        }
                    } catch (final IllegalArgumentException e) {
                        result.add(rule);
                    }
                }
            }
        }
        return result;
    }

    /**
     * Perform all steps needed to simplify and clean rules automatically generated from a termination graph.
     * @param pIGRules the P rules (those for which we need to prove termination)
     * @param rIGRules the R rules (those which might be called from P or R)
     * @param predefinedMap the predefined map
     * @param args parameters for this process, usually from the strategy
     * @param conversionLog a list used to log the cleaning steps
     * @param rti the runtime information (needed for dumping)
     * @param oblId (needed for dumping)
     * @param aborter the aborter
     * @return a pair of cleaned P and R rules
     * @throws AbortionException when aborted
     */
    public static Pair<Set<GeneralizedRule>, Set<GeneralizedRule>> doRuleCleaning(
        final Set<IGeneralizedRule> pIGRules,
        final Set<IGeneralizedRule> rIGRules,
        final IDPPredefinedMap predefinedMap,
        final Arguments args,
        final List<Pair<String, ? extends RuleSet>> conversionLog,
        final RuntimeInformation rti,
        final String oblId,
        final Abortion aborter
    ) throws AbortionException {
        RuleCombiner pIGCombiner = new RuleCombiner(pIGRules, Collections.emptySet(), aborter);
        Set<IGeneralizedRule> curPIGRules = pIGCombiner.combineRules(true, true).y;
        final Set<FunctionSymbol> usedInPSymbols = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : curPIGRules) {
            usedInPSymbols.addAll(rule.getRight().getFunctionSymbols());
        }
        Set<IGeneralizedRule> curRIGRules;
        if (args.compressRules) {
            RuleCombiner rIGCombiner = new RuleCombiner(rIGRules, usedInPSymbols, aborter);
            curRIGRules = filterUnreachableRRules(curPIGRules, rIGCombiner.combineRules(true, true).y);
        } else {
            curRIGRules = TerminationSCCToIDPv1Processor.filterUnreachableRRules(curPIGRules, rIGRules);
        }
        TerminationSCCToIDPv1Processor.dumpIGRulesToQTRSIfPossible(
            args.qtrsDumpDir,
            rti,
            oblId + "combined",
            curPIGRules,
            curRIGRules,
            predefinedMap
        );
        conversionLog.add(
            new Pair<String, RuleSet>(
                "Combined rules. Obtained "
                + curPIGRules.size()
                + " conditional rules for P and "
                + curRIGRules.size()
                + " conditional rules for R.",
                new IGeneralizedRuleSet(curPIGRules, curRIGRules)
            )
        );
        // Transform constraints
        Set<GeneralizedRule> pGRules = IGeneralizedRule.removeConditions(curPIGRules, true);
        Set<GeneralizedRule> rGRules = IGeneralizedRule.removeConditions(curRIGRules, true);
        // TODO give this type a name
        Triple<
            Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
            Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
            Collection<Rule>
        > resultTriple;
        final GroundTermRemover groundTermRemover = new GroundTermRemover();
        resultTriple = groundTermRemover.processRulePair(pGRules, rGRules, predefinedMap);
        if (resultTriple != null) {
            pGRules = resultTriple.x.x;
            rGRules = resultTriple.y.x;
            conversionLog.add(new Pair<>("Filtered ground terms:", new RuleSet(resultTriple.z)));
        }
        if (args.filterUnneededArguments) {
            final UnneededArgumentRemover unneededArgumentRemover = new UnneededArgumentRemover();
            resultTriple = unneededArgumentRemover.processRulePair(pGRules, rGRules, predefinedMap);
            if (resultTriple != null) {
                pGRules = resultTriple.x.x;
                rGRules = resultTriple.y.x;
                conversionLog.add(new Pair<>("Filtered unneeded arguments:", new RuleSet(resultTriple.z)));
            }
        }
        TerminationSCCToIDPv1Processor.dumpIGRulesToQTRSIfPossible(
            args.qtrsDumpDir,
            rti,
            oblId + "filtered",
            curPIGRules,
            curRIGRules,
            predefinedMap
        );
        aborter.checkAbortion();
        if (args.filterDuplicateArguments) {
            final DuplicateArgsRemover duplicateArgsRemover = new DuplicateArgsRemover();
            resultTriple = duplicateArgsRemover.processRulePair(pGRules, rGRules, predefinedMap);
            if (resultTriple != null) {
                pGRules = resultTriple.x.x;
                rGRules = resultTriple.y.x;
                conversionLog.add(new Pair<>("Filtered duplicate args:", new RuleSet(resultTriple.z)));
            }
            aborter.checkAbortion();
        }
        if (args.filterUnneededArguments) {
            final UnneededArgumentRemover unneededArgumentRemover = new UnneededArgumentRemover();
            resultTriple = unneededArgumentRemover.processRulePair(pGRules, rGRules, predefinedMap);
            if (resultTriple != null) {
                pGRules = resultTriple.x.x;
                rGRules = resultTriple.y.x;
                conversionLog.add(new Pair<>("Filtered unneeded arguments:", new RuleSet(resultTriple.z)));
            }
            aborter.checkAbortion();
        }
        RuleAnalysis<GeneralizedRule> pAnalysis = new RuleAnalysis<>(ImmutableCreator.create(pGRules), predefinedMap);
        //Try to readd conditions to run our cleaners again (now restrict to DPs in P)
        curPIGRules = TerminationSCCToIDPv1Processor.readdConditions(pAnalysis.getDependencyPairs());
        curPIGRules =
            TerminationSCCToIDPv1Processor.cleanConstraints(curPIGRules, false, false, predefinedMap, aborter);
        curPIGRules = TerminationSCCToIDPv1Processor.removeTrivialConstraints(curPIGRules, predefinedMap);
        curRIGRules =
            TerminationSCCToIDPv1Processor.filterUnreachableRRules(
                curPIGRules,
                TerminationSCCToIDPv1Processor.readdConditions(rGRules)
            );
        curRIGRules =
            TerminationSCCToIDPv1Processor.cleanConstraints(curRIGRules, false, false, predefinedMap, aborter);
        curRIGRules = TerminationSCCToIDPv1Processor.removeTrivialConstraints(curRIGRules, predefinedMap);
        if (args.compressRules) {
            pIGCombiner = new RuleCombiner(curPIGRules, Collections.emptySet(), aborter);
            curPIGRules = pIGCombiner.combineRules(true, true).y;
            RuleCombiner rIGCombiner = new RuleCombiner(curRIGRules, usedInPSymbols, aborter);
            curRIGRules = rIGCombiner.combineRules(true, true).y;
        }
        curPIGRules = TerminationSCCToIDPv1Processor.removePredefinedOpsOnLhs(curPIGRules, predefinedMap);
        curRIGRules = TerminationSCCToIDPv1Processor.removePredefinedOpsOnLhs(curRIGRules, predefinedMap);
        conversionLog.add(
            new Pair<String, RuleSet>(
                "Combined rules. Obtained "
                + curPIGRules.size()
                + " conditional rules for P and "
                + curRIGRules.size()
                + " conditional rules for R.",
                new IGeneralizedRuleSet(curPIGRules, curRIGRules)
            )
        );
        aborter.checkAbortion();
        pGRules =
            IGeneralizedRule.removeConditions(
                curPIGRules,
                true
            );
        rGRules =
            IGeneralizedRule.removeConditions(
                curRIGRules,
                true
            );
        //Prepare the shit out of idp:
        aborter.checkAbortion();
        TerminationSCCToIDPv1Processor.dumpGRulesToQTRSIfPossible(
            args.qtrsDumpDir,
            rti,
            "final",
            pGRules,
            rGRules,
            predefinedMap
        );
        return new Pair<>(pGRules, rGRules);
    }

    /**
     * @param rules set of rules which might have free vars in their conditions
     * @param predefinedMap the predefined map
     * @param retainRelationInformation if true, f(x) -> f(y) | y < x and similar conditions are not removed.
     * @return a set of rules which does not use free variables in its conditions
     */
    public static Set<IGeneralizedRule> filterFreeVarFromCond(
        final Set<IGeneralizedRule> rules,
        final IDPPredefinedMap predefinedMap,
        final boolean retainRelationInformation
    ) {
        final LinkedHashSet<IGeneralizedRule> res = new LinkedHashSet<>();
        RemoveFreeVarsFromCond freeVarFilter = new RemoveFreeVarsFromCond(retainRelationInformation);
        for (final IGeneralizedRule rule : rules) {
            res.add(freeVarFilter.removeFreeVarsFromCond(rule));
        }
        return res;
    }

    /**
     * @param pRules set of P rules
     * @param rRules set of R rules
     * @return set of R rules only containing things reachable from
     *  <code>pRules</code>.
     */
    public static final Set<IGeneralizedRule> filterUnreachableRRules(
        final Set<IGeneralizedRule> pRules,
        final Set<IGeneralizedRule> rRules
    ) {
        /*
         * Get all symbols that are "called" from P (i.e. function symbols
         * on the rhs of P's rules):
         */
        final Set<FunctionSymbol> calledSym = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : pRules) {
            calledSym.addAll(rule.getRight().getFunctionSymbols());
        }
        /*
         * The set of needed rules from R are those whose root function
         * symbol on the lhs is a called symbol:
         */
        final Set<IGeneralizedRule> neededRules = new LinkedHashSet<>();
        boolean changed = false;
        do {
            changed = false;
            for (final IGeneralizedRule rule : rRules) {
                if (calledSym.contains(rule.getLeft().getRootSymbol())) {
                    if (neededRules.add(rule)) {
                        changed = true;
                        calledSym.addAll(rule.getRight().getFunctionSymbols());
                    }
                }
            }
        } while (changed);
        return neededRules;
    }

    /**
     * @param rules some TRS, given as collection of rules
     * @return true iff this looks like there are rules which traverse objects
     */
    public static boolean isjlORemovalSystem(final Collection<GeneralizedRule> rules) {
        for (final GeneralizedRule rule : rules) {
            final Set<TRSTerm> rhsSubTerms = rule.getRight().getSubTerms();
            for (final TRSTerm subTerm : rule.getLeft().getSubTerms()) {
                if (subTerm.isVariable()) {
                    continue;
                }
                final TRSFunctionApplication subFa = (TRSFunctionApplication)subTerm;
                final FunctionSymbol subFs = subFa.getRootSymbol();
                /*
                 * If this is some jlO-wrapped non-array thing, check if it does
                 * not appear on the rhs, but one of the enclosed variables does.
                 */
                if (InstanceTransformer.JAVA_LANG_OBJECT_NAME.getName().equals(subFs.getName())) {
                    if (subFs.getArity() < 1 || !subFa.getArgument(0).getName().startsWith("ARRAY")) {
                        if (!rhsSubTerms.contains(subFa)) {
                            for (final TRSVariable wrappedVar : subFa.getVariables()) {
                                if (rhsSubTerms.contains(wrappedVar)) {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    /**
     * @param uncondedRules set of generalized rules
     * @return set of IGeneralizedRules
     */
    public static Set<IGeneralizedRule> readdConditions(final Set<GeneralizedRule> uncondedRules) {
        final CollectionMap<FunctionSymbol, GeneralizedRule> symbolMap = new CollectionMap<>();
        for (final GeneralizedRule rule : uncondedRules) {
            symbolMap.add(rule.getLeft().getRootSymbol(), rule);
        }
        final Set<GeneralizedRule> processedRules = new LinkedHashSet<>();
        final Set<IGeneralizedRule> condedRules = new LinkedHashSet<>();
        for (final GeneralizedRule rule : uncondedRules) {
            //Check, otherwise mark that we processed this rule
            if (!processedRules.add(rule)) {
                continue;
            }
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSTerm rhs = rule.getRight();
            //Check if this leads to a cond rule
            if (
                (rhs.getName().startsWith("Cond_") || rhs.getName().startsWith("COND_"))
                && rhs instanceof TRSFunctionApplication
            ) {
                final TRSFunctionApplication rfa = ((TRSFunctionApplication) rhs);
                if (symbolMap.getNotNull(rfa.getRootSymbol()).size() >= 1) {
                    for (final GeneralizedRule condRule : symbolMap.getNotNull(rfa.getRootSymbol())) {
                        final TRSTerm newRhs = condRule.getRight();
                        final TRSTerm newCond = rfa.getRootSymbol().getArity() > 0 ? rfa.getArgument(0) : ToolBox.buildTrue();
                        processedRules.add(condRule);
                        if (newCond instanceof TRSVariable && !lhs.getVariables().contains(newCond)) {
                            condedRules.add(IGeneralizedRule.create(lhs, newRhs, null));
                        } else {
                            condedRules.add(IGeneralizedRule.create(lhs, newRhs, newCond));
                        }
                    }
                    continue;
                }
            }
            condedRules.add(IGeneralizedRule.create(lhs, rhs, null));
        }
        assert (processedRules.size() == uncondedRules.size()) : "Lost rules, I think";
        return condedRules;
    }

    /**
     * @param rules set of rules
     * @param predefinedMap a predefined map
     * @return new set of rules that have no predefined ops on lhss.
     */
    public static Set<IGeneralizedRule> removePredefinedOpsOnLhs(
        final Set<IGeneralizedRule> rules,
        final IDPPredefinedMap predefinedMap
    ) {
        final Set<IGeneralizedRule> result = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : rules) {
            final TRSFunctionApplication lhs = rule.getLeft();
            TRSFunctionApplication newLhs = lhs;
            final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
            fne.lockHasNames(rule.getVariables());
            TRSTerm newCond = rule.getCondTerm();
            final TRSTerm rhs = rule.getRight();
            boolean changed = true;
            restartScan: while (changed) {
                changed = false;
                for (final Position pos : newLhs.getPositions()) {
                    final TRSTerm subterm = newLhs.getSubterm(pos);
                    if (subterm instanceof TRSFunctionApplication) {
                        final TRSFunctionApplication fa = (TRSFunctionApplication) subterm;
                        FunctionSymbol f = fa.getRootSymbol();
                        if (predefinedMap.isInt(f, DomainFactory.INTEGERS) || (f.getArity() == 2 && predefinedMap.isPredefined(f))) {
                            String origName = ArithExpToVarName.getVarName(fa);
                            final TRSVariable newVar = TRSTerm.createVariable(fne.getFreshName(origName, false));
                            newLhs = (TRSFunctionApplication) newLhs.replaceAt(pos, newVar);
                            final TRSFunctionApplication newVarCond =
                                TRSTerm.createFunctionApplication(
                                    predefinedMap.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER),
                                    newVar,
                                    fa
                                );
                            if (newCond == null) {
                                newCond = newVarCond;
                            } else {
                                newCond =
                                    TRSTerm.createFunctionApplication(
                                        predefinedMap.getSym(Func.Land, DomainFactory.BOOLEAN),
                                        newCond,
                                        newVarCond
                                    );
                            }
                            changed = true;
                            continue restartScan;
                        }
                    }
                }
            }
            final IGeneralizedRule newRule = IGeneralizedRule.create(newLhs, rhs, newCond);
            result.add(newRule);
        }
        return result;
    }

    /**
     * Removes every condition of the form "x = x"
     * @param rules Rule set to filter
     * @param predefinedMap the predefined map
     * @return New rule set
     */
    public static Set<IGeneralizedRule> removeTrivialConstraints(
        final Set<IGeneralizedRule> rules,
        final IDPPredefinedMap predefinedMap
    ) {
        final LinkedHashSet<IGeneralizedRule> newRules = new LinkedHashSet<>();
        final FunctionSymbol andSym = predefinedMap.getSym(Func.Land, DomainFactory.BOOLEAN);
        final FunctionSymbol eqSym = predefinedMap.getSym(Func.Eq, DomainFactory.INTEGER_INTEGER);
        for (final IGeneralizedRule rule : rules) {
            //If there's no condition, there's nothing to simplify:
            final TRSTerm condition = rule.getCondTerm();
            if (condition == null) {
                newRules.add(rule);
                continue;
            }
            final LinkedList<TRSTerm> stack = new LinkedList<>();
            final Set<TRSFunctionApplication> keptConstraints = new LinkedHashSet<>();
            final Set<TRSSubstitution> substs = new LinkedHashSet<>();
            stack.push(condition);
            /*
             * Simplify the constraints:
             *  - If it's a conjunction, look at both parts.
             *  - If it's an equality, add it to the substitutions if one side
             *    is a variable.
             *  - If it's something different, add it to the new constraints.
             */
            while (!stack.isEmpty()) {
                final TRSFunctionApplication c = (TRSFunctionApplication)stack.pop();
                final FunctionSymbol root = c.getRootSymbol();
                if (root.equals(andSym)) {
                    stack.addAll(c.getArguments());
                } else if (root.equals(eqSym)) {
                    final TRSTerm left = c.getArgument(0);
                    final TRSTerm right = c.getArgument(1);
                    if (left.equals(right)) {
                        continue;
                    } else if (right.isVariable() && (left.isVariable() || left.isConstant())) {
                        substs.add(TRSSubstitution.create((TRSVariable) right, left));
                    } else if (left.isVariable() && (right.isVariable() || right.isConstant())) {
                        substs.add(TRSSubstitution.create((TRSVariable) left, right));
                    } else {
                        keptConstraints.add(c);
                    }
                } else {
                    keptConstraints.add(c);
                }
            }
            TRSTerm newConstraint = null;
            for (final TRSFunctionApplication c : keptConstraints) {
                newConstraint = IDPv2ToIDPv1Utilities.getConjunction(newConstraint, c);
            }
            TRSFunctionApplication newLeft = rule.getLeft();
            TRSTerm newRight = rule.getRight();
            List<TRSTerm> newLeftOutputVariables = rule.getLeftOutputVariables();
            boolean changed;
            do {
                TRSTerm oldLeft = newLeft;
                TRSTerm oldRight = newRight;
                TRSTerm oldConstraint = newConstraint;
                for (final TRSSubstitution s : substs) {
                    newLeft = newLeft.applySubstitution(s);
                    for (TRSTerm outVar: newLeftOutputVariables) {
                        outVar.applySubstitution(s);
                    }
                    newRight = newRight.applySubstitution(s);
                    if (newConstraint != null) {
                        newConstraint = newConstraint.applySubstitution(s);
                    }
                }
                changed = !(oldLeft.equals(newLeft) && oldRight.equals(newRight) && (newConstraint == null || oldConstraint.equals(newConstraint)));
            } while (changed);
            newRules.add(IGeneralizedRule.create(newLeft, newRight, newConstraint, newLeftOutputVariables));
        }
        return newRules;
    }

    /**
     * @param obl an FI Graph
     * @param aborter some aborter
     * @param rti ignored.
     * @param conversionArguments argument object setting options for the conversion
     * @throws AbortionException as soon as the aborter kicks in.
     * @return IDPProblem, QDPProblem or null, depending on the shape of obl
     */
    public static Pair<? extends BasicObligation, List<Pair<String, ? extends RuleSet>>> toObligation(
        final BasicObligation obl,
        final Abortion aborter,
        final RuntimeInformation rti,
        final Arguments conversionArguments
    ) throws AbortionException {
        final List<Pair<String, ? extends RuleSet>> conversionLog = new LinkedList<>();
        // Get rule sets from the graph and turn them into problems.
        final JBCTerminationSCCProblem terminationSCCProblem = (JBCTerminationSCCProblem) obl;
        // Edges from the SCC shall be converted into rules in P
        final Collection<Edge> pEdges = terminationSCCProblem.getSCC().getEdges();
        // All other edges shall be converted into rules in R
        final Collection<Edge> rEdges = new LinkedHashSet<>();
        rEdges.addAll(terminationSCCProblem.getOutgoingCallEdges());
        for (final MethodGraph calledGraph : terminationSCCProblem.getHelperGraphs()) {
            rEdges.addAll(calledGraph.getEdges());
            //Find all implicit incoming edges and add them too:
            for (final MethodEndListener listener : calledGraph.getMethodEndListeners()) {
                if (terminationSCCProblem.getHelperGraphs().contains(listener.getMethodGraph())) {
                    boolean found = false;
                    Node startNode = null;
                    for (final Edge edge : listener.getNode().getOutEdges()) {
                        if (edge.getLabel() instanceof CallAbstractEdge) {
                            found = true;
                            // There may be a chain of instance edges following the call abstraction.
                            Node tempNode = edge.getEnd();
                            Set<Edge> outEdges = tempNode.getOutEdges();
                            while (!outEdges.isEmpty()) {
                                tempNode = outEdges.iterator().next().getEnd();
                                outEdges = tempNode.getOutEdges();
                            }
                            startNode = tempNode;
                            break;
                        }
                    }
                    assert (found) : "Could not find source of call";
                    final Node endNode = calledGraph.getStartNode();
                    rEdges.add(new Edge(startNode, new InstanceEdgeBetweenGraphs(), endNode));
                }
            }
        }
        aborter.checkAbortion();
        //Construct graph of all involved nodes and edges:
        final JBCGraph fullGraph = terminationSCCProblem.getFullGraph();
        //Initialize the rule creator and transformation dispatcher:
        final PolyFactory polyFactory = new SharingPolyFactory();
        final ItpfFactory itpfFactory = new SharingItpfFactory(polyFactory);
        final SCCAnnotations sccAnnotations = terminationSCCProblem.getSCCAnnotations();
        final TransformationDispatcher dispatcher = new TransformationDispatcher(sccAnnotations, conversionArguments);
        final RuleCreator ruleCreator =
            new RuleCreator(fullGraph, conversionArguments, dispatcher, sccAnnotations, itpfFactory, aborter);
        final Set<IGeneralizedRule> pIGRules =
            IDPv2ToIDPv1Utilities.convertEdgesToIDPv1(
                aborter,
                ruleCreator,
                false,
                sccAnnotations,
                dispatcher,
                pEdges,
                conversionArguments.encodeMethodEnds
            );
        final Set<IGeneralizedRule> rIGRules;
        if (conversionArguments.encodeMethodEnds) {
            rIGRules =
                IDPv2ToIDPv1Utilities.convertEdgesToIDPv1(
                    aborter,
                    ruleCreator,
                    false,
                    sccAnnotations,
                    dispatcher,
                    rEdges,
                    conversionArguments.encodeMethodEnds
                );
        } else {
            rIGRules = Collections.emptySet();
        }
        aborter.checkAbortion();
        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        conversionLog.add(
            new Pair<String, RuleSet>(
                "Generated " + pIGRules.size() + " rules for P and " + rIGRules.size() + " rules for R.",
                new IGeneralizedRuleSet(pIGRules, rIGRules)
            )
        );
        aborter.checkAbortion();
        final Pair<Set<GeneralizedRule>, Set<GeneralizedRule>> p =
            TerminationSCCToIDPv1Processor.doRuleCleaning(
                pIGRules,
                rIGRules,
                predefinedMap,
                conversionArguments,
                conversionLog,
                rti,
                obl.getId(),
                aborter
            );
        final Set<GeneralizedRule> pGRules = p.x;
        final Set<GeneralizedRule> rGRules = p.y;
        // Get Q Termset
        final Collection<TRSFunctionApplication> rLHSs = new LinkedList<>();
        for (final GeneralizedRule rule : rGRules) {
            rLHSs.add(rule.getLeft());
        }
        final IQTermSet q = new IQTermSet(new QTermSet(rLHSs), predefinedMap);
        final RuleAnalysis<GeneralizedRule> rAnalysis =
            new RuleAnalysis<>(ImmutableCreator.create(rGRules), predefinedMap);
        final RuleAnalysis<GeneralizedRule> pAnalysis =
            new RuleAnalysis<>(ImmutableCreator.create(pGRules), predefinedMap);
        final IDPRuleAnalysis analysis = new IDPRuleAnalysis(rAnalysis, pAnalysis.getDependencyPairs(), q, null);
        QDPExport: if (conversionArguments.tryQDPExport) {
            if (rAnalysis.getPredefinedFunctions().isEmpty() && pAnalysis.getPredefinedFunctions().isEmpty()) {
                //Check for free variables:
                final Set<Rule> pRules = new LinkedHashSet<>();
                for (final GeneralizedRule r : pGRules) {
                    if (!Rule.checkProperLandR(r.getLeft(), r.getRight())) {
                        break QDPExport;
                    } else {
                        pRules.add(Rule.create(r.getLeft(), r.getRight()));
                    }
                }
                final Set<Rule> rRules = new LinkedHashSet<>();
                for (final GeneralizedRule r : rGRules) {
                    if (!Rule.checkProperLandR(r.getLeft(), r.getRight())) {
                        break QDPExport;
                    } else {
                        rRules.add(Rule.create(r.getLeft(), r.getRight()));
                    }
                }
                final QDPProblem qdp =
                    QDPProblem.create(
                        pRules,
                        QTRSProblem.create(ImmutableCreator.create(rRules), new QTermSet(rLHSs)),
                        true
                    );
                return new Pair<>(qdp, conversionLog);
            }
        }
        final RootConstrGraphProcessor idpGraphProc = new RootConstrGraphProcessor(IItpfRule.ApplicationMode.Multistep);
        IIDependencyGraph graph;
        try {
            graph = idpGraphProc.createInitialGraph(analysis, aborter);
        } catch (final AbortionException e) {
            return null;
        }
        conversionLog.add(
            new Pair<String, RuleSet>(
                "Finished conversion. Obtained "
                + analysis.getPAnalysis().getRules().size()
                + " rules for P and "
                + analysis.getRAnalysis().getRules().size()
                + " rules for R. System has "
                + (analysis.hasPredefinedDefSymbols() ? "" : "no ")
                + "predefined symbols.",
                new GeneralizedRuleSet(
                    analysis.getPAnalysis().getRules(),
                    analysis.getRAnalysis().getRules()
                )
            )
        );
        return new Pair<>(IDPProblem.create(graph, rAnalysis, q, true), conversionLog);
    }

    /**
     * Check whether the given condition is satisfiable via SMT.
     */
    private static YNM checkSat(TRSTerm cond, Abortion aborter) {
        List<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<>();
        ToolBox.boolTermToSMTTheoryAtoms(
            cond,
            TerminationSCCToIDPv1Processor.fng,
            formulas,
            TerminationSCCToIDPv1Processor.formulaFactory,
            aborter
        );
        YNM smtRes;
        try {
            smtRes = TerminationSCCToIDPv1Processor.smtSolver.satisfiable(formulas, SMTLogic.QF_NIA, aborter);
        } catch (WrongLogicException e) {
            smtRes = YNM.MAYBE;
        }
        return smtRes;
    }

    /**
     * @param qtrsDumpDir directory to which a QTRS is dumped
     * @param rti runtime information of the machine, used to generate a file name
     * @param infix additional String used in the file name for the exported QTRS
     * @param pRules the P rules
     * @param rRules the R rules
     * @param predefinedMap the predefined map
     */
    private static void dumpGRulesToQTRSIfPossible(
        final String qtrsDumpDir,
        final RuntimeInformation rti,
        final String infix,
        final Set<GeneralizedRule> pRules,
        final Set<GeneralizedRule> rRules,
        final IDPPredefinedMap predefinedMap
    ) {
        if (qtrsDumpDir == null) {
            return;
        }
        final Set<GeneralizedRule> combinedRules = new LinkedHashSet<>();
        combinedRules.addAll(pRules);
        combinedRules.addAll(rRules);
        //Build rule analysis:
        final RuleAnalysis<GeneralizedRule> analysis =
            new RuleAnalysis<>(ImmutableCreator.create(combinedRules), predefinedMap);
        //Prepare Q from the rules from R:
        final IQTermSet q = new IQTermSet(new QTermSet(CollectionUtils.getLeftHandSides(rRules)), predefinedMap);
        //Only dump systems which are really QTRS material:
        if (analysis.hasPredefinedDefSymbols() || analysis.hasRestrictedInt() || !analysis.satVarCondition()) {
            return;
        }
        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = inputPath.getName();
        final ITRSProblem itrs = ITRSProblem.create(ImmutableCreator.create(combinedRules), predefinedMap, q);
        final ITRStoQTRSProcessor proc = new ITRStoQTRSProcessor(new ITRStoQTRSProcessor.Arguments());
        try {
            final QTRSProblem qtrs = proc.ITRStoQTRS(itrs);
            final File path =
                new File(
                    System.getProperty("user.home")
                    + System.getProperty("file.separator")
                    + qtrsDumpDir
                    + System.getProperty("file.separator")
                    + problemName
                    + "-"
                    + infix
                    + ".trs"
                );
            path.getParentFile().mkdirs();
            try (final FileWriter fw = new FileWriter(path)) {
                fw.write(qtrs.toExternString());
            }
        } catch (final IOException | IntOutOfRangeException e) {
            return;
        }
    }

    /**
     * @param qtrsDumpDir directory to which a QTRS is dumped
     * @param rti runtime information of the machine, used to generate a file name
     * @param infix additional String used in the file name for the exported QTRS
     * @param pIGRules the P rules
     * @param rIGRules the R rules
     * @param predefinedMap the predefined map
     */
    private static void dumpIGRulesToQTRSIfPossible(
        final String qtrsDumpDir,
        final RuntimeInformation rti,
        final String infix,
        final Set<IGeneralizedRule> pIGRules,
        final Set<IGeneralizedRule> rIGRules,
        final IDPPredefinedMap predefinedMap
    ) {
        if (qtrsDumpDir == null) {
            return;
        }
        final Set<GeneralizedRule> pRulesUnconded = IGeneralizedRule.removeConditions(pIGRules, true);
        final Set<GeneralizedRule> rRulesUnconded = IGeneralizedRule.removeConditions(rIGRules, true);
        TerminationSCCToIDPv1Processor.dumpGRulesToQTRSIfPossible(
            qtrsDumpDir,
            rti,
            infix,
            pRulesUnconded,
            rRulesUnconded,
            predefinedMap
        );
    }

    /**
     * Parameters for this processor.
     */
    private final Arguments arguments;

    /**
     * Create a fresh processor to transform a FIGraph into an ITRS
     * @param args object holding parameters for this processor
     */
    @ParamsViaArgumentObject
    public TerminationSCCToIDPv1Processor(final Arguments args) {
        this.arguments = args;
    }

    /**
     * @return true for an FI Graph.
     * @param obl some obligation that should be an FI Graph
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof JBCTerminationSCCProblem;
    }

    /**
     * Work on the given obligation.
     * @param obl an FI Graph
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @throws AbortionException as soon as the aborter kicks in.
     * @return one ITRS for each SCC in the FI Graph
     */
    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti
    ) throws AbortionException {
        if (!(obl instanceof JBCTerminationSCCProblem)) {
            assert (false);
            return ResultFactory.unsuccessful();
        }
        final Pair<? extends BasicObligation, List<Pair<String, ? extends RuleSet>>> p =
            TerminationSCCToIDPv1Processor.toObligation(obl, aborter, rti, this.arguments);
        if (p.x instanceof IDPProblem) {
            return ResultFactory.proved(p.x, YNMImplication.SOUND, new TerminationSCCToIDPv1Proof(p.y));
        } else if (p.x instanceof QDPProblem) {
            return ResultFactory.proved(p.x, YNMImplication.SOUND, new TerminationSCCToQDPProof(p.y));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    public static class Arguments extends ConverterArguments {

        /**
         * Switches on rule compression. SHOULD ALWAYS BE ON.
         */
        public boolean compressRules = true;

        /**
         * Decided if method calls will be properly encoded, i.e., we have rules
         * of the form f(x,y) -&gt; f(g(x),y) and f(g_end(z), y) -&gt; h(z, y).
         * If false, we will not try to use the information from the method
         * return and generate rules f(x,y) -&gt; g(x) and f(x,y) -&gt; h(z, y).
         */
        public boolean encodeMethodEnds = true;

        /**
         * Switches on duplicate argument filter. SHOULD ALWAYS BE ON.
         */
        public boolean filterDuplicateArguments = true;

        /**
         * Switches on unneeded argument filter. SHOULD ALWAYS BE ON.
         */
        public boolean filterUnneededArguments = true;

        /**
         * Name of a directory to which QTRS problems created in the
         * conversion are dumped too. If null, no dumps are created.
         */
        public String qtrsDumpDir = null;

        /**
         * Switches on a direct QDP export (if there are no predefined
         * symbols). This doesn't really make sense without cleanRules = true.
         */
        public boolean tryQDPExport = true;

    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me)
     */
    public class TerminationSCCToIDPv1Proof extends DefaultProof {

        /**
         * Some documentation about the magic we've done.
         */
        private final List<Pair<String, ? extends RuleSet>> log;

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         */
        public TerminationSCCToIDPv1Proof(final List<Pair<String, ? extends RuleSet>> l) {
            super();
            this.log = l;
            this.shortName = "SCCToIDPv1Proof";
            this.longName = "TerminationSCCToIDPv1Proof";
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Transformed FIGraph SCCs to IDPs. Log: ");
            sb.append(o.linebreak());
            for (final Pair<String, ? extends RuleSet> entry : this.log) {
                sb.append(o.indent(entry.x));
                sb.append(o.linebreak());
                if (entry.y != null) {
                    sb.append(o.indent(entry.y.export(o)));
                }
            }
            return sb.toString();
        }
    }
}
