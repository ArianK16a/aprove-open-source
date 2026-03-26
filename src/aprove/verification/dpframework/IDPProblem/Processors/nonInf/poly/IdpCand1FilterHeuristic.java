package aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.filter.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Filters everything, which is not int
 * @author Martin Pluecker
 */
public class IdpCand1FilterHeuristic extends AbstractFilterHeuristic {

    public IdpCand1FilterHeuristic() {
        this(new Arguments());
    }

    @ParamsViaArgumentObject
    public IdpCand1FilterHeuristic(final Arguments arguments) {
        super(arguments);
    }

    @Override
    protected void initializeFilter(final IDPRuleAnalysis ruleAnalysis,
        final Map<FunctionSymbol, boolean[]> usedPositions,
        final Map<GeneralizedRule, Map<TRSVariable, Set<Pair<FunctionSymbol, Integer>>>> variablePositions) {
        final IDPPredefinedMap predefinedMap = ruleAnalysis.getPreDefinedMap();
        final ImmutableMap<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap = ruleAnalysis.getRuleMap();
        for (final GeneralizedRule rule : ruleAnalysis.getRules()) {
            final Set<TRSVariable> arithmetricVariables = new LinkedHashSet<TRSVariable>();
            final Set<TRSVariable> relationalVariables = new LinkedHashSet<TRSVariable>();
            final Map<TRSVariable, Set<Pair<FunctionSymbol, Integer>>> varPos =
                new LinkedHashMap<TRSVariable, Set<Pair<FunctionSymbol, Integer>>>();
            this.collectVariables(rule.getLeft(), new ArrayList<Pair<FunctionSymbol, Integer>>(), false, false, true,
                arithmetricVariables, relationalVariables, varPos, predefinedMap);
            this.collectVariables(rule.getRight(), new ArrayList<Pair<FunctionSymbol, Integer>>(), false, false, true,
                arithmetricVariables, relationalVariables, varPos, predefinedMap);
            arithmetricVariables.addAll(relationalVariables);
            for (final TRSVariable v : arithmetricVariables) {
                if (varPos.get(v) == null) {
                    System.err.println("varPost.get(v) is null for v=" + v);
                    continue;
                }
                for (final Pair<FunctionSymbol, Integer> p : varPos.get(v)) {
                    if (Globals.DEBUG_MPLUECKER) {
                        AbstractFilterHeuristic.log.finest("Activate RULE " + rule + "/" + v + " -> " + p.x + "/" + p.y);
                    }
                    this.activatePosition(p.x, p.y, usedPositions, predefinedMap, ruleMap, variablePositions);
                    if (Globals.DEBUG_MPLUECKER) {
                        AbstractFilterHeuristic.log.finest("\n");
                    }
                }
            }
        }
    }

    /**
     * Collects all variables on scope of predefined functions
     * @param relationalVariables
     */
    protected void collectVariables(final TRSTerm t,
        final List<Pair<FunctionSymbol, Integer>> currentPath,
        boolean arithmetic,
        boolean relational,
        boolean addPath,
        final Set<TRSVariable> arithmetricVariables,
        final Set<TRSVariable> relationalVariables,
        final Map<TRSVariable, Set<Pair<FunctionSymbol, Integer>>> variablePositions,
        final IDPPredefinedMap predefinedMap) {
        if (t.isVariable()) {
            final TRSVariable v = (TRSVariable) t;
            Set<Pair<FunctionSymbol, Integer>> varPos = variablePositions.get(v);
            if (varPos == null) {
                varPos = new LinkedHashSet<Pair<FunctionSymbol, Integer>>();
                variablePositions.put(v, varPos);
            }
            if (addPath) {
                varPos.addAll(currentPath);
            }
            if (relational) {
                relationalVariables.add(v);
            }
            if (arithmetic) {
                arithmetricVariables.add(v);
            }
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
            final FunctionSymbol fs = fa.getRootSymbol();
            final ImmutableList<TRSTerm> arguments = fa.getArguments();
            final PredefinedFunction<? extends Domain> func = predefinedMap.getPredefinedFunction(fs);
            if (func != null) {
                if (!func.isArithmetic()) {
                    if (this.filterRelations) {
                        addPath = false;
                    }
                    if (func.isRelation()) {
                        relational = true;
                        arithmetic = false;
                    }
                } else if (!relational) {
                    arithmetic = true;
                }
            }
            for (int i = arguments.size() - 1; i >= 0; i--) {
                currentPath.add(new Pair<FunctionSymbol, Integer>(fs, i));
                this.collectVariables(arguments.get(i), currentPath, arithmetic, relational, addPath, arithmetricVariables,
                    relationalVariables, variablePositions, predefinedMap);
                currentPath.remove(currentPath.size() - 1);
            }
        }
    }

    @Override
    public String export(final Export_Util o, final IDPPredefinedMap predefinedMap, final VerbosityLevel verbosityLevel) {
        return "IdpCand1ShapeHeuristic";
    }

}
