package aprove.verification.dpframework.IDPProblem.utility;

import java.util.*;

import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Computes argument filters for IDP rules based on the inferred types of the
 * argument positions.
 */
public final class IDPTypeFilter {

    private IDPTypeFilter() {
    }

    /**
     * @return the argument positions whose type is integer or boolean, or
     *         <code>null</code> if the rules are not well-typed
     */
    public static CollectionMap<FunctionSymbol, Integer> getIntOrBoolPositions(
            final Set<? extends GeneralizedRule> rules, final IDPPredefinedMap predefinedMap) {
        return IDPTypeFilter.getPositions(rules, predefinedMap, true);
    }

    /**
     * @return the argument positions whose type is neither integer nor
     *         boolean, or <code>null</code> if the rules are not well-typed
     */
    public static CollectionMap<FunctionSymbol, Integer> getOtherPositions(
            final Set<? extends GeneralizedRule> rules, final IDPPredefinedMap predefinedMap) {
        return IDPTypeFilter.getPositions(rules, predefinedMap, false);
    }

    /**
     * Infers the types of all argument positions in the rules. The types of
     * the arguments and results of predefined symbols are integer or boolean
     * according to their domains.
     *
     * @return the positions whose type is integer or boolean if
     *         <code>intOrBool</code> is set, and the other positions
     *         otherwise; <code>null</code> if the rules are not well-typed,
     *         i.e. if a type is both integer and boolean, or if it is integer
     *         or boolean and also the result type of a constructor, e.g. for
     *         <code>f(Nil)</code> and <code>f(1)</code>
     */
    private static CollectionMap<FunctionSymbol, Integer> getPositions(
            final Set<? extends GeneralizedRule> rules, final IDPPredefinedMap predefinedMap,
            final boolean intOrBool) {
        final Set<FunctionSymbol> allSymbols = CollectionUtils.getFunctionSymbols(rules);
        final Set<FunctionSymbol> definedSymbols = CollectionUtils.getRootSymbols(rules);

        // Convert the rules to the type expected for TypeInference
        final Set<aprove.verification.complexity.LowerBounds.BasicStructures.Rule> newRules = new LinkedHashSet<>();
        for (final GeneralizedRule rule : rules) {
            newRules.add(new aprove.verification.complexity.LowerBounds.BasicStructures.Rule(rule.getLeft(),
                    rule.getRight()));
        }
        final TrsTypes types = TypeInference.infer(newRules, allSymbols, definedSymbols);

        // Collect the integer and boolean types from the predefined symbols
        final Set<Type> intTypes = new LinkedHashSet<>();
        final Set<Type> boolTypes = new LinkedHashSet<>();
        for (final FunctionSymbol sym : allSymbols) {
            final PredefinedSemantics semantics = predefinedMap.getPredefinedSemantics(sym);
            final FunctionSymbolSimpleType symType = types.lookupType(sym);
            if (semantics instanceof PfInt || semantics instanceof PfUndefinedInt) {
                intTypes.add(symType.getReturnType());
            } else if (semantics instanceof PfBoolean) {
                boolTypes.add(symType.getReturnType());
            } else if (semantics instanceof PredefinedFunction) {
                final PredefinedFunction<?> func = (PredefinedFunction<?>) semantics;
                IDPTypeFilter.addType(func.getResultDomain(), symType.getReturnType(), intTypes, boolTypes);
                for (int i = 0; i < sym.getArity(); i++) {
                    IDPTypeFilter.addType(func.getDomains().get(i), symType.getArgumentTypes().get(i), intTypes,
                            boolTypes);
                }
            }
        }

        // Check that the rules are well-typed
        if (!Collections.disjoint(intTypes, boolTypes)) {
            return null;
        }
        for (final FunctionSymbol sym : allSymbols) {
            if (!predefinedMap.isPredefined(sym) && !definedSymbols.contains(sym)) {
                final Type returnType = types.lookupType(sym).getReturnType();
                if (intTypes.contains(returnType) || boolTypes.contains(returnType)) {
                    return null;
                }
            }
        }

        final CollectionMap<FunctionSymbol, Integer> positions = new CollectionMap<FunctionSymbol, Integer>();
        for (final FunctionSymbol sym : allSymbols) {
            final List<Type> argTypes = types.lookupArgumentTypes(sym);
            for (int i = 0; i < argTypes.size(); i++) {
                final Type type = argTypes.get(i);
                if ((intTypes.contains(type) || boolTypes.contains(type)) == intOrBool) {
                    positions.add(sym, i);
                }
            }
        }
        return positions;
    }

    private static void addType(final Domain domain, final Type type, final Set<Type> intTypes,
            final Set<Type> boolTypes) {
        if (domain instanceof IntegerDomain) {
            intTypes.add(type);
        } else if (domain instanceof BooleanDomain) {
            boolTypes.add(type);
        }
    }
}
