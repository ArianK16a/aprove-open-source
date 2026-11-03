package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * The projection of an IDP onto some sorts: the arguments of the other sorts
 * are removed from the pairs and the rules (Kulmer, Integer Term Rewriting via
 * Projections). Every step of the IDP is still possible or removed, so an
 * infinite chain of the IDP still yields an infinite chain of the projection.
 *
 * <p>A removed argument of a symbol below the root of the pairs may turn a
 * normal form into a redex and a terminating term into a non-terminating one.
 * So unless only arguments of tuple symbols are removed, a chain of the
 * projection is neither innermost nor minimal, see {@link #isInnermost()}.</p>
 */
public final class IDPProjection {

    private final CollectionMap<FunctionSymbol, Integer> removed;
    private final String reason;
    private final Map<Node, GeneralizedRule> pairs;
    private final Set<GeneralizedRule> rules;
    private final boolean innermost;

    private IDPProjection(final CollectionMap<FunctionSymbol, Integer> removed, final String reason,
            final Map<Node, GeneralizedRule> pairs, final Set<GeneralizedRule> rules, final boolean innermost) {
        this.removed = removed;
        this.reason = reason;
        this.pairs = pairs;
        this.rules = rules;
        this.innermost = innermost;
    }

    /**
     * Removes all integer and boolean arguments, and the arguments of a type
     * that no symbol has as result type. Only variables have such a type,
     * e.g. a fresh variable passed to a call, and as they would often be free
     * in the QDP, they are removed as well.
     *
     * @return the projection, or <code>null</code> if the IDP is not
     *         well-typed
     */
    public static IDPProjection removeIntsAndBools(final IDPProblem iDP) {
        return IDPProjection.create(iDP,
                IDPTypeFilter.getIntOrBoolPositions(IDPProjection.allRules(iDP), IDPProjection.predefinedMap(iDP), true),
                "their type is integer, boolean or only has variables");
    }

    /**
     * Removes all arguments that are neither integer nor boolean.
     *
     * @return the projection, or <code>null</code> if the IDP is not
     *         well-typed
     */
    public static IDPProjection removeOthers(final IDPProblem iDP) {
        return IDPProjection.create(iDP,
                IDPTypeFilter.getOtherPositions(IDPProjection.allRules(iDP), IDPProjection.predefinedMap(iDP)),
                "their type is neither integer nor boolean");
    }

    private static IDPProjection create(final IDPProblem iDP, final CollectionMap<FunctionSymbol, Integer> removed,
            final String reason) {
        if (removed == null) {
            return null;
        }
        final IDPPredefinedMap predefinedMap = IDPProjection.predefinedMap(iDP);
        final Set<HasFunctionSymbols> forbiddenSymbols = new LinkedHashSet<HasFunctionSymbols>();
        forbiddenSymbols.addAll(iDP.getQ().getExplicitTerms());
        forbiddenSymbols.addAll(iDP.getP());
        forbiddenSymbols.addAll(iDP.getR());
        final Set<FunctionSymbol> takenSymbols = CollectionUtils.getFunctionSymbols(forbiddenSymbols);
        final Map<FunctionSymbol, FunctionSymbol> names = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

        final Map<Node, GeneralizedRule> pairs = new LinkedHashMap<Node, GeneralizedRule>();
        for (final Node node : iDP.getIdpGraph().getNodes()) {
            pairs.put(node, IDPProjection.project(node.getRule(), removed, names, takenSymbols, predefinedMap));
        }
        final Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>();
        for (final GeneralizedRule rule : iDP.getR()) {
            final GeneralizedRule projected = IDPProjection.project(rule, removed, names, takenSymbols, predefinedMap);
            if (IDPProjection.hasFreeVariables(projected) && !IDPProjection.hasFreeVariables(rule)) {
                // A variable only becomes free if it occurs in removed
                // arguments of the lhs and at the root of the rhs (other
                // arguments of the rhs would be removed as well). So the rule
                // computes a value of a removed sort and all calls of its root
                // symbol have been removed.
                continue;
            }
            rules.add(projected);
        }
        final boolean innermost = HelperClass.removesOnlyTupleArguments(removed, iDP.getP(), iDP.getR(),
                iDP.getQ().getExplicitTerms());
        return new IDPProjection(removed, reason, pairs, rules, innermost);
    }

    private static GeneralizedRule project(final GeneralizedRule rule,
            final CollectionMap<FunctionSymbol, Integer> removed, final Map<FunctionSymbol, FunctionSymbol> names,
            final Set<FunctionSymbol> takenSymbols, final IDPPredefinedMap predefinedMap) {
        return GeneralizedRule.create(
                (TRSFunctionApplication) HelperClass.remove(rule.getLeft(), removed, names, takenSymbols,
                        predefinedMap),
                HelperClass.remove(rule.getRight(), removed, names, takenSymbols, predefinedMap));
    }

    private static boolean hasFreeVariables(final GeneralizedRule rule) {
        return !rule.getLeft().getVariables().containsAll(rule.getRight().getVariables());
    }

    private static Set<GeneralizedRule> allRules(final IDPProblem iDP) {
        final Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>();
        rules.addAll(iDP.getR());
        rules.addAll(iDP.getP());
        return rules;
    }

    private static IDPPredefinedMap predefinedMap(final IDPProblem iDP) {
        return iDP.getRuleAnalysis().getPreDefinedMap();
    }

    /**
     * @return whether nothing is removed
     */
    public boolean isIdentity() {
        return this.removed.isEmpty();
    }

    /**
     * @return the projected pair of each node of the IDP graph
     */
    public Map<Node, GeneralizedRule> getPairs() {
        return this.pairs;
    }

    /**
     * @return the projected rules of R, without the rules that compute a
     *         value of a removed sort
     */
    public Set<GeneralizedRule> getRules() {
        return this.rules;
    }

    /**
     * @return whether only arguments of tuple symbols are removed, so that the
     *         normal forms and the terminating terms stay the same and
     *         innermost and minimal chains of the IDP stay innermost and
     *         minimal
     */
    public boolean isInnermost() {
        return this.innermost;
    }

    /**
     * @return the removed positions, for the proof
     */
    public String export(final Export_Util o) {
        final StringBuilder result = new StringBuilder();
        result.append("The following positions were removed because " + this.reason + ":");
        result.append(o.linebreak());
        for (final Map.Entry<FunctionSymbol, Collection<Integer>> entry : this.removed.entrySet()) {
            result.append("function symbol: " + entry.getKey().getName() + ", removed positions: "
                    + entry.getValue());
            result.append(o.cond_linebreak());
        }
        return result.toString();
    }
}
