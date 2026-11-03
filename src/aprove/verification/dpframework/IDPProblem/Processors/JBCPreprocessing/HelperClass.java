package aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * A bundle of useful things.
 * @author cotto
 */
public final class HelperClass {
    /**
     * No.
     */
    private HelperClass() {
    }

    /**
     * @param newRules the new rules
     * @return a new Q termset for all LHS of the new rules
     */
    public static QTermSet getNewQ(final Collection<GeneralizedRule> newRules) {
        final Collection<TRSFunctionApplication> lhs =
            new LinkedHashSet<TRSFunctionApplication>();
        for (final GeneralizedRule rule : newRules) {
            lhs.add(rule.getLeft());
        }
        return new QTermSet(lhs);
    }

    /**
     * Remove the given arguments and generate fresh names if needed.
     * @param term the old term
     * @param removePositions information positions to remove
     * @param names the name mapping
     * @param takenSymbols the function symbols that are already in use and may
     * not be used again
     * @param predefinedMap information about predefined symbols
     * @return a new function application where some arguments may be removed
     */
    public static TRSTerm remove(final TRSTerm term,
        final CollectionMap<FunctionSymbol, Integer> removePositions,
        final Map<FunctionSymbol, FunctionSymbol> names,
        final Collection<FunctionSymbol> takenSymbols,
        final IDPPredefinedMap predefinedMap) {
        if (!(term instanceof TRSFunctionApplication)) {
            return term;
        }
        final TRSFunctionApplication fa = (TRSFunctionApplication) term;
        final FunctionSymbol sym = fa.getRootSymbol();
        final Collection<Integer> remove = removePositions.getNotNull(sym);
        // do we already have the new symbol?
        final int newArity = sym.getArity() - remove.size();
        final String oldName = sym.getName();
        FunctionSymbol newFs;
        if (remove.isEmpty()) {
            newFs = sym;
            names.put(sym, sym);
        } else {
            newFs = names.get(sym);
        }

        if (newFs == null) {
            // no, so just generate a fresh one
            String newName = oldName;
            newFs = FunctionSymbol.create(newName, newArity);
            int counter = 0;
            while (takenSymbols.contains(newFs)
                || predefinedMap.isPredefined(newFs)) {
                newName = oldName + counter;
                newFs = FunctionSymbol.create(newName, newArity);
                counter++;
            }
            names.put(sym, newFs);
            takenSymbols.add(newFs);
        }

        // create an function application for the symbol
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(newArity);
        for (int i = 0; i < sym.getArity(); i++) {
            final TRSTerm arg = fa.getArgument(i);
            final TRSTerm removed =
                HelperClass.remove(arg, removePositions, names, takenSymbols, predefinedMap);
            if (!remove.contains(Integer.valueOf(i))) {
                args.add(removed);
            }
        }
        return TRSTerm.createFunctionApplication(newFs, args);
    }

    /**
     * Checks whether only arguments of tuple symbols are removed, i.e. of
     * symbols that do not occur in R, in Q or in the kept arguments of the
     * pairs. Then the kept arguments of the pairs, R and Q stay the same, so
     * the normal forms and the terminating terms do not change. Otherwise, a
     * left-hand side may match more terms after the removal.
     *
     * @param removePositions the positions to remove, or <code>null</code>
     */
    public static boolean removesOnlyTupleArguments(final CollectionMap<FunctionSymbol, Integer> removePositions,
            final Collection<? extends GeneralizedRule> pairs, final Collection<? extends GeneralizedRule> rules,
            final Collection<TRSFunctionApplication> qTerms) {
        if (removePositions == null || removePositions.isEmpty()) {
            return true;
        }
        final Set<FunctionSymbol> nonTupleSymbols = new LinkedHashSet<FunctionSymbol>();
        nonTupleSymbols.addAll(CollectionUtils.getFunctionSymbols(rules));
        nonTupleSymbols.addAll(CollectionUtils.getFunctionSymbols(qTerms));
        for (final GeneralizedRule pair : pairs) {
            for (final TRSTerm side : Arrays.asList(pair.getLeft(), pair.getRight())) {
                if (side instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) side;
                    final Collection<Integer> remove = removePositions.getNotNull(fa.getRootSymbol());
                    for (int i = 0; i < fa.getArguments().size(); i++) {
                        if (!remove.contains(i)) {
                            nonTupleSymbols.addAll(fa.getArgument(i).getFunctionSymbols());
                        }
                    }
                }
            }
        }
        for (final Map.Entry<FunctionSymbol, Collection<Integer>> entry : removePositions.entrySet()) {
            if (!entry.getValue().isEmpty() && nonTupleSymbols.contains(entry.getKey())) {
                return false;
            }
        }
        return true;
    }

    /**
     * Remove the given arguments of all terms, construct a new ITRS and return
     * it. In addition, information about renamed symbols is returned.
     * @param itrs the itrs
     * @param removedPositions information about arguments that can be removed
     * @return a result with a new ITRS
     */
    public static Pair<ITRSProblem, Map<FunctionSymbol, FunctionSymbol>> getResultingITRS(final ITRSProblem itrs,
        final CollectionMap<FunctionSymbol, Integer> removedPositions) {
        return HelperClass.getResultingITRS(itrs, removedPositions,
            new LinkedHashSet<FunctionSymbol>());
    }

    /**
     * Remove the given arguments of all terms, construct a new ITRS and return
     * it. In addition, information about renamed symbols is returned.
     * @param itrs the itrs
     * @param removedPositions information about arguments that can be removed
     * @param takenSymbols the function symbols that are already in use and may
     * not be used again
     * @return a result with a new ITRS
     */
    public static Pair<ITRSProblem, Map<FunctionSymbol, FunctionSymbol>> getResultingITRS(final ITRSProblem itrs,
        final CollectionMap<FunctionSymbol, Integer> removedPositions,
        final Collection<FunctionSymbol> takenSymbols) {

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> p =
            HelperClass.getResultingRules(itrs.getR(), itrs.getPredefinedMap(), removedPositions, takenSymbols);
        final Set<GeneralizedRule> newRules = p.x;
        final Map<FunctionSymbol, FunctionSymbol> names = p.y;

        final IQTermSet newQ = new IQTermSet(HelperClass.getNewQ(newRules), itrs.getPredefinedMap());
        final ITRSProblem newItrs = ITRSProblem.create(newRules, newQ);
        return new Pair<ITRSProblem, Map<FunctionSymbol, FunctionSymbol>>(
            newItrs, names);
    }

    /**
     * Remove the given arguments of all terms, construct a new rule set and
     * return it. In addition, information about renamed symbols is returned.
     * @param rules the rule set
     * @param predefinedMap the predefined map of this rule set
     * @param removedPositions information about arguments that can be removed
     * @param takenSymbols the function symbols that are already in use and may
     * not be used again
     * @return a result with a new ITRS
     */
    public static Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> getResultingRules(final Set<GeneralizedRule> rules,
            final IDPPredefinedMap predefinedMap,
            final CollectionMap<FunctionSymbol, Integer> removedPositions,
            final Collection<FunctionSymbol> takenSymbols) {
        // the rules of the new ITRS
        final Set<GeneralizedRule> newRules =
            new LinkedHashSet<GeneralizedRule>(rules.size());

        // helper for name generation
        final Map<FunctionSymbol, FunctionSymbol> names =
            new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

        // for uninteresting symbols do not change the name
        final Collection<FunctionSymbol> symbols =
            new LinkedHashSet<FunctionSymbol>();
        for (final GeneralizedRule rule : rules) {
            symbols.addAll(rule.getLeft().getFunctionSymbols());
            symbols.addAll(rule.getRight().getFunctionSymbols());
        }
        symbols.removeAll(removedPositions.keySet());
        for (final FunctionSymbol fs : symbols) {
            final boolean added = takenSymbols.add(fs);
            assert (added);
            names.put(fs, fs);
        }

        for (final GeneralizedRule rule : rules) {
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSFunctionApplication newLhs =
                (TRSFunctionApplication)
                HelperClass.remove(lhs, removedPositions, names, takenSymbols, predefinedMap);
            final TRSTerm rhs = rule.getRight();
            TRSTerm newRhs;
            if (!rhs.isVariable()) {
                newRhs =
                    HelperClass.remove(rhs, removedPositions, names,
                        takenSymbols, predefinedMap);
            } else {
                newRhs = rhs;
            }
            final GeneralizedRule newRule =
                GeneralizedRule.create(newLhs, newRhs);
            newRules.add(newRule);
        }

        return new Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>(newRules, names);
    }

    /**
     * Checks if the ITRS has the right format. If so, create a handy graph out
     * of it and get some nice properties of this graph.
     * @param itrs some ITRS problem
     * @param computeInterestingNodes iff true, some interesting nodes are
     * computed during SCC computation
     * @return a graph representing the calls of the ITRS and its SCCs
     */
    public static Pair<MultiGraph<FunctionSymbol, GeneralizedRule>, Collection<Cycle<FunctionSymbol>>> toGraph(final ITRSProblem itrs,
        final boolean computeInterestingNodes) {
        /*
         * First it is checked if the ITRS has the right format. We need at
         * least one SCC. The idea here is to handle ITRSs that essentially
         * are P cup R, where P results in the SCCs and the rules of R are not
         * involved.
         * Furthermore, every function symbol taking part in one SCC may not be
         * used as an argument or outside the SCC. In the following example, no
         * symbol is allowed to be part of the SCC.
         * G(x) -> F(x)
         * F(x) -> G(G(x))
         * H(x) -> x
         */

        final MultiGraph<FunctionSymbol, GeneralizedRule> graph =
            new MultiGraph<FunctionSymbol, GeneralizedRule>();
        final Map<FunctionSymbol, Node<FunctionSymbol>> fsToNode =
            new LinkedHashMap<FunctionSymbol, Node<FunctionSymbol>>();
        final Collection<FunctionSymbol> notInScc =
            new LinkedHashSet<FunctionSymbol>();

        // Build a graph based on the function symbols used in the rules
        for (final GeneralizedRule rule : itrs.getR()) {
            final TRSFunctionApplication lhsFA = rule.getLeft();
            final FunctionSymbol leftFS = lhsFA.getRootSymbol();
            // Forbid all function applications hidden inside the LHS
            HelperClass.removeNestedFunctionSymbols(lhsFA, notInScc, graph, fsToNode);

            final TRSTerm rhs = rule.getRight();
            if (rhs.isVariable()) {
                // F(...) -> x, so F is not good
                HelperClass.forbid(leftFS, fsToNode, graph, notInScc);
                continue;
            }
            final TRSFunctionApplication rhsFA = (TRSFunctionApplication) rhs;

            // Forbid all function applications hidden inside the RHS
            HelperClass.removeNestedFunctionSymbols(rhsFA, notInScc, graph, fsToNode);

            if (notInScc.contains(leftFS)) {
                continue;
            }

            final FunctionSymbol rightFS = rhsFA.getRootSymbol();
            if (notInScc.contains(rightFS)) {
                HelperClass.forbid(leftFS, fsToNode, graph, notInScc);
                continue;
            }

            final Node<FunctionSymbol> nodeLeft = HelperClass.getNode(leftFS, fsToNode);
            final Node<FunctionSymbol> nodeRight = HelperClass.getNode(rightFS, fsToNode);
            graph.addEdge(nodeLeft, nodeRight, rule);
        }

        /*
         * Now we should have at least one SCC of the form
         * F(...) -> G(...) -> ... -> F(...)
         */
        final Collection<Cycle<FunctionSymbol>> sccs =
            graph.getSCCsWithInterestingNodes(computeInterestingNodes);
        if (sccs.isEmpty()) {
            return null;
        }
        for (final Cycle<FunctionSymbol> scc : sccs) {
            for (final FunctionSymbol fs : scc.getNodeObjects()) {
                if (notInScc.contains(fs)) {
                    assert (false);
                    return null;
                }
            }
        }
        return new Pair<MultiGraph<FunctionSymbol, GeneralizedRule>, Collection<Cycle<FunctionSymbol>>>(
            graph, sccs);
    }

    /**
     * Have a look at the given function application. For every nested function
     * application the corresponding symbol is forbidden to be used in the SCC
     * and the graph is cleaned of corresponding nodes.
     * @param fa the function application to analyze
     * @param notInScc the function symbols that will not be used for the SCC
     * @param graph the current graph
     * @param fsToNode a map giving nodes for symbols
     */
    private static void removeNestedFunctionSymbols(final TRSFunctionApplication fa,
        final Collection<FunctionSymbol> notInScc,
        final MultiGraph<FunctionSymbol, GeneralizedRule> graph,
        final Map<FunctionSymbol, Node<FunctionSymbol>> fsToNode) {
        final Collection<TRSTerm> todo = fa.getSubTerms();
        todo.remove(fa);
        for (final TRSTerm termTodo : todo) {
            if (termTodo.isVariable()) {
                continue;
            }
            final TRSFunctionApplication faTodo = (TRSFunctionApplication) termTodo;
            final FunctionSymbol fs = faTodo.getRootSymbol();
            /*
             * This symbol is used as an argument, so we cannot use it to
             * construct any SCC.
             */
            HelperClass.forbid(fs, fsToNode, graph, notInScc);
        }
    }


    /**
     * The given function symbol is not allowed to be part of the SCC. As a
     * consequence, all nodes connecting to its node are also not allowed. This
     * removal process therefore is recursive.
     * @param fs a function symbol
     * @param fsToNode a map giving nodes for symbols
     * @param graph the current graph
     * @param notInScc the function symbols that will not be used for the SCC
     */
    private static void forbid(final FunctionSymbol fs,
        final Map<FunctionSymbol, Node<FunctionSymbol>> fsToNode,
        final MultiGraph<FunctionSymbol, GeneralizedRule> graph,
        final Collection<FunctionSymbol> notInScc) {
        if (notInScc.contains(fs)) {
            return;
        }
        notInScc.add(fs);
        final Node<FunctionSymbol> node = fsToNode.get(fs);
        if (node == null) {
            return;
        }
        for (final EdgeEquality<GeneralizedRule, FunctionSymbol> edge : new LinkedHashSet<EdgeEquality<GeneralizedRule, FunctionSymbol>>(
            graph.getInEdges(node))) {
            HelperClass.forbid(edge.getStartNode().getObject(), fsToNode, graph, notInScc);
        }
        for (final EdgeEquality<GeneralizedRule, FunctionSymbol> edge : new LinkedHashSet<EdgeEquality<GeneralizedRule, FunctionSymbol>>(
            graph.getOutEdges(node))) {
            HelperClass.forbid(edge.getEndNode().getObject(), fsToNode, graph, notInScc);
        }
        graph.removeNode(node);
    }

    /**
     * @param fs a function symbol
     * @param fsToNode a map from function symbols to nodes
     * @return the node for the given function symbol
     */
    private static Node<FunctionSymbol> getNode(final FunctionSymbol fs,
        final Map<FunctionSymbol, Node<FunctionSymbol>> fsToNode) {
        Node<FunctionSymbol> result = fsToNode.get(fs);
        if (result == null) {
            result = new Node<FunctionSymbol>(fs);
            fsToNode.put(fs, result);
        }
        return result;
    }

    /**
     * For the given graph, mark the arguments of every function symbol that are
     * unchanged throughout the SCCs.
     * @param scc some SCC
     * @param graph the graph for the SCC.
     * @return the arguments that are unchanged throughout the SCC.
     */
    public static CollectionMap<FunctionSymbol, Integer> getUnchangedPositions(final MultiGraph<FunctionSymbol, GeneralizedRule> graph,
        final Cycle<FunctionSymbol> scc) {
        final CollectionMap<FunctionSymbol, Integer> unchangedPositions =
            new CollectionMap<FunctionSymbol, Integer>();
        final Equalities equalities = new Equalities();
        final MultiGraph<FunctionSymbol, GeneralizedRule> subGraph =
            graph.getSubGraph(scc);
        // For every rule, get the changes along that rule
        for (final EdgeEquality<GeneralizedRule, FunctionSymbol> edge : subGraph.getEdges()) {
            for (final GeneralizedRule rule : edge.getObject()) {
                equalities.equalityForRule(rule.getLeft(),
                    (TRSFunctionApplication) rule.getRight());
            }
        }

        /*
         * Now, for each SCC, merge the maps with "no change" edges
         * together, so we know which arguments of the function symbol used
         * to start the construction are unchanged through the whole SCC.
         * We also check if a variable at such an unchanged position occurs
         * inside some function application on the RHS. If so, we will not
         * delete the corresponding position.
         */
        // I brake together!
        equalities.puzzleTogether(subGraph, unchangedPositions);
        return unchangedPositions;
    }

    /**
     * Mark all function symbols in the given rules as used.
     * @param rules some rules
     * @param takenSymbols a collection of function symbols that are marked as
     * "in use".
     */
    public static void mark(final Collection<GeneralizedRule> rules,
        final Collection<FunctionSymbol> takenSymbols) {
        for (final GeneralizedRule rule : rules) {
            for (final TRSTerm term : rule.getTerms()) {
                if (term instanceof TRSFunctionApplication) {
                    final FunctionSymbol sym =
                        ((TRSFunctionApplication) term).getRootSymbol();
                    takenSymbols.add(sym);
                }
            }
        }
    }
}
