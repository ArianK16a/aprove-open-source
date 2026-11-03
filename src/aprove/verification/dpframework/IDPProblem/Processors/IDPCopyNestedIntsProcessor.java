package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Copies subterms of the pairs that are nested in constructors to new
 * arguments of the root symbol, e.g. f(c(x)) becomes f(c(x), x). Then
 * {@link IDPRemoveTermProcessor} keeps integers stored in objects, which it
 * would otherwise remove together with the object.
 *
 * <p>A position below the root of a symbol of the pairs is copied if, in every
 * occurrence of the symbol, it holds a variable or a term with a predefined
 * root, and the symbols above it are the same constructors (neither
 * predefined nor defined in R). So the copy is always equal to the subterm,
 * and the conversion is EQUIVALENT. Different constructors, e.g. a call and
 * its return value, are not matched, as IDPRemoveTerm would then relate
 * unrelated integers. Positions that are already copied are skipped, so
 * applying the processor again changes nothing.</p>
 *
 * <p>The graph is rebuilt, so edges removed before are back.</p>
 */
public class IDPCopyNestedIntsProcessor extends IDPProcessor {

    @ParamsViaArgumentObject
    public IDPCopyNestedIntsProcessor(final Arguments arguments) {
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem iDP) {
        return true;
    }

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter) throws AbortionException {
        final IDPPredefinedMap predefinedMap = iDP.getRuleAnalysis().getPreDefinedMap();
        final Set<FunctionSymbol> definedInR = iDP.getRuleAnalysis().getRAnalysis().getDefinedSymbols();

        // The occurrences of the root symbols of the pairs
        final Map<FunctionSymbol, List<TRSFunctionApplication>> occurrences = new LinkedHashMap<>();
        for (final GeneralizedRule pair : iDP.getP()) {
            for (final TRSTerm side : Arrays.asList(pair.getLeft(), pair.getRight())) {
                if (side instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) side;
                    occurrences.computeIfAbsent(fa.getRootSymbol(), k -> new ArrayList<>()).add(fa);
                }
            }
        }

        final Map<FunctionSymbol, List<Position>> copies = new LinkedHashMap<>();
        for (final Map.Entry<FunctionSymbol, List<TRSFunctionApplication>> entry : occurrences.entrySet()) {
            aborter.checkAbortion();
            final List<Position> positions = IDPCopyNestedIntsProcessor.getCopyPositions(entry.getValue(),
                    predefinedMap, definedInR);
            if (!positions.isEmpty()) {
                copies.put(entry.getKey(), positions);
            }
        }
        if (copies.isEmpty()) {
            return ResultFactory.unsuccessful("There are no nested integers to copy.");
        }

        final Set<GeneralizedRule> newP = new LinkedHashSet<>();
        for (final GeneralizedRule pair : iDP.getP()) {
            newP.add(GeneralizedRule.create(
                    (TRSFunctionApplication) IDPCopyNestedIntsProcessor.copy(pair.getLeft(), copies),
                    IDPCopyNestedIntsProcessor.copy(pair.getRight(), copies)));
        }
        final RuleAnalysis<GeneralizedRule> newPAnalysis =
            new RuleAnalysis<GeneralizedRule>(ImmutableCreator.create(newP), predefinedMap);
        final IDPRuleAnalysis newAnalysis = iDP.getRuleAnalysis().change(null, newPAnalysis, null);
        final IIDependencyGraph graph = new RootConstrGraphProcessor(IItpfRule.ApplicationMode.Multistep)
            .createInitialGraph(newAnalysis, aborter);
        return ResultFactory.proved(iDP.change(graph, null, null, null, this), YNMImplication.EQUIVALENT,
                new IDPCopyNestedIntsProof(copies));
    }

    /**
     * @return the positions to copy for a symbol with the given occurrences,
     *         in the order of the first occurrence
     */
    private static List<Position> getCopyPositions(final List<TRSFunctionApplication> occurrences,
            final IDPPredefinedMap predefinedMap, final Set<FunctionSymbol> definedInR) {
        // The candidate positions with the constructors on the path to them
        Map<Position, List<FunctionSymbol>> positions = null;
        for (final TRSFunctionApplication occurrence : occurrences) {
            final Map<Position, List<FunctionSymbol>> current = new LinkedHashMap<>();
            IDPCopyNestedIntsProcessor.collectLeaves(occurrence, Position.create(), new ArrayList<FunctionSymbol>(),
                    predefinedMap, definedInR, current);
            if (positions == null) {
                positions = current;
            } else {
                positions.entrySet().removeIf(e -> !e.getValue().equals(current.get(e.getKey())));
            }
        }
        final List<Position> result = new ArrayList<>();
        for (final Position pos : positions.keySet()) {
            if (!IDPCopyNestedIntsProcessor.isCopied(pos, occurrences)) {
                result.add(pos);
            }
        }
        return result;
    }

    /**
     * Collects the positions of depth at least 2 below <code>pos</code> that
     * hold a variable or a term with a predefined root and are only below
     * constructors, together with these constructors.
     */
    private static void collectLeaves(final TRSFunctionApplication term, final Position pos,
            final List<FunctionSymbol> path, final IDPPredefinedMap predefinedMap,
            final Set<FunctionSymbol> definedInR, final Map<Position, List<FunctionSymbol>> result) {
        for (int i = 0; i < term.getArity(); i++) {
            final TRSTerm arg = term.getArgument(i);
            final Position argPos = pos.append(i);
            if (arg.isVariable() || predefinedMap.isPredefined(((TRSFunctionApplication) arg).getRootSymbol())) {
                if (argPos.getDepth() >= 2) {
                    result.put(argPos, path);
                }
            } else if (!definedInR.contains(((TRSFunctionApplication) arg).getRootSymbol())) {
                final List<FunctionSymbol> argPath = new ArrayList<>(path);
                argPath.add(((TRSFunctionApplication) arg).getRootSymbol());
                IDPCopyNestedIntsProcessor.collectLeaves((TRSFunctionApplication) arg, argPos, argPath,
                        predefinedMap, definedInR, result);
            }
        }
    }

    /**
     * @return whether some argument is equal to the subterm at
     *         <code>pos</code> in every occurrence
     */
    private static boolean isCopied(final Position pos, final List<TRSFunctionApplication> occurrences) {
        final int arity = occurrences.get(0).getArity();
        argLoop: for (int i = 0; i < arity; i++) {
            for (final TRSFunctionApplication occurrence : occurrences) {
                if (!occurrence.getArgument(i).equals(occurrence.getSubterm(pos))) {
                    continue argLoop;
                }
            }
            return true;
        }
        return false;
    }

    private static TRSTerm copy(final TRSTerm term, final Map<FunctionSymbol, List<Position>> copies) {
        if (!(term instanceof TRSFunctionApplication)) {
            return term;
        }
        final TRSFunctionApplication fa = (TRSFunctionApplication) term;
        final List<Position> positions = copies.get(fa.getRootSymbol());
        if (positions == null) {
            return term;
        }
        final List<TRSTerm> args = new ArrayList<TRSTerm>(fa.getArguments());
        for (final Position pos : positions) {
            args.add(fa.getSubterm(pos));
        }
        final FunctionSymbol newRoot = FunctionSymbol.create(fa.getRootSymbol().getName(), args.size());
        return TRSTerm.createFunctionApplication(newRoot, ImmutableCreator.create(args));
    }

    public static class IDPCopyNestedIntsProof extends DefaultProof {
        private final Map<FunctionSymbol, List<Position>> copies;

        public IDPCopyNestedIntsProof(final Map<FunctionSymbol, List<Position>> copies) {
            this.copies = copies;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();
            result.append("The subterms at the following positions were copied to new arguments:");
            result.append(o.linebreak());
            for (final Map.Entry<FunctionSymbol, List<Position>> entry : this.copies.entrySet()) {
                result.append("function symbol: " + entry.getKey().getName() + ", copied positions: "
                        + entry.getValue());
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }
    }

    public static class Arguments {
    }
}
