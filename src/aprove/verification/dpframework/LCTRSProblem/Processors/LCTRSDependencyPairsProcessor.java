package aprove.verification.dpframework.LCTRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.LCTRSProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Computes the dependency pairs of an LCTRS: <code>l# -> p# [phi]</code> for every rule
 * <code>l -> r [phi]</code> and every subterm p of r with a defined symbol at its root. The LCTRS is
 * terminating iff the dependency pair problem (DP(R), R) is finite.
 */
public class LCTRSDependencyPairsProcessor extends Processor.ProcessorSkeleton {

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof LCTRSProblem;
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        final LCTRSProblem lctrs = (LCTRSProblem) obl;
        final LCTRSSignature signature = lctrs.getSignature();

        // the tuple symbols and their sort
        String dpSortName = "dpsort";
        while (signature.sorts().contains(LCTRSSort.user(dpSortName))) {
            dpSortName += "'";
        }
        final LCTRSSort dpSort = LCTRSSort.user(dpSortName);
        final Set<FunctionSymbol> allSymbols = new LinkedHashSet<>(signature.functions().keySet());
        allSymbols.addAll(signature.theorySymbols().keySet());
        allSymbols.addAll(signature.userTheorySymbols().keySet());
        final Map<FunctionSymbol, FunctionSymbol> tupleSymbols = new LinkedHashMap<>();
        final Map<FunctionSymbol, LCTRSSortDeclaration> declarations = new LinkedHashMap<>(signature.functions());
        for (final FunctionSymbol f : lctrs.getDefinedSymbols()) {
            final FunctionSymbol tuple = QTRSProblem.getTupleSymbol(f, tupleSymbols, allSymbols);
            declarations.put(tuple, new LCTRSSortDeclaration(signature.functions().get(f).argumentSorts(), dpSort));
        }

        final List<LCTRSRule> pairs = new ArrayList<>();
        for (final LCTRSRule rule : lctrs.getRules()) {
            aborter.checkAbortion();
            final TRSFunctionApplication left = rule.left();
            final TRSFunctionApplication tupleLeft =
                TRSTerm.createFunctionApplication(tupleSymbols.get(left.getRootSymbol()), left.getArguments());
            for (final TRSFunctionApplication subterm : rule.right().getNonVariableSubTerms()) {
                final FunctionSymbol tuple = tupleSymbols.get(subterm.getRootSymbol());
                if (tuple != null) {
                    final TRSTerm tupleRight = TRSTerm.createFunctionApplication(tuple, subterm.getArguments());
                    final Map<TRSVariable, LCTRSSort> variableSorts = new LinkedHashMap<>(rule.variableSorts());
                    final Set<TRSVariable> occurring = new LinkedHashSet<>(left.getVariables());
                    occurring.addAll(tupleRight.getVariables());
                    occurring.addAll(rule.guard().getVariables());
                    variableSorts.keySet().retainAll(occurring);
                    final LCTRSRule pair = new LCTRSRule(tupleLeft, tupleRight, rule.guard(), variableSorts);
                    if (!pairs.contains(pair)) {
                        pairs.add(pair);
                    }
                }
            }
        }

        final Set<LCTRSSort> sorts = new LinkedHashSet<>(signature.sorts());
        sorts.add(dpSort);
        final LCTRSSignature dpSignature =
            new LCTRSSignature(
                signature.theories(),
                sorts,
                declarations,
                signature.theorySymbols(),
                signature.userTheorySymbols());
        return ResultFactory.proved(
            new LCTRSDPProblem(dpSignature, dpSort, pairs, lctrs.getRules()),
            YNMImplication.EQUIVALENT,
            new LCTRSDependencyPairsProof());
    }

    /**
     * The proof of the dependency pair transformation.
     */
    private static class LCTRSDependencyPairsProof extends Proof.DefaultProof {

        private LCTRSDependencyPairsProof() {
            this.setShortName("LCTRSDependencyPairsProof");
            this.setLongName("Dependency Pairs");
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Computed the dependency pairs of the LCTRS. It is terminating iff they have no infinite chain.";
        }

    }

}
