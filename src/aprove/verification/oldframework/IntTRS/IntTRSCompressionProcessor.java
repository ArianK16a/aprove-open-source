package aprove.verification.oldframework.IntTRS;

import java.util.*;
import java.util.Collections;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IntTRS.Compression.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Compresses intTRS. Leaves air in.
 *
 * @author Marc Brockschmidt
 */
public class IntTRSCompressionProcessor extends Processor.ProcessorSkeleton {

    public static class Args {
        public boolean filterFreeVariablesFromConditions = false;
        public boolean normalize = true;
        public boolean cleanConstraints = true;
    }

    private Args args;

    @ParamsViaArgumentObject 
    public IntTRSCompressionProcessor(Args args) {
        this.args = args;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSLike && Options.certifier.isNone();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
        {
        final IRSLike intTRS = (IRSLike) obl;
        final Set<IGeneralizedRule> rules = intTRS.getRules();

        final Set<FunctionSymbol> dontRemove;
        if (intTRS.getStartTerm() != null) {
            dontRemove = Collections.singleton(intTRS.getStartTerm().getRootSymbol());
        } else {
            dontRemove = Collections.<FunctionSymbol>emptySet();
        }

        RuleCombiner combiner = new RuleCombiner(rules, dontRemove, aborter);
        Pair<Boolean, Set<IGeneralizedRule>> res = combiner.combineRules(args.filterFreeVariablesFromConditions, args.cleanConstraints);

        if (res.x.booleanValue()) {
            Set<IGeneralizedRule> newRules = res.y;
            if (args.normalize) {
                newRules = TerminationSCCToIDPv1Processor.removeTrivialConstraints(res.y, IDPPredefinedMap.DEFAULT_MAP);
                newRules = TerminationSCCToIDPv1Processor.removePredefinedOpsOnLhs(newRules, IDPPredefinedMap.DEFAULT_MAP);
                // this is not sound for IRSwTs, as it might move variables of type TERM to the condition
                if (intTRS instanceof IRSProblem) {
                    newRules = IRSwTFormatTransformer.makeLhsLinear(newRules, IDPPredefinedMap.DEFAULT_MAP);
                }
            }

            if (newRules.isEmpty()) {
                // Without rules, the termination problem is solved
                return ResultFactory.proved(new IntTRSCompressionProof());
            }
            return ResultFactory.proved(intTRS.create(newRules, intTRS.getStartTerm()), YNMImplication.EQUIVALENT, new IntTRSCompressionProof());
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    /**
     * The proof for this processor giving information about the removed positions.
     * @author Marc Brockschmidt
     */
    public static class IntTRSCompressionProof extends DefaultProof {
        /**
         * @return the proof as a nice string representation.
         * @param o an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Compressed rules.";
        }
    }
}
