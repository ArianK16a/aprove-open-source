package aprove.verification.dpframework.IDPProblem.Processors;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.xml.*;

/**
 * Base class for IDPProblem processors. Takes care of really simple cases.
 *
 * @author noschinski
 *
 */
public abstract class IDPProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process an IDP problem; called after the really simple cases are already
     * handled. For semantics see semantics of {@link Processor#process}
     *
     * @param idp Basic Obligation
     */
    protected abstract Result processIDPProblem(IDPProblem idp, Abortion aborter) throws AbortionException;

    protected RuntimeInformation rti;

    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        IDPProblem problem = (IDPProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getP().isEmpty()) { // success for free!
            return ResultFactory.proved(IDPProcessor.pIsEmptyProof);
        }
        this.rti = rti;
        // FIXME: We will probably have some simple abortion cases here
        // (cached, ...) cf. QDPProblemProcessor
        return this.processIDPProblem(problem, aborter);
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof IDPProblem) {
            return this.isIDPApplicable((IDPProblem) o);
        }
        return false;
    }

    /**
     * Is the IDP processor applicable to this idp?
     *
     * @param idp Problem to check for applicability
     * @return True, iff the processor is applicable
     */
    public abstract boolean isIDPApplicable(IDPProblem idp);

    final static Proof pIsEmptyProof = new PisEmptyProof();

    private static final class PisEmptyProof extends Proof {

        @Override
        public String export(final Export_Util o) {
            return o.export("The TRS P is empty. Hence, there is no (P,Q,R) chain.");
        }

        public String toBibTeX() {
            return "";
        }

        @Override
        public Element toDOM(final Document doc, final XMLMetaData xmlMetaStorage) {
            return XMLTag.P_IS_EMPTY_PROOF.createElement(doc);
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaStorage,
            final CPFModus modus
        ) {
            return CPFTag.P_IS_EMPTY.createElement(doc);
        }

    }
}
