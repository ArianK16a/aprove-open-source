package aprove.verification.theoremprover.ObligationFactories;

import java.util.*;

import javax.swing.*;

import aprove.*;
import aprove.input.Programs.c.*;
import aprove.input.Programs.jbc.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.input.Programs.t2.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.confluence.*;
import aprove.verification.diophantine.*;
import aprove.verification.dpframework.CLSProblem.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.dpframework.LCTRSProblem.*;
import aprove.verification.dpframework.MCSProblem.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import aprove.verification.theoremprover.TheoremProver.*;

/**
 * @author Stephan Swiderski
 */
public class MetaObligationFactory implements ObligationFactory {

    @Override
    public void clearResult(final AnnotatedInput annotatedInput) {
        if (annotatedInput.getAnnotation() instanceof FormulaAnnotation) {
            ((FormulaAnnotation)annotatedInput.getAnnotation()).clearResult();
        }
    }

    @Override
    public Pair<ObligationNode, List<BasicObligationNode>> getRootAndPositions(final AnnotatedInput annotatedInput) {
        final TypedInput typedInput = annotatedInput.getTypedInput();
        final Language type = typedInput.getLanguage();

        ObligationNode root;
        List<BasicObligationNode> positions;
        if (annotatedInput.getAnnotation() instanceof FormulaAnnotation) {
            // needed for the theorem prover
            final FormulaAnnotation formulaAnnotation = (FormulaAnnotation)annotatedInput.getAnnotation();
            root = formulaAnnotation.getRoot();
            positions = formulaAnnotation.getPositions();
        } else if (typedInput.getHandlingMode().equals(HandlingMode.RuntimeComplexity)) {
            final BasicObligationNode node =
                new BasicObligationNode(this.getRuntimeComplexityBasicObligation(annotatedInput));
            root = node;
            positions = new ArrayList<>(1);
            positions.add(node);
        } else if (typedInput.getHandlingMode().equals(HandlingMode.Termination)) {
            final BasicObligationNode node =
                new BasicObligationNode(this.getTerminationBasicObligation(annotatedInput));
            root = node;
            positions = new ArrayList<>(1);
            positions.add(node);
        } else if (typedInput.getHandlingMode().equals(HandlingMode.Satisfiability)) {
            final BasicObligationNode node =
                new BasicObligationNode(this.getSatisfiabilityBasicObligation(annotatedInput));
            root = node;
            positions = Collections.singletonList(node);
        } else {
            System.err.println("The combination of "
                + type
                + " and "
                + typedInput.getHandlingMode()
                + " has not yet been implemented.");
            root = null;
            positions = null;
        }
        return new Pair<>(root, positions);
    }

    private BasicObligation getRuntimeComplexityBasicObligation(final AnnotatedInput annotatedInput) {
        final TypedInput typedInput = annotatedInput.getTypedInput();
        final Language type = typedInput.getLanguage();
        switch (type) {
        case CpxTRS:
        case CpxITrs:
        case CpxIntTrs:
        case CpxRelTRS:
        case CpxPTRS:
            return (BasicObligation)typedInput.getInput();
        default:
            throw new IllegalStateException("No suitable type found!");
        }
    }

    private BasicObligation getSatisfiabilityBasicObligation(final AnnotatedInput annotatedInput) {
        final TypedInput typedInput = annotatedInput.getTypedInput();
        final Language type = typedInput.getLanguage();
        if (type.equals(Language.DIOPHANTINE)) {
            return (DiophantineConstraints) typedInput.getInput();
        }
        throw new IllegalArgumentException("Expected diophantine language!");
    }

    private BasicObligation getTerminationBasicObligation(final AnnotatedInput annotatedInput) {
        final TypedInput typedInput = annotatedInput.getTypedInput();
        final Annotation annotation = annotatedInput.getAnnotation();
        final Object input = typedInput.getInput();
        switch (typedInput.getLanguage()) {
        case TES:
            final TESAnnotation TESanno = (TESAnnotation)annotation;
            return new TRS(((Program)input), TESanno.getInnermost());
        case TRS:
            return new TRS(((Program)input), ((Program)input).getStrategy() == Program.INNERMOST);
        case SES:
            final SESAnnotation SESanno = (SESAnnotation)annotation;
            return new TRS(((Program)input), SESanno.getInnermost());
        case SRS:
            return new TRS(((Program)input), ((Program)input).getStrategy() == Program.INNERMOST);
        case CSR:
            return (CSRProblem)input;
        case GTRS:
            return (GTRSProblem)input;
        case OTRS:
            return (OTRSProblem)input;
        case CLS:
            return (CLSProblem)input;
        case CTRS:
            return (CTRSProblem)input;
        case FP:
            return new TRS(((ProgramContainingFormulas)input).getProgram(), true);
        case IDP:
            return (aprove.verification.idpframework.Core.IDPProblem)input;
        case ITRS:
            return (ITRSProblem)input;
        case IPAD:
            return new TRS(((Program)input), true);
        case PROLOG:
            final Pair<PrologProgram, PrologQuery> pair = ((ParsedProlog)input);
            final String query = ((NewPrologAnnotation)annotation).getQuery();
            if (query != null) {
                return
                    new PrologProblem(
                        pair.x,
                        aprove.input.Programs.prolog.Translator.parseQuery(query),
                        PrologProblem.DEFAULT_SMT_FACTORY,
                        PrologProblem.DEFAULT_SMT_LOGIC
                    );
            } else {
                PrologQuery q = pair.y;
                if (q == null) {
                    if (Main.UI_MODE == Main.UI.GUI) {
                        final PrologQueryDialog diag = new PrologQueryDialog(pair.x);
                            SwingUtilities.invokeLater(
                                new Runnable() {

                                    @Override
                                    public void run() {
                                        diag.setVisible(true);
                                    }

                                }
                            );
                        synchronized (diag) {
                            while (!diag.isDone()) {
                                try {
                                    diag.wait();
                                } catch (InterruptedException e) {
                                    throw new IllegalStateException(
                                        "No query has been specified in the program and user input has been interrupted!"
                                    );
                                }
                            }
                        }
                        q = diag.getQuery();
                        diag.dispose();
                    } else {
                        throw new NullPointerException("No query has been specified!");
                    }
                }
                return new PrologProblem(pair.x, q, PrologProblem.DEFAULT_SMT_FACTORY, PrologProblem.DEFAULT_SMT_LOGIC);
            }
        case HASKELL:
            HaskellAnnotation ha = (HaskellAnnotation)annotation;
            ((HaskellProgram)input).setAnnotation(ha);
            return (HaskellProgram)input;
        case QDP:
            return (QDPProblem)input;
        case QTRS:
            return (QTRSProblem)input;
        case RTRS:
            return (RelTRSProblem)input;
        case ETRS:
            return (ETRSProblem)input;
        case ETES:
            return new TRS(((Program)input), false);
        case MCS:
            return (MCSProblem)input;
        case PATRS:
            return (PATRSProblem)input;
        case CSPATRS:
            return (CSPATRSProblem)input;
        case JBC:
            final JBCProgram jbcProgram = (JBCProgram)input;
            final JBCAnnotation jbcAnnotation = (JBCAnnotation)annotation;

            final ClassStreamProvider jbcProgramStream = ClassStreamProvider.create(jbcProgram.getInput(), ClassStreamProvider.Type.UserDefined);

            final aprove.input.Programs.jbc.Translator translator =
                new aprove.input.Programs.jbc.Translator();
            translator.parseMethodString(jbcAnnotation.getStartMethodString());
            translator.parseAnnotationsString(jbcAnnotation.getAnnotationsString());

            return new BareJBCProblem(translator, jbcProgramStream, jbcAnnotation.getGoal());
        case TRIPLES:
            return (aprove.input.Programs.triples.TriplesProblem)input;
        case LLVM:
            return (LLVMProblem)input;
        case T2:
            return (T2IntSys)input;
        case INTTRS:
            return (IRSwTProblem)input;
        case LCTRS:
            return (LCTRSProblem)input;
        case C:
            return (CProblem)input;
        case PTRS:
            return (PTRSProblem)input;
        case ConfTRS:
            return (ConfTRSProblem)input;
        default:
            throw new IllegalStateException("Did not find suitable type!");
        }
    }

}
