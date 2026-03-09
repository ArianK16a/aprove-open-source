/**
 *
 * @author 
 * @version $Id$
 */

package aprove.DPFramework.IDPProblem.Processors;

import immutables.Immutable.*;

import java.util.*;
import java.util.Map.*;
import java.util.logging.*;

import aprove.Complexity.LowerBounds.Types.*;
import aprove.DPFramework.*;
import aprove.DPFramework.BasicStructures.*;
import aprove.DPFramework.DPProblem.*;
import aprove.DPFramework.IDPProblem.*;
import aprove.DPFramework.IDPProblem.PfManager.*;
import aprove.DPFramework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.DPFramework.IDPProblem.idpGraph.*;
import aprove.DPFramework.IDPProblem.idpGraph.Node;
import aprove.DPFramework.IDPProblem.utility.*;
import aprove.DPFramework.TRSProblem.*;
import aprove.Framework.BasicStructures.*;
import aprove.Framework.IRSwT.Processors.FilterProcessors.IRSwTTempSortFilterProcessor.*;
import aprove.Framework.IntTRS.*;
import aprove.Framework.Logic.*;
import aprove.Framework.Utility.*;
import aprove.Framework.Utility.GenericStructures.*;
import aprove.Framework.Utility.Graph.*;
import aprove.GraphUserInterface.Factories.Solvers.*;
import aprove.Probabilistic.Termination.ADPProblem.AST.Processors.AST_ADPReductionPairProcessor.*;
import aprove.ProofTree.Export.*;
import aprove.ProofTree.Export.Utility.*;
import aprove.ProofTree.Obligations.*;
import aprove.ProofTree.Proofs.Proof.DefaultProof;
import aprove.Strategies.Abortions.*;
import aprove.Strategies.Annotations.*;
import aprove.Strategies.ExecutableStrategies.*;
import aprove.Strategies.UserStrategies.*;

/**
 * Converts an IDPProblem to an IRSProblem.
 *
 * The IDPProblem must not contain any terms.
 * nested function calls will be replaced by fresh variables
 */
public class IDPToIRSProcessor extends IDPProcessor {
    // ================================================================================
    // Properties
    // ================================================================================

    private final static Logger log = Logger
            .getLogger("aprove.DPFramework.IDPProblem.Processors.IDPToIRSProcessor");

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    // ================================================================================
    // isApplicable
    // ================================================================================

    /**
     * Checks if this processor is applicable to the IDP.
     */
    @Override
    public boolean isIDPApplicable(final IDPProblem iDP) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter) throws AbortionException {
        final Set<IGeneralizedRule> rules = new LinkedHashSet<>();
        int i = 0;
        for (GeneralizedRule rule : iDP.getP()) {
            List<TRSTerm> args = new ArrayList<>();
            TRSTerm newRight = rule.getRight();
            TRSTerm constraint = null;
            if (rule.getRight() instanceof TRSFunctionApplication) {
                TRSFunctionApplication fun = (TRSFunctionApplication) rule.getRight();
                int j = 0;
                for (TRSTerm arg : fun.getArguments()) {
                    if (arg instanceof TRSFunctionApplication) {
                        TRSFunctionApplication innerFun = (TRSFunctionApplication) arg;
                         if (IDPPredefinedMap.DEFAULT_MAP.isArithmeticFunction(innerFun.getFunctionSymbol())) {
                             // TODO fresh variable
                             TRSVariable freshVar = TRSTerm.createVariable("new" + i + j);
                             args.add(freshVar);
                             List<TRSTerm> constraintArgs = new ArrayList<>();
                             constraintArgs.add(freshVar);
                             constraintArgs.add(innerFun);
                             constraint = TRSTerm.createFunctionApplication(FunctionSymbol.create("=", 2), constraintArgs);
                             if (IDPPredefinedMap.DEFAULT_MAP.isArithmeticFunction(((TRSFunctionApplication) constraint).getFunctionSymbol())) {
                                 
                             }
                         } else {
                             // fresh variable
                             args.add(TRSTerm.createVariable("new" + i + j));
                         }
                        
                        j++;
                    } else {
                        args.add(arg);
                    }
                }
                newRight = TRSTerm.createFunctionApplication(fun.getRootSymbol(), ImmutableCreator.create(args));
            }

//            List<TRSTerm> lArgs = new ArrayList<>();
//            for (TRSTerm arg : rule.getLeft().getArguments()) {
//                if (arg instanceof TRSConstantTerm) {
//                    lArgs.add(TRSTerm.createVariable(arg.getName()));
//                } else {
//                    lArgs.add(arg);
//                }
//            }
//            TRSFunctionApplication newLeft = TRSTerm.createFunctionApplication(rule.getLeft().getRootSymbol(), ImmutableCreator.create(lArgs));

            // condition is unset, conditions in IDP are moved to the rules itself
            final IGeneralizedRule iRule = IGeneralizedRule.create(rule.getLeft(), newRight, constraint);
            rules.add(iRule);
            i++;
        }
        final IRSProblem irs = new IRSProblem(ImmutableCreator.create(rules));

        final IDPToIRSProof proof = new IDPToIRSProof();

        return ResultFactory.proved(irs, YNMImplication.SOUND, proof);

    }

    private TrsTypes runTypeInference(final Set<GeneralizedRule> rules) {
        Set<FunctionSymbol> allSymbols = CollectionUtils.getFunctionSymbols(rules);
        Set<FunctionSymbol> definedSymbols = CollectionUtils.getRootSymbols(rules);

        // Predefined symbols don't occur as root symbols but are defined too
        for (final FunctionSymbol fun : allSymbols) {
            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(fun)) {
                definedSymbols.add(fun);
            }
        }

        // Convert the rules to the type expected for TypeInference
        Set<aprove.Complexity.LowerBounds.BasicStructures.Rule> newRules = new LinkedHashSet<>();
        for (final GeneralizedRule rule : rules) {
            newRules.add(new aprove.Complexity.LowerBounds.BasicStructures.Rule(rule.getLeft(), rule.getRight()));
        }

        return TypeInference.infer(newRules, allSymbols, definedSymbols);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public class IDPToIRSProof extends DefaultProof implements DOT_Able {

        /** Obligation node where substrategy has been applied. */

        public IDPToIRSProof() {
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("No proof yet :(");
            result.append(o.linebreak());
            return result.toString();
        }

        @Override
        public String toDOT() {
            return "";
            //            return this.idp.getIdpGraph().toDOT();
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================


}
