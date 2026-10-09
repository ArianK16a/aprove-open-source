package aprove.verification.oldframework.Bytecode.Processors.ToIntTRS;

import java.io.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Processors.*;
import aprove.verification.oldframework.Bytecode.Processors.PathLength.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.TerminationSCCToIDPv2Processor.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IRSwT.IRSwTFormatTransformer.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.Compression.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This processor takes a TerminationGraph SCC and translates it to an intTRS
 * problem by converting each edge of the SCC to an integer rewrite rule and
 * simplifying these.
 *
 * @author Christian von Essen, Matthias Hoelzel, Marc Brockschmidt
 */
public class TerminationSCCToIRSProcessor extends Processor.ProcessorSkeleton {
    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    public static class Arguments extends ConverterArguments {
        /**
         * A path to which intTRSs are dumped. If null, no dumping is performed.
         */
        public String dumpIntTRSPath;

        /**
         * Should we do the path length transformation on the resulting system?
         */
        public boolean applyPathLength = false;

        /**
         * Switches on a direct QDP export (if there are no predefined
         * symbols). This doesn't really make sense without cleanRules = true.
         */
        public boolean tryQDPExport = true;

        /**
         * Switches on rule compression. SHOULD ALWAYS BE ON.
         */
        public boolean compressRules = true;

        /**
         * Switches on unneeded argument filter. SHOULD ALWAYS BE ON.
         */
        public boolean filterUnneededArguments = true;

        /**
         * Switches on duplicate argument filter. SHOULD ALWAYS BE ON.
         */
        public boolean filterDuplicateArguments = true;

        /**
         * Duplicate integer argument nested in function symbols to the top level before doing anything.
         */
        public boolean duplicateNestedIntegerArguments = true;
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me)
     */
    public class TerminationSCCToIRSProof extends DefaultProof {
        /**
         * Some documentation about the magic we've done.
         */
        private final List<Pair<String, ? extends RuleSet>> log;

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         */
        public TerminationSCCToIRSProof(final List<Pair<String, ? extends RuleSet>> l) {
            super();
            this.log = l;
            this.shortName = "SCCToIRSProof";
            this.longName = "TerminationSCCToIRSProof";
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Transformed FIGraph SCCs to intTRSs. Log: ");
            sb.append(o.linebreak());
            for (final Pair<String, ? extends RuleSet> entry : this.log) {
                sb.append(o.indent(entry.x));
                if (entry.y != null) {
                    sb.append(o.indent(entry.y.export(o)));
                } else {
                    sb.append(o.linebreak());
                }
            }
            return sb.toString();
        }
    }

    /**
     * Parameters for this processor.
     */
    private final Arguments arguments;

    /**
     * Create a fresh processor to transform a FIGraph into an ITRS
     * @param args object holding parameters for this processor
     */
    @ParamsViaArgumentObject
    public TerminationSCCToIRSProcessor(final Arguments args) {
        this.arguments = args;
    }

    /**
     * Converts an IDPv1 ITRS into an intTRS.
     * @param rules The ITRS.
     * @param predefinedMap The map of predefined function symbols.
     * @param conversionLog For logging.
     * @param doPathLength turns on path length conversion
     * @param removeEOSinFirstArg Removes the first argument starting with EOS introduced by the static field encoding in the JBC backend
     * @param duplicateFilterAfterPL Apply the duplicate arg filter again after doing the path length thing
     * @param duplicateNestedIntegerArguments Duplicate integer argument nested in function symbols to the top level before doing anything
     * @param aborter For abortions.
     * @return The intTRS.
     * @throws AbortionException If it is aborted.
     */
    public static IRSwTProblem convertToIntTRSProblem(
        final Set<IGeneralizedRule> rules,
        final IDPPredefinedMap predefinedMap,
        final List<Pair<String, ? extends RuleSet>> conversionLog,
        final boolean doPathLength,
        final boolean removeEOSinFirstArg,
        final boolean duplicateFilterAfterPL,
        final boolean duplicateNestedIntegerArguments,
        final Abortion aborter) throws AbortionException
    {
        Set<IGeneralizedRule> iGRules = rules;

        if (duplicateNestedIntegerArguments) {
            iGRules = TerminationSCCToIRSProcessor.copyIntVarsToTopPos(rules, predefinedMap);
        }

        if (doPathLength) {
            conversionLog.add(new Pair<String, RuleSet>("Prepared "
                + iGRules.size()
                + " rules for path length conversion:", new IGeneralizedRuleSet(iGRules, null)));
            iGRules = PathLength.translateIGRuleSet(iGRules, predefinedMap);

            iGRules = PathLength.translateIGRuleSet(iGRules, predefinedMap);
            if (duplicateFilterAfterPL) {
                final Pair<Pair<Set<IGeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>, CollectionMap<FunctionSymbol, Integer>> resultPair =
                    IntTRSDuplicateArgumentFilterProcessor.processRules(iGRules);
                if (resultPair != null) {
                    iGRules = resultPair.x.x;
                }
            }
        }

        final LinkedHashSet<IGeneralizedRule> newRules = new LinkedHashSet<>();

        for (final IGeneralizedRule rule : iGRules) {
            final IGeneralizedRule newRule = IRSwTFormatTransformer.moveArithmeticToConstrains(rule, predefinedMap);
            //Remove ! (does not exist anyway, done) and != and the ensuing ||:
            final Set<IGeneralizedRule> tmp =
                IRSwTFormatTransformer.removeDivModAndNotAndNotEqualAndOrAndFalse(newRule, RoundingBehaviour.UNKNOWN, predefinedMap, false, true);
            newRules.addAll(tmp);
        }
        iGRules = newRules;

        iGRules = TerminationSCCToIDPv1Processor.cleanConstraints(iGRules, false, true, predefinedMap, aborter);
        iGRules = TerminationSCCToIDPv1Processor.removeTrivialConstraints(iGRules, predefinedMap);
        iGRules = TerminationSCCToIDPv1Processor.removePredefinedOpsOnLhs(iGRules, predefinedMap);
        if (removeEOSinFirstArg) {
            iGRules = TerminationSCCToIRSProcessor.removeEOS(iGRules);
        }

        conversionLog.add(new Pair<String, RuleSet>(
            "Finished conversion. Obtained " + iGRules.size() + " rules.",
            new IGeneralizedRuleSet(iGRules, null)));

        if (doPathLength) {
            iGRules = IRSwTFormatTransformer.makeLhsLinear(iGRules, predefinedMap);
            return new IRSProblem(ImmutableCreator.create(iGRules));
        } else {
            return new IRSwTProblem(ImmutableCreator.create(iGRules));
        }
    }

    /**
     * @param rules some rules
     * @return a new set of rules in which no lhs or rhs has an EOS thingy as first Argument
     */
    private static Set<IGeneralizedRule> removeEOS(final Set<IGeneralizedRule> rules) {
        final LinkedHashSet<IGeneralizedRule> newRules = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : rules) {
            final TRSTerm newLhs = TerminationSCCToIRSProcessor.removeEOS(rule.getLeft());
            final TRSTerm newRhs = TerminationSCCToIRSProcessor.removeEOS(rule.getRight());
            newRules.add(IGeneralizedRule.create((TRSFunctionApplication) newLhs, newRhs, rule.getCondTerm()));
        }
        return newRules;
    }

    /**
     * @param t some term
     * @return a term that has no EOS thingy as first argument.
     */
    private static TRSTerm removeEOS(final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
            final FunctionSymbol fs = fa.getRootSymbol();
            final ImmutableList<TRSTerm> args = fa.getArguments();
            if (args.size() > 0) {
                final TRSTerm firstArg = args.get(0);
                if (firstArg instanceof TRSFunctionApplication
                    && "EOS".equals(((TRSFunctionApplication) firstArg).getRootSymbol().getName()))
                {
                    final FunctionSymbol newFs = FunctionSymbol.create(fs.getName(), fs.getArity() - 1);
                    final ArrayList<TRSTerm> newArgs = new ArrayList<>(args.subList(1, args.size()));
                    return TRSTerm.createFunctionApplication(newFs, newArgs);
                }
            }
        }
        return t;
    }

    /**
     * @param fA some function application
     * @param alwaysIntegerPositions a collection map giving a set of positions
     *  at which we only observed integers until now.
     * @return an extended version of <code>fA</code> where all proper
     *  subterms at positions which only contain integers are copied to
     *  a top-level position.
     */
    private static TRSFunctionApplication copyIntVarsToTopPos(
        final TRSFunctionApplication fA,
        final CollectionMap<FunctionSymbol, Position> alwaysIntegerPositions
    ) {
        final ImmutableList<TRSTerm> oldArgs = fA.getArguments();
        final FunctionSymbol defSym = fA.getRootSymbol();
        final List<TRSTerm> copiedArgs = new LinkedList<>();
        for (final Position copyPos : alwaysIntegerPositions.get(defSym)) {
            if (copyPos.getDepth() <= 1) {
                continue;
            }
            copiedArgs.add(fA.getSubterm(copyPos));
        }
        final ArrayList<TRSTerm> newArgs = new ArrayList<>(oldArgs.size() + copiedArgs.size());
        newArgs.addAll(oldArgs);
        newArgs.addAll(copiedArgs);
        final FunctionSymbol newDefSym = FunctionSymbol.create(defSym.getName(), newArgs.size());
        return TRSTerm.createFunctionApplication(newDefSym, newArgs);
    }

    /**
     * @param rules a set of rules
     * @param predefinedMap the predefined map
     * @return a set of rules in which integer positions hidden deep in other terms are copied as additional arguments
     * of the enclosing defined symbol
     */
    public static Set<IGeneralizedRule> copyIntVarsToTopPos(
        final Set<IGeneralizedRule> rules,
        final IDPPredefinedMap predefinedMap)
    {
        /*
         * (1) compute alwaysIntegerPositions:
         *  (a) start with all positions below a term with defined symbol
         *  (b) remove all positions which either don't exist for some
         *      occurrence of the defined symbol or have no integer on it.
         *  (c) compute fix point, through the system, i.e.,
         *       remove every position on lhs where some var is bound that
         *       also appears on a position that is not guaranteed to be
         *       always an int on the rhs.
         * (2) Extend defined symbols to copy all alwaysIntegerPositions to some
         *     position below root
         */
        final CollectionMap<FunctionSymbol, Position> alwaysIntegerPositions = new CollectionMap<>();
        for (final IGeneralizedRule rule : rules) {
            alwaysIntegerPositions.put(rule.getLeft().getRootSymbol(), rule.getLeft().getPositions());
        }

        //We have special rules here, where no user-def. symbol appears below epsilon
        for (final IGeneralizedRule rule : rules) {
            TerminationSCCToIRSProcessor.removeNonExistingAndNonPredefinedPositions(
                alwaysIntegerPositions,
                rule.getLeft(),
                predefinedMap);
            TerminationSCCToIRSProcessor.removeNonExistingAndNonPredefinedPositions(
                alwaysIntegerPositions,
                (TRSFunctionApplication) rule.getRight(),
                predefinedMap);
        }

        boolean changed;
        do {
            changed = false;
            for (final IGeneralizedRule rule : rules) {
                final Set<TRSVariable> integerVarsOnRhs =
                    TerminationSCCToIRSProcessor.getAlwaysIntegerVars(
                        (TRSFunctionApplication) rule.getRight(),
                        alwaysIntegerPositions);
                for (final Pair<Position, TRSTerm> p : rule.getLeft().getPositionsWithSubTerms()) {
                    final Position pos = p.getKey();
                    final TRSTerm subterm = p.getValue();
                    if (alwaysIntegerPositions.containsKey(pos)) {
                        if (!integerVarsOnRhs.containsAll(subterm.getVariables())) {
                            alwaysIntegerPositions.remove(pos);
                            changed = true;
                        }
                    }
                }
            }

        } while (changed);

        //Now copy the arguments out:
        final Set<IGeneralizedRule> newRules = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : rules) {
            newRules.add(IGeneralizedRule.create(TerminationSCCToIRSProcessor.copyIntVarsToTopPos(
                rule.getLeft(),
                alwaysIntegerPositions), TerminationSCCToIRSProcessor.copyIntVarsToTopPos(
                (TRSFunctionApplication) rule.getRight(),
                alwaysIntegerPositions), rule.getCondTerm()));
        }

        return newRules;
    }

    /**
     * @param dumpIntTRSPath path to which the intTRS is dumped
     * @param suffix additional String used in the file name for the exported intTRS
     * @param rti runtime information of the machine, used to generate a file name
     * @param rules the actual rules
     * @param aborter tells us when to abort
     * @throws AbortionException can be aborted
     */
    private static void dumpIntTRS(
        final String dumpIntTRSPath,
        final String suffix,
        final RuntimeInformation rti,
        final Abortion aborter,
        final Set<IGeneralizedRule> rules) throws AbortionException
    {

        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = inputPath.getName();

        FileWriter fw = null;
        try {
            final File path =
                new File(dumpIntTRSPath + System.getProperty("file.separator") + problemName + "-" + suffix + ".inttrs");
            final boolean created = path.getParentFile().mkdirs();
            assert (created);
            fw = new FileWriter(path);
            IRSwTProblem.exportRules(rules, aborter, fw);
        } catch (final IOException e) {
            return;
        } finally {
            if (fw != null) {
                try {
                    fw.close();
                } catch (final IOException e) {
                    return;
                }
            }
        }
    }

    /**
     * @param fA some function application
     * @param alwaysIntegerPositions a collection map giving a set of positions
     *  at which we only observed integers until now.
     * @return a set of variables which occur at positions which supposedly
     *  only contain integers.
     */
    private static Set<TRSVariable> getAlwaysIntegerVars(
        final TRSFunctionApplication fA,
        final CollectionMap<FunctionSymbol, Position> alwaysIntegerPositions)
    {
        final Set<TRSVariable> res = new LinkedHashSet<>();
        for (final Pair<Position, TRSTerm> p : fA.getPositionsWithSubTerms()) {
            final Position pos = p.getKey();
            final TRSTerm subterm = p.getValue();
            if (alwaysIntegerPositions.containsKey(pos)) {
                res.addAll(subterm.getVariables());
            }
        }
        return res;
    }

    /**
     * @param alwaysIntegerPositions a collection map giving a set of positions
     *  at which we only observed integers until now.
     * @param fA some function application
     * @param predefinedMap the predefined map
     */
    private static void removeNonExistingAndNonPredefinedPositions(
        final CollectionMap<FunctionSymbol, Position> alwaysIntegerPositions,
        final TRSFunctionApplication fA,
        final IDPPredefinedMap predefinedMap)
    {
        final FunctionSymbol defSym = fA.getRootSymbol();
        final Set<Position> posInFa = new LinkedHashSet<>();
        for (final Pair<Position, TRSTerm> p : fA.getPositionsWithSubTerms()) {
            final Position pos = p.getKey();
            posInFa.add(pos);
            final TRSTerm subterm = p.getValue();
            if (subterm instanceof TRSFunctionApplication
                && !predefinedMap.isPredefined(((TRSFunctionApplication) subterm).getRootSymbol()))
            {
                alwaysIntegerPositions.remove(defSym, pos);
            }
        }

        /*
         * curPos is a ref to the inner structure of the collection map, we do
         * not need to write the changed set back.
         */
        final Collection<Position> curPos = alwaysIntegerPositions.getNotNullAndAdd(defSym);
        curPos.retainAll(posInFa);
    }

    /**
     * @return true for a JBCTerminationSCCProblem.
     * @param obl some obligation that should be a JBCTerminationSCCProblem
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof JBCTerminationSCCProblem;
    }

    /**
     * Work on the given obligation.
     * @param obl an FI Graph
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @throws AbortionException as soon as the aborter kicks in.
     * @return one ITRS
     */
    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        if (!(obl instanceof JBCTerminationSCCProblem)) {
            assert (false);
            return ResultFactory.unsuccessful();
        }
        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        final List<Pair<String, ? extends RuleSet>> conversionLog = new LinkedList<>();

        // Get rule sets from the graph and turn them into problems.
        final JBCTerminationSCCProblem terminationSCCProblem = (JBCTerminationSCCProblem) obl;

        // Edges from the SCC shall be converted into rules in P. We can
        // ignore R here.
        final Collection<Edge> pEdges = terminationSCCProblem.getSCC().getEdges();

        //Initialize the rule creator and transformation dispatcher:
        final PolyFactory polyFactory = new SharingPolyFactory();
        final ItpfFactory itpfFactory = new SharingItpfFactory(polyFactory);
        final SCCAnnotations sccAnnotations = terminationSCCProblem.getSCCAnnotations();
        final TransformationDispatcher dispatcher = new TransformationDispatcher(sccAnnotations, this.arguments);
        final RuleCreator ruleCreator =
            new RuleCreator(
                terminationSCCProblem.getFullGraph(),
                this.arguments,
                dispatcher,
                sccAnnotations,
                itpfFactory,
                aborter);

        Set<IGeneralizedRule> iGRules =
            IDPv2ToIDPv1Utilities.convertEdgesToIDPv1(
                aborter,
                ruleCreator,
                false,
                sccAnnotations,
                dispatcher,
                pEdges,
                false);

        conversionLog.add(new Pair<String, RuleSet>(
            "Generated rules. Obtained " + iGRules.size() + " IRules",
            new IGeneralizedRuleSet(iGRules, null)));

        if (this.arguments.compressRules) {
            RuleCombiner combiner = new RuleCombiner(iGRules, Collections.emptySet(), aborter);
            iGRules = combiner.combineRules(false, true).y;

            conversionLog.add(new Pair<String, RuleSet>(
                "Combined rules. Obtained " + iGRules.size() + " IRules",
                new IGeneralizedRuleSet(iGRules, null)));
        }

        //Some pseudo-DP-Graph magic:
        final Set<FunctionSymbol> definedSymbols = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : iGRules) {
            definedSymbols.add(rule.getRootSymbol());
        }
        final Set<IGeneralizedRule> rulesToRemove = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : iGRules) {
            final TRSTerm rhs = rule.getRight();
            if (rhs instanceof TRSVariable) {
                rulesToRemove.add(rule);
            } else if (!definedSymbols.contains(((TRSFunctionApplication) rhs).getRootSymbol())) {
                rulesToRemove.add(rule);
            }
        }
        if (!rulesToRemove.isEmpty()) {
            iGRules.removeAll(rulesToRemove);
            conversionLog.add(new Pair<>("Removed following non-SCC rules:\n", new IGeneralizedRuleSet(
                rulesToRemove,
                Collections.<IGeneralizedRule>emptySet(),
                false)));
        }

        // Transform constraints
        Pair<Pair<Set<IGeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>, CollectionMap<FunctionSymbol, Integer>> resultPair =
            null;
        resultPair = IntTRSConstantGroundArgumentFilterProcessor.processRules(iGRules);
        if (resultPair != null) {
            iGRules = resultPair.x.x;
            conversionLog.add(new Pair<>("Filtered constant ground arguments:", new RuleSet(ArgumentsRemovalProof
                .getFilterRules(resultPair.y, resultPair.x.y))));
        }

        if (this.arguments.filterDuplicateArguments) {
            resultPair = IntTRSDuplicateArgumentFilterProcessor.processRules(iGRules);
            if (resultPair != null) {
                iGRules = resultPair.x.x;
                conversionLog.add(new Pair<>("Filtered duplicate arguments:", new RuleSet(ArgumentsRemovalProof
                    .getFilterRules(resultPair.y, resultPair.x.y))));
            }
        }

        if (this.arguments.filterUnneededArguments) {
            resultPair = IntTRSUnneededArgumentFilterProcessor.processRules(iGRules, true, null);
            if (resultPair != null) {
                iGRules = resultPair.x.x;
                conversionLog.add(new Pair<>("Filtered unneeded arguments:", new RuleSet(ArgumentsRemovalProof
                    .getFilterRules(resultPair.y, resultPair.x.y))));
            }
        }

        //Direct export to QDP if we don't have no predefined symbols:
        OUTER: if (this.arguments.tryQDPExport) {
            try {
                final Set<GeneralizedRule> gRules = IGeneralizedRule.removeConditions(iGRules);
                final RuleAnalysis<GeneralizedRule> ruleAnalysis =
                    new RuleAnalysis<>(ImmutableCreator.create(gRules), predefinedMap);

                if (!ruleAnalysis.hasPredefinedDefSymbols()) {
                    //The result system may be in QDP shape. So what we do now is to call the IDP export, letting it do its QDP bit, trying to get a QDP with nested stuff:
                    final Pair<? extends BasicObligation, List<Pair<String, ? extends RuleSet>>> p =
                        TerminationSCCToIDPv1Processor.toObligation(
                            obl,
                            aborter,
                            rti,
                            new TerminationSCCToIDPv1Processor.Arguments());
                    if (p.x instanceof QDPProblem) {
                        return ResultFactory.proved(p.x, YNMImplication.SOUND, new TerminationSCCToQDPProof(p.y));
                    }

                    final QTermSet qSet = new QTermSet(Collections.<TRSFunctionApplication>emptySet());

                    final Set<Rule> pRules = new LinkedHashSet<>();
                    for (final GeneralizedRule r : gRules) {
                        if (Rule.checkProperLandR(r.getLeft(), r.getRight())) {
                            pRules.add(Rule.create(r.getLeft(), r.getRight()));
                        } else {
                            // we have a free variable, this cannot be handled in QDP
                            break OUTER;
                        }
                    }

                    final QDPProblem qdp =
                        QDPProblem.create(
                            pRules,
                            QTRSProblem.create(ImmutableCreator.create(Collections.<Rule>emptySet()), qSet),
                            true);

                    return ResultFactory.proved(qdp, YNMImplication.SOUND, new TerminationSCCToQDPProof(conversionLog));
                }
            } catch (final AssertionError err) {
                //This was a free var. Ignore.
            }
        }

        IRSwTProblem newObl =
            TerminationSCCToIRSProcessor.convertToIntTRSProblem(iGRules, predefinedMap, conversionLog,
                this.arguments.applyPathLength, this.arguments.encodeStaticFields,
                this.arguments.filterDuplicateArguments, this.arguments.duplicateNestedIntegerArguments,
                aborter);
        if (this.arguments.dumpIntTRSPath != null) {
            TerminationSCCToIRSProcessor.dumpIntTRS(
                this.arguments.dumpIntTRSPath,
                obl.getId() + "-simplified",
                rti,
                aborter,
                newObl.getRules());
        }

        final Node startNode = terminationSCCProblem.getStartNode();
        TRSFunctionApplication startTerm = null;
        if (startNode != null) {
            //We need this loop because there is no good way to guess the arity of the damn thing...
            final String nameOfStartSym =
                RuleCreator.getNameOfStateFunctionSymbol(startNode.getNodeNumber() + "", 0,
                    startNode.getState().getCurrentOpCode());
            FunctionSymbol startSymbol = null;
            for (final IGeneralizedRule rule : newObl.getRules()) {
                if (rule.getRootSymbol().getName().equals(nameOfStartSym)) {
                    startSymbol = rule.getRootSymbol();
                }
            }
            if (startSymbol != null) {
                final int arity = startSymbol.getArity();
                final ArrayList<TRSTerm> args = new ArrayList<>(arity);
                for (int i = 1; i <= arity; i++) {
                    args.add(TRSTerm.createVariable("x" + i));
                }
                startTerm = TRSTerm.createFunctionApplication(startSymbol, args);
                newObl = new IRSwTProblem(newObl.getRules(), startTerm);
            }
        }

        return ResultFactory.proved(newObl, YNMImplication.SOUND, new TerminationSCCToIRSProof(conversionLog));
    }
}
