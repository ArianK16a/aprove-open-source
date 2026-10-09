package aprove.verification.dpframework.IDPProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.Processors.processorHistory.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Profiling.*;
import aprove.verification.oldframework.Utility.Profiling.FeaturesIDP.*;
import aprove.xml.*;
import immutables.*;

/**
 * Integer DP problem.
 *
 * @author mpluecke, noschinski
 * @version $Id$
 */
public final class IDPProblem extends DefaultBasicObligation implements
Immutable, HTML_Able, HasTRSTerms, ExternUsable, XMLObligationExportable,
        DOT_Able,
        VerbosityExportable,
        HasFeatureVector<FeaturesIDP.Features>
{

    /*
     * real values
     */

    /**
     * TRS with integer conditions.
     */
    private final ImmutableSet<GeneralizedRule> R;

    /*
     * cached/computed values
     */

    /**
     * Dependency Pairs
     */
    private final ImmutableSet<GeneralizedRule> P;

    /**
     * RuleAnalysis<GeneralizedRule>
     */
    private final IDPRuleAnalysis ruleAnalysis;

    /**
     * processor history
     */
    private final IdpProcessorHistory procHistory;


    /**
     * IDependencyGraph
     */
    private final IIDependencyGraph idpGraph;

    private final boolean minimal;

    private IDPProblem(final IIDependencyGraph idpGraph, final IDPRuleAnalysis ruleAnalysis, final boolean minimal, final IdpProcessorHistory procHistory) {
        super("IDP_v1", "Integer DP v1 Problem");
        this.R = ruleAnalysis.getRAnalysis().getRules();
        if (ruleAnalysis.getPAnalysis() != idpGraph.getNodeAnalysis()) {
            throw new IllegalArgumentException("idpGraph.getNodeAnalysis() must be the same as ruleAnalysis.getPAnalysis()");
        }
        this.P = ruleAnalysis.getPAnalysis().getRules();
        this.idpGraph = idpGraph;
        this.ruleAnalysis = ruleAnalysis;
        this.minimal = minimal;
        this.procHistory = procHistory;
    }

    public static IDPProblem create(final IIDependencyGraph idpGraph, final RuleAnalysis<GeneralizedRule> rAnalysis, final IQTermSet Q, final boolean minimal) {
        return IDPProblem.create(idpGraph, rAnalysis, Q, minimal, null);
    }

    public static IDPProblem create(final IIDependencyGraph idpGraph, final RuleAnalysis<GeneralizedRule> rAnalysis, final IQTermSet Q, final boolean minimal, final IDPProcessor sourceProc) {
        return new IDPProblem(idpGraph, new IDPRuleAnalysis(rAnalysis, idpGraph.getNodeAnalysis(), Q, null), minimal, IdpProcessorHistory.initialHistory(sourceProc));
    }

    @Deprecated
    public static IDPProblem create(final Set<GeneralizedRule> r, final Set<GeneralizedRule> p) {
        throw new UnsupportedOperationException();
    }

    public static IDPProblem create(final ITRSProblem rWithQ, final boolean minimal, final Abortion aborter) throws AbortionException {
        return IDPProblem.create(new RootConstrGraphProcessor(IItpfRule.ApplicationMode.Multistep), rWithQ, minimal, aborter);
    }

    public static IDPProblem create(final AbstractInitialGraphProcessor proc, final RuleAnalysis<GeneralizedRule> r, final IQTermSet Q, final boolean minimal, final Abortion aborter) throws AbortionException {
        final IDPRuleAnalysis analysis = new IDPRuleAnalysis(r, new RuleAnalysis<GeneralizedRule>(r.getDependencyPairs(), r.getPreDefinedMap()), Q, null);
        final IIDependencyGraph graph = proc.createInitialGraph(analysis, aborter);
        return new IDPProblem(graph, analysis.change(null, graph.getNodeAnalysis(), null), minimal, graph.getProcHistory());
    }

    public static IDPProblem create(final AbstractGraphProcessor proc, final ITRSProblem rWithQ, final boolean minimal, final Abortion aborter) throws AbortionException {
        return IDPProblem.create(new RootConstrGraphProcessor(IItpfRule.ApplicationMode.Multistep), rWithQ.getRuleAnalysis(), rWithQ.getQ(), minimal, aborter);
    }

    public static IDPProblem create(final IDPRuleAnalysis rules, final boolean minimal, final Abortion aborter) throws AbortionException {
        return IDPProblem.create(new RootConstrGraphProcessor(IItpfRule.ApplicationMode.Multistep), rules, minimal, aborter);
    }

    public static IDPProblem create(final AbstractInitialGraphProcessor proc, final IDPRuleAnalysis rules, final boolean minimal, final Abortion aborter) throws AbortionException {
        final IIDependencyGraph graph = proc.createInitialGraph(rules, aborter);
        return new IDPProblem(graph, rules.change(null, graph.getNodeAnalysis(), null), minimal, graph.getProcHistory());
    }

    public ImmutableSet<GeneralizedRule> getR() {
        return this.R;
    }

    public ImmutableSet<GeneralizedRule> getP() {
        return this.P;
    }

    public IQTermSet getQ() {
        return this.ruleAnalysis.getQ();
    }

    public IDPRuleAnalysis getRuleAnalysis() {
        return this.ruleAnalysis;
    }

    @Override
    public Set<? extends TRSTerm> getTerms() {
        return this.ruleAnalysis.getRAnalysis().getTerms();
    }

    public IIDependencyGraph getIdpGraph() {
        return this.idpGraph;
    }

    public boolean isMinimal() {
        return this.minimal;
    }

    public IdpProcessorHistory getProcHistory() {
        return this.procHistory;
    }

    public IDPProblem change(final IIDependencyGraph idpGraph, final RuleAnalysis<GeneralizedRule> rAnalysis, final IQTermSet Q, final Boolean minimal, final IDPProcessor proc) {
        final IIDependencyGraph graph = idpGraph != null ? idpGraph : this.idpGraph;
        final IDPRuleAnalysis analysis = this.ruleAnalysis.change(rAnalysis, graph.getNodeAnalysis(), Q);
        return new IDPProblem(graph, analysis, minimal != null ? minimal : this.minimal, IdpProcessorHistory.newEntry(this.procHistory, proc));
    }

    /**
     * returns a new QDP-Problem where s_to_t is transformed by nri to a set of new
     * DPs. Moreover, the counter for the new DPs and the given transformation is returned.
     * @param s_to_t
     * @param newDPs
     * @param p the position of the transformation in t.
     * @return
     */
    /*
    public Pair<IDPProblem, Integer> getTransformedProblem(IDPTransformation transformation, GeneralizedRule s_to_t, Set<GeneralizedRule> newDPs, Position p, IDPProcessor proc) {
        Pair<IIDependencyGraph, Integer> graphCounter = this.idpGraph.getTransformedGraph(transformation, s_to_t, newDPs, p, proc);
        return new Pair<IDPProblem, Integer>(
                change(graphCounter.x, null, null, null, proc),
                graphCounter.y);
    }*/

    @Override
    public String export(final Export_Util o) {
        return this.export(o, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(final Export_Util o, final VerbosityLevel verbosityLevel) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("IDP_v1 problem:"));
        s.append(o.cond_linebreak());
        if (this.getR().isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The ITRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(IDPExport.exportRule(this.R, o, this.ruleAnalysis.getPreDefinedMap()));
            s.append(o.cond_linebreak());
        }
        s.append(o.cond_linebreak());
        if (this.idpGraph.getNodes().isEmpty()) {
            s.append("The integer pair graph is empty.");
            s.append(o.cond_linebreak());
            s.append(o.cond_linebreak());
        } else {
            s.append(o.export("The integer pair graph contains the following rules and edges:"));
            s.append(o.cond_linebreak());
            s.append(this.idpGraph.export(o, this.ruleAnalysis.getPreDefinedMap(), verbosityLevel));
        }

        if (this.ruleAnalysis.getQ().isEmpty()) {
            s.append("The set Q is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The set Q consists of the following terms:"));
            s.append(o.cond_linebreak());
            s.append(IDPExport.exportTerm(this.ruleAnalysis.getQ().getWrappedQ().getTerms(), o, this.ruleAnalysis.getPreDefinedMap()));
            s.append(o.cond_linebreak());
        }

        return s.toString();
    }

    @Override
    public String externName() {
        return "idp";
    }

    @Override
    public String toExternString() {
        return SaveProblemHelper.toAProVE_IDP(this.R, this.P, this.ruleAnalysis.getPreDefinedMap());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Finiteness");
    }

    @Override
    public String toDOT() {
        return this.idpGraph.toDOT();
    }

    @Override
    public FeatureVector<Features> getFeatureVector() {
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "idpv1";
    }
}
