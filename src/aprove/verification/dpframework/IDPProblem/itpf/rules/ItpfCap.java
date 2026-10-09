/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf.rules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class ItpfCap extends IItpfRule.ItpfRuleSkeleton implements IInitialItpfRule, ISoundItpfRule, ICompleteItpfRule {

    public static final Integer SUB_TYPE = Integer.valueOf(0);

    private ExportableString longDescription;
    private IECap cap;

    public ItpfCap(IECap cap) {
        this.longDescription = new ExportableString("ItpfICap [" + cap.getDescription() + "]");
        this.cap = cap;
    }

    @Override
    public Exportable getDescription(NameLength length) {
        return this.longDescription;
    }

    @Override
    public boolean isApplicable(IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isApplicable(IDPProblem idp, Itpf formula, ApplicationMode mode) {
        return mode == ApplicationMode.Multistep || mode == ApplicationMode.SingleStep || formula.isItp();
    }

    @Override
    public Itpf process(IDPProblem idp, Itpf formula, ApplicationMode mode, Abortion aborter) throws AbortionException {
        CapVisitor visitor = new CapVisitor(idp.getRuleAnalysis(), this.cap, mode);
        return visitor.applyTo(formula.normalize());
    }

    @Override
    public Itpf processInitial(IDPRuleAnalysis ruleAnalysis, Itpf formula,
            Abortion aborter) throws AbortionException {
        CapVisitor visitor = new CapVisitor(ruleAnalysis, this.cap, ApplicationMode.Multistep);
        return visitor.applyTo(formula.normalize());
    }

    protected static class CapVisitor extends IItpfVisitor.ItpfVisitorSkeleton<Set<IECap>> {

        private final IECap cap;
        private final IDPRuleAnalysis ruleAnalysis;

        public CapVisitor(IDPRuleAnalysis ruleAnalysis, IECap cap, ApplicationMode mode) {
            super(ItpfMark.ItpfCap, mode);
            this.cap = cap;
            this.ruleAnalysis = ruleAnalysis;
        }

        @Override
        public Itpf caseItp(final ItpfItp tp) {
            IECap.CapFreshNameGenerator freshNames = new IECap.CapFreshNameGenerator(tp.getFreeVariables());
            TRSTerm l = tp.getL();
            TRSTerm r = tp.getR();
            ItpRelation rel = tp.getRelation();
            if (rel == ItpRelation.TO || rel == ItpRelation.TO_TRANS || rel == ItpRelation.TO_PLUS) {
                Pair <TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> cappedL = this.cap.cap(this.ruleAnalysis, tp.getS(), l, freshNames, false, false);
                if (rel == ItpRelation.TO) {
                    // check if one rewrite step can suffice
                    Position diffPos = null;
                    Stack<Position> stackP = new Stack<Position>();
                    Stack<TRSTerm> stackL = new Stack<TRSTerm>();
                    Stack<TRSTerm> stackR = new Stack<TRSTerm>();
                    stackP.push(Position.create());
                    stackL.push(l);
                    stackR.push(r);
                    while(!stackL.isEmpty()) {
                        Position p = stackP.pop();
                        TRSTerm cL = stackL.pop();
                        TRSTerm cR = stackR.pop();
                        if (!cL.isVariable() && !cR.isVariable()) {
                            TRSFunctionApplication fL = (TRSFunctionApplication)cL;
                            TRSFunctionApplication fR = (TRSFunctionApplication)cR;
                            if (fL.getRootSymbol().equals(fR.getRootSymbol())) {
                                stackL.addAll(fL.getArguments());
                                stackR.addAll(fR.getArguments());
                                int s = fL.getArguments().size();
                                for (int i = 0; i < s; i++) {
                                    stackP.push(p.append(i));
                                }
                            } else {
                                if (diffPos == null) {
                                    diffPos = p;
                                } else {
                                    diffPos = diffPos.getLongestCommonPrefix(p);
                                }
                            }
                        }
                    }
                    // we got one ore more differences, can we rewrite?
                    if (diffPos != null) {
                        boolean rewriteable = true;
                        for (Map.Entry<Position, ImmutableSet<GeneralizedRule>> e : cappedL.y.entrySet()) {
                            if (!e.getKey().isPrefixOf(diffPos)) {
                                rewriteable = false;
                                break;
                            }
                        }
                        if (!rewriteable) {
                            // we need at least 2 rewrite steps, so clause is not solveable!
                            this.applicationCount ++;
                            return Itpf.FALSE;
                        }
                    }
                }
                TRSSubstitution sigma = cappedL.x.getMGU(r);
                if (sigma == null) {
                    this.applicationCount ++;
                    return Itpf.FALSE;
                } else {
                    /*
                    // optimize orientation of substitution
                    Map<Variable, Term> newSubst = new HashMap<Variable, Term>();
                    Set<Variable> orgVars = l.getVariables();
                    orgVars.addAll(r.getVariables());
                    for (Map.Entry<Variable, ? extends Term> e : sigma.getMap().entrySet()) {
                        if (e.getValue().isVariable() && orgVars.contains(e.getKey()) && ! orgVars.contains(e.getValue())) {
                            newSubst.put((Variable)e.getValue(), e.getKey());
                        } else {
                            newSubst.put(e.getKey(), e.getValue());
                        }
                    }
                    sigma = Substitution.create(ImmutableCreator.create(newSubst), true);
                    Term lSigma = l.applySubstitution(sigma);
                    Term rSigma = r.applySubstitution(sigma);
                    */
                    Set<Itpf> newTermPairs = new LinkedHashSet<Itpf>();
                    TRSTerm lSigma = l;
                    TRSTerm rSigma = r;
                    Set<Position> rewritePositions = new LinkedHashSet<Position>();
                    for (Position capPos : cappedL.y.keySet()) {
                        rewritePositions.add(r.getLongestPrefixInTerm(capPos));
                    }
                    this.addTermPairs(tp, lSigma, rSigma, rewritePositions, newTermPairs);
                    if (newTermPairs.isEmpty()) {
                        return this.mark(tp, tp);
                    } else {
                        // newTermPairs.add(tp);
                        this.applicationCount ++;
                        return this.mark(tp, ItpfAnd.create(ImmutableCreator.create(newTermPairs)));
                    }
                }
            } else if (rel == ItpRelation.TO_SYM_TRANS) {
                // TODO: check if caching is legal
                Pair <TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> cappedL = this.cap.cap(this.ruleAnalysis, tp.getS(), l, freshNames, false, false);
                Pair <TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> cappedR = this.cap.cap(this.ruleAnalysis, tp.getS(), r, freshNames, false, false);
                if (cappedL.x.isVariable() || cappedR.x.isVariable()) {
                    return this.mark(tp, tp);
                } else {
                    // Substitution sigma = cappedL.x.getMGU(cappedR.x);
                    if (!cappedL.x.unifies(cappedR.x)) {
                        this.applicationCount ++;
                        return Itpf.FALSE;
                    } else {
                        Iterator<Map.Entry<Position, ImmutableSet<GeneralizedRule>>> iL = cappedL.y.entrySet().iterator();
                        while(iL.hasNext()) {
                            Map.Entry<Position, ImmutableSet<GeneralizedRule>> eL = iL.next();
                            Position pL = eL.getKey();
                            Iterator<Map.Entry<Position, ImmutableSet<GeneralizedRule>>> iR = cappedR.y.entrySet().iterator();
                            while(iR.hasNext()) {
                                Map.Entry<Position, ImmutableSet<GeneralizedRule>> eR = iR.next();
                                Position pR = eR.getKey();
                                if (pR.isPrefixOf(pL)) {
                                    iL.remove();
                                    break;
                                } else if (pL.isPrefixOf(pR)) {
                                    iR.remove();
                                }
                            }
                        }
                        // optimize orientation of substitution
                        /*
                        Map<Variable, Term> newSubst = new HashMap<Variable, Term>();
                        Set<Variable> orgVars = l.getVariables();
                        orgVars.addAll(r.getVariables());
                        for (Map.Entry<Variable, ? extends Term> e : sigma.getMap().entrySet()) {
                            if (e.getValue().isVariable() && orgVars.contains(e.getKey()) && ! orgVars.contains(e.getValue())) {
                                newSubst.put((Variable)e.getValue(), e.getKey());
                            } else {
                                newSubst.put(e.getKey(), e.getValue());
                            }
                        }
                        sigma = Substitution.create(ImmutableCreator.create(newSubst), true);
                        Term lSigma = l.applySubstitution(sigma);
                        Term rSigma = r.applySubstitution(sigma);
                        */

                        Set<Itpf> newTermPairs = new LinkedHashSet<Itpf>();
                        TRSTerm lSigma = l;
                        TRSTerm rSigma = r;
                        this.addTermPairs(tp, lSigma, rSigma, cappedL.y.keySet(), newTermPairs);
                        this.addTermPairs(tp, lSigma, rSigma, cappedR.y.keySet(), newTermPairs);
                        if (newTermPairs.isEmpty()) {
                            return this.mark(tp, tp);
                        } else {
                            newTermPairs.add(tp);
                            this.applicationCount ++;
                            return this.mark(tp, ItpfAnd.create(ImmutableCreator.create(newTermPairs)));
                        }
                    }
                }
            } else {
                return this.mark(tp, tp);
            }
        }

        protected void addTermPairs(final ItpfItp tp, final TRSTerm l, final TRSTerm r, Set<Position> positions, Set<Itpf> addTo) {
            ItpRelation rel = tp.getRelation();
            for (Position p : positions) {
                if (p.isEmptyPosition()) {
                    continue;
                }
                ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextL = null;
                ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextR = null;
                if (tp.getKLeft() != null) {
                    ArrayList<ImmutablePair<FunctionSymbol, Integer>> tmp =  new ArrayList<ImmutablePair<FunctionSymbol, Integer>>(tp.getContextL());
                    tmp.addAll(IActiveCondition.pathToRoot(l, p));
                    contextL = ImmutableCreator.create(tmp);
                }
                if (tp.getKRight() != null) {
                    ArrayList<ImmutablePair<FunctionSymbol, Integer>> tmp = new ArrayList<ImmutablePair<FunctionSymbol, Integer>>(tp.getContextR());
                    tmp.addAll(IActiveCondition.pathToRoot(r, p));
                    contextR = ImmutableCreator.create(tmp);
                }

                TRSTerm left = l.getSubterm(p);
                TRSTerm right = r.getSubterm(p);
                if (!left.equals(right) || (contextL == null && contextR != null) || (contextL != null && !contextL.equals(contextR))) {
                    ItpfItp itp = ItpfItp.create(
                            left, tp.getKLeft(), contextL,
                            rel,
                            right, tp.getKRight(), contextR,
                            tp.getS());
                    addTo.add(this.mark(tp, itp));
                }
            }
        }

        @Override
        protected boolean checkVisit(Itpf itpf) {
            if (this.applicationCount != 0 && this.mode == ApplicationMode.SingleStep) {
                return false;
            }
            Set<IECap> estimations = (Set<IECap>)itpf.getMark(ItpfMark.ItpfCap);
            if (estimations != null && estimations.contains(this.cap)) {
                return false;
            }
            return true;
        }

        @Override
        protected Itpf mark(Itpf origItpf, Itpf newItpf) {
            if (this.mode == ApplicationMode.Multistep || origItpf.isAtom()) {
                Set<IECap> estimations = origItpf.getMark(ItpfMark.ItpfCap);
                if (estimations == null) {
                    estimations = new LinkedHashSet<IECap>();
                } else {
                    synchronized(estimations) {
                        estimations = new LinkedHashSet<IECap>(estimations);
                    }
                }
                estimations.add(this.cap);
                newItpf.setMark(this.mark, estimations);
            }
            if (origItpf != newItpf) {
                origItpf.copyCompatibleMarks(newItpf, this.mark);
            }
            return newItpf;
        }
    }
}
