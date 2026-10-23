package aprove.verification.dpframework.LCTRSProblem.Processors;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.LCTRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Asks an SMT solver whether logical terms of an LCTRS are satisfiable. The terms are written in SMT-LIB,
 * which is the language they come from.
 */
final class LCTRSSmt {

    private final LCTRSSignature signature;

    /** The time limit of the solver for one call in milliseconds. */
    private final int timeout;

    /** The answers for the scripts that were already checked. */
    private final Map<String, Boolean> unsatisfiable = new LinkedHashMap<>();

    LCTRSSmt(final LCTRSSignature signature, final int timeout) {
        this.signature = signature;
        this.timeout = timeout;
    }

    /**
     * @return the number of calls of the solver so far
     */
    int getCalls() {
        return this.unsatisfiable.size();
    }

    /**
     * A conjunction of logical terms whose variables are kept apart by prefixes of their names, so that
     * terms of two rules can be combined without renaming them.
     */
    final class Formula {

        private final Map<String, LCTRSSort> constants = new LinkedHashMap<>();

        private final List<String> assertions = new ArrayList<>();

        /**
         * Adds the conjunct <code>term</code>, a term of sort Bool.
         *
         * @param sorts the sorts of the variables of the term
         */
        void add(final TRSTerm term, final Map<TRSVariable, LCTRSSort> sorts, final String prefix) {
            this.assertions.add(this.toSmt(term, sorts, prefix));
        }

        /**
         * Adds the conjunct <code>left = right</code>.
         */
        void addEquation(
            final TRSTerm left,
            final Map<TRSVariable, LCTRSSort> leftSorts,
            final String leftPrefix,
            final TRSTerm right,
            final Map<TRSVariable, LCTRSSort> rightSorts,
            final String rightPrefix)
        {
            final String smtLeft = this.toSmt(left, leftSorts, leftPrefix);
            this.assertions.add("(= " + smtLeft + " " + this.toSmt(right, rightSorts, rightPrefix) + ")");
        }

        private String toSmt(final TRSTerm term, final Map<TRSVariable, LCTRSSort> sorts, final String prefix) {
            if (term.isVariable()) {
                final String name = "|" + prefix + ((TRSVariable) term).getName() + "|";
                this.constants.put(name, sorts.get(term));
                return name;
            }
            final TRSFunctionApplication app = (TRSFunctionApplication) term;
            final FunctionSymbol f = app.getRootSymbol();
            if (LCTRSSmt.this.signature.isValue(f)) {
                // SMT-LIB has no negative literals
                return f.getName().startsWith("-") ? "(- " + f.getName().substring(1) + ")" : f.getName();
            }
            final StringBuilder res = new StringBuilder("(");
            res.append(
                LCTRSSmt.this.signature.userTheorySymbols().containsKey(f)
                    ? "|" + f.getName() + "|"
                    : LCTRSSmt.this.signature.getName(f));
            for (final TRSTerm arg : app.getArguments()) {
                res.append(" ").append(this.toSmt(arg, sorts, prefix));
            }
            return res.append(")").toString();
        }

        /**
         * @return true iff the solver showed that the conjunction is unsatisfiable; false if it is
         * satisfiable or the solver gave no answer
         */
        boolean isUnsatisfiable(final Abortion aborter) throws AbortionException {
            if (this.assertions.isEmpty()) {
                return false;
            }
            final StringBuilder script = new StringBuilder();
            script.append("(set-option :timeout ").append(LCTRSSmt.this.timeout).append(")\n");
            for (final LCTRSUserTheorySymbol userSymbol : LCTRSSmt.this.signature.userTheorySymbols().values()) {
                final Formula body = new Formula();
                final Map<TRSVariable, LCTRSSort> sorts = new LinkedHashMap<>();
                script.append("(define-fun |").append(userSymbol.symbol().getName()).append("| (");
                for (int i = 0; i < userSymbol.parameters().size(); i++) {
                    final TRSVariable parameter = userSymbol.parameters().get(i);
                    final LCTRSSort sort = userSymbol.declaration().argumentSorts().get(i);
                    sorts.put(parameter, sort);
                    script.append("(").append(body.toSmt(parameter, sorts, "")).append(" ").append(sort).append(")");
                }
                script.append(") ").append(userSymbol.declaration().resultSort()).append(" ");
                script.append(body.toSmt(userSymbol.body(), sorts, "")).append(")\n");
            }
            this.constants.forEach(
                (name, sort) -> script.append("(declare-const ").append(name).append(" ").append(sort).append(")\n"));
            this.assertions.forEach(assertion -> script.append("(assert ").append(assertion).append(")\n"));
            final String smt = script.append("(check-sat)\n").toString();
            Boolean unsat = LCTRSSmt.this.unsatisfiable.get(smt);
            if (unsat == null) {
                final Pair<YNM, Map<String, String>> answer = new SMTLIBEngine().solve(smt, SMTLogic.QF_NIA, aborter);
                unsat = answer != null && answer.x == YNM.NO;
                LCTRSSmt.this.unsatisfiable.put(smt, unsat);
            }
            return unsat;
        }

    }

}
