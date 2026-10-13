package aprove.solver.Engines;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.SMTUtility.*;

/**
 * Calls some SMTLIB2-compatible SMT solver and tries to get a model for a given
 * SMT formula.
 *
 * @author Marc Brockschmidt
 */
public class SMTLIBEngine extends SMTEngine {
    /**
     * Arguments for this SMTLIB2-compatible SMT engine.
     */
    public static class Arguments extends SMTEngine.Arguments {
        /**
         * Just a random, but fixed number.
         */
        private static final int SEED = 463345727;

        /** The actual command that needs to be called. */
        //public String SMTSOLVER = "z3 smt.random_seed=" + Arguments.SEED;
        public String SMTSOLVER = "z3";

        /** Things needed to use this as SMTLIB-compatible solver. */
        public String ARGUMENTS = "-smt2";
    }

    /** The log facility used for debugging stuff. */
    private static final Logger LOG = Logger
        .getLogger("aprove.solver.Engines.SMTLIBEngine");

    /** The arguments given to this processor. */
    private final Arguments args;

    @ParamsViaArgumentObject
    public SMTLIBEngine(final Arguments arguments) {
        super(arguments);
        this.args = arguments;
    }

    public SMTLIBEngine() {
        super(new Arguments());
        this.args = new Arguments();
    }

    @Override
    public
        YNM
        satisfiable(final List<Formula<SMTLIBTheoryAtom>> formulas, final SMTLogic logic, final Abortion aborter)
            throws AbortionException,
                WrongLogicException
    {
        return this.solveAndPutIntoFormula(formulas, logic, aborter);
    }

    @Override
    public Pair<YNM, Map<String, String>> solve(
        final List<Formula<SMTLIBTheoryAtom>> formulas,
        final SMTLogic logic,
        final Abortion aborter) throws AbortionException
    {
        final SMTLIBFormulaOutputVisitor vis = SMTFormulaToSMTLIBVisitor.create(logic);
        for (final Formula<SMTLIBTheoryAtom> f : formulas) {
            vis.handleConstraint(f);
        }
        // Retrieve old names for the variables and functions
        final Pair<YNM, Map<String, String>> resultPair = this.solve(vis.getResult(), logic, aborter);
        if (resultPair == null) {
            // the solver could not be run, e.g. since AProVE is being shut down
            return new Pair<YNM, Map<String, String>>(YNM.MAYBE, new LinkedHashMap<String, String>());
        }

        resultPair.y = SMTEngine.translateResultMapToOldNames(resultPair.y, vis.getVarNameMap());

        return resultPair;
    }

    public YNM solveAndPutIntoFormula(
        final List<Formula<SMTLIBTheoryAtom>> formulas,
        final SMTLogic logic,
        final Abortion aborter) throws AbortionException, WrongLogicException
    {
        final SMTLIBFormulaOutputVisitor vis = SMTFormulaToSMTLIBVisitor.create(logic);

        for (final Formula<SMTLIBTheoryAtom> f : formulas) {
            vis.handleConstraint(f);
        }
        // Retrieve old names for the variables and functions
        final Pair<YNM, Map<String, String>> resultPair = this.solve(vis.getResult(), logic, aborter);
        if (resultPair == null) {
            // WOOOOOWWW if THAT happens, there is something seriously wrong (like no more MEM)
            return YNM.MAYBE;
        }

        final YNM resType = resultPair.x;
        final Map<String, String> result = resultPair.y;
        if (result == null) {
            assert (resType != YNM.YES) : "SMT returned SAT, but we have no model!";
            return resType;
        }
        final SMTLIBVarNameMap varNameMap = vis.getVarNameMap();
        final Map<String, SMTLIBAssignableSemantics> nameToVarMap = varNameMap.getNameToVarMap();
        for (final Map.Entry<String, String> e : result.entrySet()) {
            final String key = e.getKey();
            final String val = e.getValue();

            if (key.startsWith("(")) {
                // Function value
                final SMTLIBFunction<?> v = (SMTLIBFunction<?>) nameToVarMap.get(key);
                if (v != null) {
                    final String[] sArr = key.split(" ");
                    final List<String> params = new ArrayList<String>(sArr.length);
                    for (final String element : sArr) {
                        params.add(element);
                    }
                    v.setResult(params, val);
                }
            } else {
                // Variable value
                final SMTLIBVariable<?> v = (SMTLIBVariable<?>) nameToVarMap.get(key);
                if (v != null) {
                    v.setResult(val);
                }
            }
        }
        return resType;
    }

    /** {@inheritDoc} */
    @Override
    public Pair<YNM, Map<String, String>> solve(final String smtString, final SMTLogic logic, final Abortion aborter)
        throws AbortionException
    {
        File input = null;
        try {
            //Write our data:
            aborter.checkAbortion();
            input = File.createTempFile("aproveSMT", ".smt2");
            input.deleteOnExit();
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(smtString);
            inputWriter.close();
            aborter.checkAbortion();

            //Call the actual solver:
            final List<String> cmdArgs = Arrays.asList(this.args.ARGUMENTS.split(" "));
            SMTLIBEngine.LOG.log(Level.FINER, "Wrote SMTLIB output to {0}\n", input.getCanonicalPath());
            SMTLIBEngine.LOG.log(Level.FINER, "Invoking {0}\n", this.args.SMTSOLVER + cmdArgs);

            final Map<String, String> resMap = new LinkedHashMap<String, String>();
            Pair<List<String>, List<String>> lines;
            try {
                final List<String> cmds = new ArrayList<>();
                cmds.add(this.args.SMTSOLVER);
                cmds.addAll(cmdArgs);
                cmds.add(input.getCanonicalPath());
                lines = ExecHelper.exec(cmds, aborter);
            } catch (final InterruptedException e) {
                assert false : "SMT interrupted!";
                return new Pair<>(YNM.MAYBE, resMap);
            }
            aborter.checkAbortion();

            for (final String errorLine : lines.y) {
                System.err.println("SMT solver stderr: " + errorLine);
                continue;
            }

            //Try to parse the input (really badly):
            YNM resType = null;
            final Iterator<String> it = lines.x.iterator();
            while (it.hasNext()) {
                final String line = it.next();
                aborter.checkAbortion();
                SMTLIBEngine.LOG.log(Level.FINEST, "{0}\n", line);
                if (line.startsWith("unsat")) {
                    assert (resType == null) : "Got two answers from SMT solver!";
                    SMTLIBEngine.LOG.log(Level.FINE, "SMT solver says: UNSAT\n");
                    resType = YNM.NO;
                } else if (line.startsWith("sat")) {
                    assert (resType == null) : "Got two answers from SMT solver!";
                    SMTLIBEngine.LOG.log(Level.FINE, "SMT solver says: SAT\n");
                    resType = YNM.YES;
                } else if (line.startsWith("unknown")) {
                    assert (resType == null) : "Got two answers from SMT solver!";
                    SMTLIBEngine.LOG.log(Level.FINE, "SMT solver says: UNKNOWN\n");
                    resType = YNM.MAYBE;
                } else if (line.startsWith("(define (")) {
                    //Function definition, unhandled.
                } else if (line.startsWith("(define ")) {
                    // Variable result: (define x 1)
                    final String[] sArr = line.split(" ");
                    // sArr[0] = "(define", [1] is var name, [2] is value + ")"
                    assert (sArr.length == 3) : "Cannot parse SMT solver answer: " + line;
                    if (sArr[2].endsWith("\"))")) {
                        resMap.put(sArr[1], sArr[2].substring(0, sArr[2].length() - 4));
                    } else {
                        resMap.put(sArr[1], sArr[2].substring(0, sArr[2].length() - 1));
                    }
                } else if (line.trim().startsWith("(define-fun")) {
                    String completeLine;
                    if (!line.endsWith(")")) {
                        assert (it.hasNext()) : "Expected more lines, only got '" + line + "'";
                        completeLine = line + " " + it.next();
                    } else {
                        completeLine = line;
                    }
                    // Variable result: (define-fun x () Int 0)
                    final String[] sArr = completeLine.trim().split("[ \t]+");
                    // sArr[0] = "(define-fun", [1] is var name, [2] () [3] Int [4] is value + ")"
                    //assert (sArr.length == 5 || sArr.length == 6 && sArr[2].equals("()") && sArr[3].equals("Int")) : "Cannot parse SMT solver answer: "
                    //    + completeLine;
                    if (sArr.length == 6) {
                        assert sArr[4].equals("(-") : "Cannot parse SMT solver answer: " + completeLine;
                        resMap.put(sArr[1], "-" + sArr[5].substring(0, sArr[5].length() - 2));
                    } else {
                    	if (sArr[3].equals("Int")) {
                    		resMap.put(sArr[1], sArr[4].substring(0, sArr[4].length() - 1));
                    	} else if (sArr[3].equals("Real")) {
                    		// non fraction "whole" reals e.g. 0.0, 2.0 etc
                    		if (sArr[4].endsWith(".0)")){
                    			resMap.put(sArr[1], sArr[4].substring(0, sArr[4].length() - 1));
                    		} else {
                    		String numerator = sArr[5];
                    		numerator = numerator.endsWith(".0") ? numerator.substring(0, numerator.length() - 2) : numerator;
                    				
                    		String denominator = sArr[6].substring(0, sArr[6].length() - 2);
                    		denominator = denominator.endsWith(".0") ? denominator.substring(0, denominator.length() - 2) : denominator;
                    		
                    		resMap.put(sArr[1],  
                    				numerator + " " + "/ " + denominator);
                    		}
                    	}
                    	else assert false: "Cannot parse SMT solver answer: " + completeLine;
                    }
                } else {
                    //Unknown line, try to ignore.
                }
            }

            input.delete();
            aborter.checkAbortion();
            if (resType == null) {
                SMTLIBEngine.LOG.warning("Got no answers from SMT solver!");
                resType = YNM.MAYBE;
            }
            return new Pair<YNM, Map<String, String>>(resType, resMap);
        } catch (final IOException e) {
            e.printStackTrace();
        } finally {
            if (input != null) {
                input.delete();
            }
        }

        return null;
    }
}
