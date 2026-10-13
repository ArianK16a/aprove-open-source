package aprove.verification.oldframework.Input;

import java.util.*;

/**
 * @author dickmeis
 * @version $Id$
 */
public enum Language {

    /*
     * Please use a separate line for each entry. This helps to prevent
     * merge conflicts and makes it easier to see what changed in a diff.
     *
     * Also, please use alphabetic ordering.
     */
    C,
    CLS,
    CpxRelTRS(HandlingMode.RuntimeComplexity),
    CpxTRS(HandlingMode.RuntimeComplexity),
    CSPATRS,
    CSR,
    CTRS,
    DIOPHANTINE(HandlingMode.Satisfiability),
    ETES, // TRS modulo some equational theory in "classic" AProVE .tes syntax
    ETRS,
    FP(HandlingMode.Termination, HandlingMode.TheoremProver),
    GTRS,
    HASKELL,
    IDP,
    INTTRS,
    IPAD,
    ITRS,
    CpxITrs(HandlingMode.RuntimeComplexity),
    CpxIntTrs(HandlingMode.RuntimeComplexity),
    JBC,
    LCTRS, // logically constrained TRS in the ARI format
    MCS, // Monotonicity Constraint Transition System of MCNP fame
    LLVM,
    OTRS,
    PATRS,
    PL_FORMULA,
    PROLOG,
    QDP,
    QTRS,
    RTRS,
    SES,
    SIMPLIFY(HandlingMode.TheoremProver),
    SRS,
    STRS(HandlingMode.TheoremProver),
    T2,
    TERM,
    TES,
    TRIPLES,
    TRS,
    TYPETERM,
    PTRS,
    CpxPTRS(HandlingMode.RuntimeComplexity), 
    ConfTRS;

    private final HandlingMode defaultMode;
    private final EnumSet<HandlingMode> modes;

    private Language() {
        this(HandlingMode.Termination, EnumSet.of(HandlingMode.Termination));
    }

    private Language(HandlingMode mode) {
        this(mode, EnumSet.of(mode));
    }

    private Language(HandlingMode mode1, HandlingMode mode2) {
        this(mode1, EnumSet.of(mode1, mode2));
    }

    private Language(HandlingMode defaultMode, EnumSet<HandlingMode> modes) {
        this.defaultMode = defaultMode;
        this.modes = modes;
    }

    public HandlingMode getDefaultMode() {
        return this.defaultMode;
    }

    public boolean supports(HandlingMode mode) {
        return this.modes.contains(mode);
    }

}
