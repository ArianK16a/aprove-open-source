/*   Type:        ANTLR
 *   Title:       LCTRS grammar of the ARI format
 *   Description: A grammar for logically constrained TRSs in the ARI format,
 *                see https://project-coco.uibk.ac.at/ARI/lctrs.php
 *   Project:     AProVE
 *   Department:  RWTH Aachen / Templergraben 55 / D-52056 Aachen
 *
 *      LCTRS ::= ( format LCTRS (:smtlib standard)? )
 *                    theory+ smt-def* sort-decl* fun-decl* rule*
 *     theory ::= ( theory smt-theory )
 *  sort-decl ::= ( sort identifier )
 *       sort ::= identifier | ( _ identifier+ )
 *    smt-def ::= ( define-fun identifier ( vars ) sort formula )
 *   fun-decl ::= ( fun identifier type )
 *       type ::= sort | ( -> sort+ sort )
 *       rule ::= ( rule term term (:guard term)? (:var ( vars ))? )
 *       vars ::= (( identifier sort ))*
 *
 *   In addition, the declaration ( entrypoint identifier ) of the integer transition systems of the TPDB
 *   is accepted. The parser passes every declaration on to aprove.input.Programs.ariLctrs.LctrsBuilder,
 *   which resolves the identifiers (a symbol must be declared before it is used), checks the sorts and
 *   builds the LCTRS.
 */

grammar ariLctrs;

options {
    language = Java;
}

@lexer::header {
package aprove.input.Generated.ariLctrs;
}

@lexer::members {
    /** The errors of the lexer, which would otherwise only be printed. */
    private final java.util.List<RecognitionException> lexerErrors = new java.util.ArrayList<RecognitionException>();

    public java.util.List<RecognitionException> getLexerErrors() {
        return this.lexerErrors;
    }

    @Override
    public void reportError(RecognitionException e) {
        this.lexerErrors.add(e);
    }
}

@header {
package aprove.input.Generated.ariLctrs;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import aprove.input.Programs.ariLctrs.LctrsBuilder;
import aprove.verification.dpframework.BasicStructures.TRSTerm;
import aprove.verification.dpframework.LCTRSProblem.LCTRSRule;
import aprove.verification.dpframework.LCTRSProblem.LCTRSSort;
}

@members {
    // reject unsupported inputs instead of recovering by deleting or inserting a token
    @Override
    protected Object recoverFromMismatchedToken(IntStream input, int ttype, org.antlr.runtime.BitSet follow)
        throws RecognitionException
    {
        throw new MismatchedTokenException(ttype, input);
    }
}

// ... and instead of recovering using the follow set (as in ariTrs.g)
@rulecatch {
catch (RecognitionException e) {
    if (true) {
        // if (true): kludge to persuade the Java compiler that some later
        // (here auto-generated) unreachable return statements might be
        // reachable after all and is thus not to be deemed a compile error
        throw e;
    }
}
}

lctrs[LctrsBuilder b]
    : LPAR k=FORMAT fmt=identifier ( SMTLIB std=identifier )? RPAR { $b.format($fmt.s, $std.s, $k.line); }
      ( LPAR decl[$b] RPAR )*
      EOF
;

decl[LctrsBuilder b]
    @init {
        TRSTerm guard = LCTRSRule.TRUE;
    }
    : k=THEORY id=identifier { $b.theory($id.s, $k.line); }
    | k=SORT id=identifier { $b.declareSort($id.s, $k.line); }
    | k=DEFINE_FUN id=identifier LPAR ps=vars[$b] RPAR s=sort[$b] body=term[$b] {
        $b.define($id.s, $ps.map, $s.rs, $body.t, $k.line);
      }
    | k=FUN id=identifier ty=type[$b] { $b.function($id.s, $ty.sorts, $k.line); }
    | k=RULE l=term[$b] r=term[$b] ( GUARD g=term[$b] { guard = $g.t; } )? ( VAR LPAR vs=vars[$b] RPAR )? {
        $b.rule($l.t, $r.t, guard, $vs.map, $k.line);
      }
    | k=ENTRYPOINT id=identifier { $b.entrypoint($id.s, $k.line); }
;

sort[LctrsBuilder b] returns [LCTRSSort rs]
    @init {
        List<String> names = new ArrayList<String>();
        int line = input.LT(1).getLine();
    }
    @after {
        $rs = $b.sort(names, line);
    }
    : id=identifier { names.add($id.s); }
    | LPAR UNDERSCORE ( i=identifier { names.add($i.s); } )+ RPAR
;

/* the sorts of the arguments followed by the sort of the result */
type[LctrsBuilder b] returns [List<LCTRSSort> sorts]
    @init {
        $sorts = new ArrayList<LCTRSSort>();
    }
    : s=sort[$b] { $sorts.add($s.rs); }
    | LPAR ARROW ( a=sort[$b] { $sorts.add($a.rs); } )+ RPAR
;

vars[LctrsBuilder b] returns [Map<String, LCTRSSort> map]
    @init {
        $map = new LinkedHashMap<String, LCTRSSort>();
    }
    : ( p=LPAR id=identifier s=sort[$b] RPAR { $b.variable($map, $id.s, $s.rs, $p.line); } )*
;

term[LctrsBuilder b] returns [TRSTerm t]
    @init {
        List<TRSTerm> args = new ArrayList<TRSTerm>();
        int line = input.LT(1).getLine();
    }
    : id=identifier { $t = $b.term($id.s, args, line); }
    | LPAR
      ( q=(FORALL | EXISTS) LPAR vars[$b] RPAR term[$b] { $t = $b.quantifier($q.text, line); }
      | h=head ( a=term[$b] { args.add($a.t); } )+ { $t = $b.term($h.s, args, line); }
      )
      RPAR
;

/* the symbol at the root of an application: an identifier or an indexed identifier like (_ divisible 2) */
head returns [String s]
    @init {
        StringBuilder indexed = new StringBuilder("(_");
    }
    : id=identifier { $s = $id.s; }
    | LPAR UNDERSCORE ( i=identifier { indexed.append(' ').append($i.s); } )+ RPAR {
        $s = indexed.append(')').toString();
      }
;

/* the words of the declarations are no reserved words of SMT-LIB and can be used as identifiers */
identifier returns [String s]
    : tok=(SYMBOL | FORMAT | THEORY | SORT | DEFINE_FUN | FUN | RULE | ENTRYPOINT) { $s = $tok.text; }
    | q=QUOTED_SYMBOL { $s = $q.text.substring(1, $q.text.length() - 1); }
;

LPAR                : '(';
RPAR                : ')';
FORMAT              : 'format';
THEORY              : 'theory';
SORT                : 'sort';
DEFINE_FUN          : 'define-fun';
FUN                 : 'fun';
RULE                : 'rule';
ENTRYPOINT          : 'entrypoint';
ARROW               : '->';
UNDERSCORE          : '_';
FORALL              : 'forall';
EXISTS              : 'exists';
SMTLIB              : ':smtlib';
GUARD               : ':guard';
VAR                 : ':var';

/* simple symbols of SMT-LIB and the literals, e.g. numerals */
SYMBOL
    : SYMBOL_CHAR+
;

fragment SYMBOL_CHAR
    : 'a'..'z' | 'A'..'Z' | '0'..'9'
    | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' | '=' | '<' | '>' | '.' | '?' | '/' | '#'
    | '\''
;

QUOTED_SYMBOL
    : '|' ~('|' | '\\')* '|'
;

WHITESPACE : ( '\t' | ' ' | '\r' | '\n' )+ { $channel = HIDDEN; };

COMMENT : ';' ~( '\r' | '\n' )* { $channel = HIDDEN; };
