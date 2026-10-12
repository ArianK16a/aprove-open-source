# IDPv1 strategy evaluation

Goal: find the most efficient `idpv1` strategy (used for ITRS and JBC), taking both
the verdicts and the runtime into account. Notes on the processors: `IDP-strategies.txt`.

## Setup

- AProVE at `idp-clean2` 703dcc09a0, frozen copy in `bench/strategy-eval/jars/`.
- Runner: `bench/strategy-eval/run.py`. A variant is a copy of `current.strategy` in which
  single top-level definitions (`idpv1 = ...`) are replaced. Each file runs as
  `java -ea -Xmx3g -jar aprove.jar -m wst -p plain -t <timeout> -s <variant>`,
  pinned to 4 cores (`taskset`), 2 files in parallel on the 8-core machine.
  Per file: verdict and wall time (including JVM start-up, ~1 s).
- Results per run: `bench/strategy-eval/runs/<name>/results.csv` and `out/` (full proofs).
- Input sets: `../TPDB/Integer_TRS_Innermost` (ITRS, 117), `../TPDB-ARI/Java_Bytecode`
  (JBC, 222), `../TPDB-ARI/Java_Bytecode_Recursive` (JBC-Rec, 143), small sets in
  `bench/strategy-eval/TPDB-small` (see below).
- JBC: the SCCs of the termination graph each become an IDP that runs through `idpv1`;
  NO answers for JBC come from `JBCNonTerm`, which runs in parallel and is not part of
  `idpv1`. ITRS: `ITRStoQTRS[CONSTONLY]` is tried before `itrsToIdp:idpv1`.

## Strategies

The original `idpv1` on `aprove/main`:

```
idpv1 = First(
          IDPtoQDP[Apply = CONSTONLY]:RunDefaultStrategyForObligation,
          First(
            Solve(Timer(12000, idpFast)),
            AnyDelay(5000,
              Solve(idpSlow),
              Solve(IDPtoQDP[Apply = ALWAYSFILTER]:RunDefaultStrategyForObligation))))
```

The current `idpv1` on `idp-clean2` (`idpv1MainLoop` is the original with `Any` instead of
`AnyDelay` and the temporary filters added):

```
idpv1 = Any(
          Solve(IDPtoIRS:RunDefaultStrategyForObligation),
          Solve(IDPtoQDP[Ints=REMOVE]:RunDefaultStrategyForObligation),
          idpv1MainLoop)
```

## Results

### Baseline on the full sets (current `idpv1`, 30 s)

| Set | YES | NO | MAYBE | KILLED | total time |
|---|---|---|---|---|---|
| ITRS (117) | 105 | 0 | 0 | 12 | 862 s |
| JBC-Rec (143) | 89 | 41 | 6 | 7 | 1004 s |
| JBC (222) | 197 | 0 | 5 | 20 | 1988 s |

Which technique the proofs use (the first branch that finishes wins in `Any`):

- ITRS: 86 via `IDPtoIRS`, 12 via `IDPNonInf` (idpFast/idpSlow), 3 via `IDPtoQDP`, 4 via
  temporary filters combined with other techniques. None before the IDP (`ITRStoQTRS`).
  The KILLED ones are a.02, A15, A16, ackTen, choice, collatz, countUpNo, Ex04, f91,
  maxsort, poly3, practical3.
- JBC: most files need `IDPtoIRS` for some SCCs and `IDPtoQDP` for others (each SCC is its
  own IDP). `IDPNonInf` appears in 16 files, the temporary filters in 21. JBC-Rec NO
  answers come from `JBCNonTerm`.

### Small sets (`bench/strategy-eval/TPDB-small`, 106 files)

Picked from the baseline so that every technique combination occurs, plus the slow
files, some KILLED/MAYBE files with IDP parts and a few NO files (soundness guard):

- ITRS (40): all 19 files not proved purely via `IDPtoIRS`, 14 `IDPtoIRS` files (fast and
  slowest), 4 KILLED (a.02, choice, collatz, maxsort).
- JBC-Rec (33) and JBC (33): files from each technique combination, KILLED/MAYBE files
  with IDP parts (e.g. Norm, EvenOdd, Collatz, Distances, juHashMapCreateHashCode), 3 NO
  files from `JBCNonTerm`.

Set lists: `bench/strategy-eval/sets/{itrs,jbcrec,jbc}-small.txt`, combined `small.txt`.

### Individual processors on the small sets (30 s)

Each variant replaces `idpv1` by a single technique (wrapped in `Solve`). Y/N/M/K =
YES/NO/MAYBE/KILLED, `time` = sum of the wall times of all files, `tYES` = of the proved
ones. The 3 NO in JBC-Rec come from `JBCNonTerm` and are the same in every variant.
`qdp-constonly` (502 s in total) roughly shows the fixed cost of the front ends, JVM
start-up and a quick failure.

| variant | ITRS Y/K | ITRS time | JBC Y/K | JBC time | JBC-Rec Y/K | JBC-Rec time | total |
|---|---|---|---|---|---|---|---|
| base-current | 36/4 | 258 | 23/8 | 461 | 26/3 | 387 | 1106 |
| base-main | 33/7 | 348 | 21/8 | 465 | 24/5 | 396 | 1209 |
| qdp-constonly `IDPtoQDP[Apply=CONSTONLY]` | 1/0 | 74 | 0/0 | 202 | 1/0 | 227 | 502 |
| qdp-encode `IDPtoQDP` | 7/31 | 1096 | 5/4 | 382 | 3/6 | 466 | 1945* |
| qdp-encode-filter `IDPtoQDP[Apply=ALWAYSFILTER]` | 8/30 | 1057 | 5/4 | 394 | 3/6 | 444 | 1896 |
| qdp-remove `IDPtoQDP[Ints=REMOVE]` | 3/1 | 125 | 2/0 | 228 | 5/1 | 267 | 620 |
| qdp-remove-filter `[Ints=REMOVE, Apply=ALWAYSFILTER]` | 3/1 | 124 | 2/0 | 250 | 5/1 | 269 | 643 |
| irs-intonly `IDPtoIRS[Apply=INTONLY]` | 19/1 | 122 | 5/1 | 263 | 4/0 | 197 | 582 |
| irs `IDPtoIRS` | 20/6 | 313 | 9/3 | 330 | 8/1 | 284 | 926 |
| idp-fast `idpFast` | 7/0 | 79 | 2/1 | 252 | 5/1 | 235 | 566 |
| idp-slow `idpSlow` | 31/9 | 406 | 20/9 | 549 | 15/13 | 632 | 1587 |
| irstemp-slow `IDPtoIRS[TempFilter]` then `idpSlow` | 31/9 | 404 | 25/4 | 452 | 19/9 | 511 | 1367 |
| qdptemp-slow `IDPtoQDP[Ints=REMOVE, TempFilter]` then `idpSlow` | 32/8 | 371 | 21/9 | 526 | 21/7 | 477 | 1374 |

\* timings disturbed by manual tests running at the same time.

Observations:

- No single technique comes close to the combination: many JBC files (Count, Flatten,
  LessLeaves, the juHashMap files, Alternate, TermsCreateMatch, Matrix, Binomial) need
  different techniques for different SCCs or after a temporary filter.
- `IDPtoIRS` alone proves three files that are KILLED in the baseline (Graph.jar 18 s,
  Distances.jar 23 s, juLinkedListCreateEquals.jar 26 s) and BinarySearch.jar in 13 s
  instead of 31 s. In the baseline the IRS branch competes with many parallel branches.
- `IDPtoIRS[Apply=INTONLY]` proves MinusUserDefined.jar (29 s, KILLED everywhere else).
  It is cheap (fails fast) but `IDPtoIRS` covers everything else it proves.
- The QDP encoding (`IDPtoQDP` with or without ALWAYSFILTER) is expensive (30 timeouts
  on ITRS) and only needed for choice.itrs (28 s, KILLED in the baseline).
- `IDPtoQDP[Ints=REMOVE]` is cheap and proves the files that only need the term
  structure (incList, minsort, quicksort, tree and list programs). ALWAYSFILTER makes no
  difference there.
- `idpFast` is cheap and proves few files quickly; `idpSlow` is needed for the
  NonInf-type ITRS files (10, A04, A09, A10, Ex09, conv, countUpExp, log_RTA09, powFast,
  round) but is slow alone.
- The temporary projections (`TempFilter`) help a lot on top of `idpSlow`, and they complement each other:
  the IRS filter proves Graph, Distances, juLinkedListCreateEquals, BinarySearch, Queen,
  Test11, Test12, MainFind; the QDP filter proves PartitionList.jar (KILLED in the
  baseline), RotateTree, TermCreateCollect, TermsCreateMatch, Alternate, Main,
  eratosthenes. Both return unsuccessful if no node was removed (checked in
  `IDPTemporaryFilter`), so they do not duplicate the IDP.
- Velroyen08-moduloLower.jar (non-terminating) gets NO from `JBCNonTerm` only sometimes,
  independent of `idpv1` (reproduced with both baselines): timing noise.

### Combinations, round 1 (small sets, 30 s)

All are modifications of the current `idpv1` (exact definitions in
`bench/strategy-eval/variants.sh`):

- `cur-noenc`: no QDP encoding (`IDPtoQDP[Apply=ALWAYSFILTER]`), neither in
  `idpv1MainLoop` nor as fallback in `idpNonInfSlow`.
- `cur-lateenc`: the encoding only once, in `idpv1MainLoop`, after `Delay(15000, ...)`.
- `cur-nofast`: no blocking `Solve(Timer(12000, idpFast))` stage in `idpv1MainLoop`; the
  filters, `idpSlow` and the encoding start immediately.
- `flat`: `First(CONSTONLY, Any(IRS, QDP-REMOVE, idpv1Loop))`, where `idpv1Loop` runs
  `idpSlow`, both filters (recursing into `idpv1Loop`) and the encoding after 15 s;
  no `idpFast` stage, `CONSTONLY` only at the top.
- `flat-rec`: like `flat`, but the filters recurse into the full `idpv1`.

| variant | ITRS Y/K | ITRS time | JBC Y/K | JBC time | JBC-Rec Y/K | JBC-Rec time | total | vs. base-current |
|---|---|---|---|---|---|---|---|---|
| base-current | 36/4 | 258 | 23/8 | 461 | 26/3 | 387 | 1106 | |
| cur-noenc | 36/3 | 222 | 23/8 | 465 | 25/3 | 361 | 1048 | -AlternatingGrowReduceRec2 |
| cur-lateenc | 36/4 | 243 | 23/8 | 474 | 25/5 | 406 | 1123 | -AlternatingGrowReduceRec2 |
| cur-nofast | 36/4 | 273 | 23/8 | 491 | 27/2 | 426 | 1190 | +PartitionList |
| flat | 36/4 | 261 | 23/8 | 514 | 24/5 | 430 | 1205 | -AlternatingGrowReduceRec2, -BinarySearch |
| flat-rec | 36/4 | 250 | 23/8 | 542 | 26/3 | 442 | 1234 | +PartitionList, -AlternatingGrowReduceRec2 |

Observations:

- The current structure is already good; none of the variants is better in both
  verdicts and time. Differences of 1-2 s per file are within the noise.
- The QDP encoding costs time through contention (ITRS 222 s instead of 258 s without
  it; BinarySearch.jar 18 s instead of 31 s), but AlternatingGrowReduceRec2.jar needs it
  early (the encoding alone proves it in 17 s), so neither removing nor delaying it is
  free. choice.itrs needs it too but takes ~28 s even alone.
- Without the `idpFast` stage, the QDP filter gets CPU earlier and proves PartitionList.jar
  (KILLED in the baseline), but everything else gets slower: the stage pays off.
- The flat variants (IRS/REMOVE/filters/`idpSlow` all in parallel from the start) are
  slower on JBC; too many branches compete for the 4 cores.

### Round 2 (small sets, 30 s, 2026-10-12)

- `base-current-r2`: the unchanged baseline again, to estimate the noise.
- `cur-enconce`: the QDP encoding only in `idpv1MainLoop`, not also as fallback in
  `idpNonInfSlow`.
- `cur-fast6`: `idpFast` timer 6 s instead of 12 s.
- `cur-enconce-fast6`: both.

| variant | ITRS Y/K | ITRS time | JBC Y/K | JBC time | JBC-Rec Y/K | JBC-Rec time | total | vs. base-current |
|---|---|---|---|---|---|---|---|---|
| base-current | 36/4 | 258 | 23/8 | 461 | 26/3 | 387 | 1106 | |
| base-current-r2 | 36/4 | 271 | 23/8 | 454 | 26/3 | 383 | 1108 | identical verdicts |
| cur-enconce | 36/4 | 246 | 23/8 | 461 | 26/3 | 357 | 1064 | |
| cur-fast6 | 36/4 | 258 | 23/8 | 454 | 27/2 | 363 | 1076 | +PartitionList |
| cur-enconce-fast6 | 36/4 | 253 | 23/8 | 442 | 26/3 | 363 | 1058 | |

Noise: two identical runs differ by 2 s in total (up to 13 s per subset), per file the
median difference is 0.3 s, 90% are below 1.6 s, and no verdict flips. So totals that
differ by 30-40 s are real differences, single files near 30 s are not.

Both changes are small, consistent gains without losses (-4% time); PartitionList.jar is
at the 30 s border (proved in 22-27 s by some variants). `cur-enconce-fast6` is the new
basis for the next rounds.

### Round 3 (small sets, 30 s): IRS head start

All on top of `cur-enconce-fast6`. `AnyDelay(t, A, B)` starts `B` after `t` ms or as soon
as `A` fails, so a head start costs nothing if the first branch fails quickly.

- `r3-irshead3` / `r3-irshead6`: `idpv1 = AnyDelay(3000 / 6000, Solve(IDPtoIRS:...),
  Any(Solve(IDPtoQDP[Ints=REMOVE]:...), idpv1MainLoop))`.
- `r3-bothhead3`: `AnyDelay(3000, Any(IRS, QDP-REMOVE), idpv1MainLoop)`.
- `r3-fast3`: `idpFast` timer 3 s instead of 6 s.

| variant | ITRS Y/K | ITRS time | JBC Y/K | JBC time | JBC-Rec Y/K | JBC-Rec time | total | vs. base-current |
|---|---|---|---|---|---|---|---|---|
| base-current | 36/4 | 258 | 23/8 | 461 | 26/3 | 387 | 1106 | |
| cur-enconce-fast6 | 36/4 | 253 | 23/8 | 442 | 26/3 | 363 | 1058 | |
| r3-irshead3 | 36/4 | 266 | 24/7 | 436 | 26/2 | 341 | 1042 | +Distances |
| r3-irshead6 | 36/4 | 302 | 26/5 (+1 NO) | 402 | 27/1 | 340 | 1044 | +Graph, Distances, juLinkedListCreateEquals, PartitionList, (moduloLower NO) |
| r3-bothhead3 | 36/4 | 272 | 23/8 | 469 | 26/3 | 372 | 1112 | |
| r3-fast3 | 36/4 | 273 | 23/8 | 514 | 27/3 | 421 | 1209 | +PartitionList |

- The 6 s IRS head start is the best variant so far: 5 more files, none lost, and less
  total time than the baseline. It fixes the starvation of the IRS branch (Graph 18 s,
  Distances 23 s, Matrix 13 s instead of 20 s, BinarySearch 16 s instead of 21 s).
- Its cost is on files where IRS runs long without success and `idpSlow` would be quick:
  A10.itrs 23 s instead of 5 s, A04.itrs 20 s instead of 4 s, 10.itrs 11 s instead of 4 s,
  log_RTA09.itrs, UnionFind.jar (+6 s each). Idea for the next round: let `idpSlow` (or
  its fast first stage) run next to IRS during the head start.
- A head start for QDP-REMOVE as well brings nothing; a 3 s `idpFast` timer is too short.

### Measurement problem found on 2026-10-12: orphaned SAT solvers

`run.py` killed only the Java process after a timeout, not the SAT solvers started by
AProVE. Two `minisat` processes survived from 10:19 on and used ~2 cores for more than an
hour. Affected and therefore **invalid**: `r3-fast3` (round 3) and all runs with the
prefix `n-` (round 4, jar d64ab6a546: `n-base-current` 1247 s, `n-cur-enconce-fast6`
1221 s, `n-r3-irshead6` 1268 s, `n-r4-irsslowhead6` 1318 s, `n-r4-irsfasthead6` 1347 s).
The earlier runs are consistent with each other (baseline 1106 s on 10-09 and 1108 s on
10-12 before the orphans appeared).

Fixed: each run now gets its own process group, which is killed afterwards. Before
measuring, check that no `minisat`/`yices` processes are left (`ps -eo comm | grep -c minisat`).

### Round 5 (small sets, 30 s, fixed runner): clean re-measurement

Prefix `c-` = first jar (703dcc09a0), prefix `h-` = jar 094bee3ece with the IRS fixes
(`ToolBox` unary minus, `IntTRSCompressionProcessor` proves empty IRSs, `IDPtoIRS` boolean
variables and abstraction of inexpressible subterms only).

| run | YES+NO | total | note |
|---|---|---|---|
| base-current (10-09, old runner) | 88 | 1106 | |
| c-base-current | 89 | 1062 | same strategy and jar, fixed runner |
| h-base-current | 89 | 1058 | +PartitionList.jar; the fixes cost no time |

The same baseline is 44 s faster with the fixed runner, so **all earlier runs were slightly
slowed down by short-lived leftover solvers**. Time differences of 30-50 s between the
variants of rounds 1-3 are therefore not reliable (verdict differences are more robust).
Only runs with the prefixes `c-` and `h-` should be used for conclusions about time.

Variants and ablations with the final jar (all `h-`, compared with `h-base-current`):

| variant | ITRS Y/K | ITRS time | JBC Y/K | JBC time | JBC-Rec Y/K | JBC-Rec time | total | vs. h-base-current |
|---|---|---|---|---|---|---|---|---|
| h-base-current | 36/4 | 266 | 23/8 | 444 | 27/2 | 348 | 1058 | |
| h-cur-enconce-fast6 | 36/4 | 248 | 23/8 | 446 | 26/3 | 373 | 1066 | -PartitionList |
| h-r3-irshead6 | 36/4 | 315 | 26/5 | 398 | 26/3 | 352 | 1065 | +Graph, Distances, juLinkedListCreateEquals; -PartitionList |
| h-r4-irsfasthead6 | 36/4 | 296 | 26/5 (+1 NO) | 436 | 26/3 | 377 | 1108 | same three (+moduloLower NO); -PartitionList |
| h-r4-irsslowhead6 | 36/4 | 244 | 24/7 | 487 | 25/3 | 424 | 1155 | +Distances; -AlternatingGrowReduceRec2, -PartitionList |
| h-abl-notemp | 35/5 | 287 | 22/9 | 478 | 24/5 | 386 | 1151 | -eratosthenes, AlternatingGrowReduceRec2, BinarySearch, PartitionList, juHashMapCreateIteratorKeyLoop |
| h-abl-nonormal | 33/7 | 350 | 24/6 | 429 | 25/4 | 354 | 1132 | +Graph; -A17, poly1, poly2, BinarySearch, PartitionList |
| h-abl-temprec | 36/4 | 281 | 23/8 | 460 | 26/3 | 380 | 1121 | -PartitionList |

- `r4-irsslowhead6`: `idpSlow` runs next to IRS during the head start. `r4-irsfasthead6`:
  `idpFast` runs next to IRS during the head start and the main loop has no `idpFast`
  stage of its own.
- Ablations of the current `idpv1`: `abl-notemp` without the temporary projections
  (`TempFilter`), `abl-nonormal` without the normal projections (`IDPtoIRS`,
  `IDPtoQDP[Ints=REMOVE]` at the top), `abl-temprec` continues after a temporary
  projection with the dependency graph and the full `idpv1` instead of `idpv1MainLoop`.

Conclusions:

- **Temporary and normal projections are both needed**; each ablation loses 5 files,
  and they are different files. Normal projections are all-or-nothing per SCC; temporary
  ones remove single nodes of an SCC and continue on the IDP, which is needed for SCCs
  whose cycles need different arguments. Example (one SCC; normal `IDPtoIRS` and
  `IDPtoQDP[Ints=REMOVE]` both give MAYBE, `IDPtoIRS[TempFilter]` followed by
  `IDPtoQDP[Ints=REMOVE]` proves it):

  ```
  f(i, xs) -> g(i, xs, xs)
  g(i, xs, cons(y, ys)) -> g(i, xs, ys)
  g(i, xs, nil) -> f(i - 1, xs) :|: i > 0
  ```

- Running the normal projections again after a temporary one (`abl-temprec`) does not pay
  off on these sets (no gain, 6% slower).
- **The 6 s IRS head start (`r3-irshead6`) is the best variant**: 3 more JBC files at the
  same total time (JBC faster, ITRS slower because NonInf-type files wait for IRS).
  `idpSlow` or `idpFast` next to IRS in the head start does not improve it.
- `cur-enconce-fast6` alone is neutral; its 4% gain in round 2 was an artifact of the
  leftover solvers.
- PartitionList.jar is at the 30 s border in all variants.

### Full-set validation (final jar 094bee3ece, 30 s), incomplete

`h-base-current` vs. `h-r3-irshead6`. The run was stopped by the system (low memory)
during `h-base-current` on JBC (106 of 222 done); `h-r3-irshead6` on JBC is missing.

| set | variant | YES | NO | MAYBE | KILLED | total |
|---|---|---|---|---|---|---|
| ITRS (117) | h-base-current | 105 | 0 | 0 | 12 | 771 |
| ITRS (117) | h-r3-irshead6 | 104 | 0 | 0 | 13 | 816 |
| JBC-Rec (143) | h-base-current | 89 | 41 | 6 | 7 | 1005 |
| JBC-Rec (143) | h-r3-irshead6 | 89 | 41 | 6 | 7 | 979 |

- ITRS: the head start loses a.10.itrs (YES in 4 s -> KILLED) and slows down A10 (6 -> 31 s),
  A04 (4 -> 18 s), countUpExp (3 -> 15 s), 10 (3 -> 10 s), log_RTA09 (4 -> 9 s): NonInf-type
  files where IRS runs without success. No file gets notably faster.
- JBC-Rec: identical verdicts, 3% faster.
- So the head start should not be used for ITRS. Idea: use it only for JBC
  (`jbcIDPv1 = AnyDelay(6000, Solve(IDPtoIRS:...), Any(Solve(IDPtoQDP[Ints=REMOVE]:...),
  idpv1MainLoop))`, `idpv1` unchanged for ITRS). Needs the JBC full-set comparison.

## Series m: one strategy, built up from the `aprove/main` `idpv1` (from 2026-10-12)

The user's direction: one `idpv1` for ITRS and JBC; take the `aprove/main` `idpv1` as the
reference instead of the current one; try the cheap methods (CONSTONLY, INTONLY) first;
then find the best place for the normal and the temporary projections. All runs with the
final jar (prefix `h-`), small sets, 30 s. With
`REST = First(Solve(Timer(12000, idpFast)), AnyDelay(5000, Solve(idpSlow), Solve(IDPtoQDP[Apply=ALWAYSFILTER]:...)))`:

- `m0-main`: `First(CONSTONLY:..., REST)` (the reference).
- `m1-intonly`: `First(CONSTONLY:..., AnyDelay(5000, Solve(IDPtoIRS[Apply=INTONLY]:...), REST))`.
- `m1c-intonly-commit`: `First(CONSTONLY:..., IDPtoIRS[Apply=INTONLY]:..., REST)` (commits to
  INTONLY if it applies).
- `m2-proj-early`: `m1` with `Any(Solve(IDPtoIRS:...), Solve(IDPtoQDP[Ints=REMOVE]:...), REST)`
  instead of `REST` (normal projections parallel to everything after the cheap stage).
- `m3-proj-late`: `m1` where the normal projections only run next to `idpSlow`, after the
  `idpFast` stage.

| run | ITRS Y/K | ITRS time | JBC Y/K | JBC time | JBC-Rec Y/K | JBC-Rec time | total | vs. m0-main |
|---|---|---|---|---|---|---|---|---|
| h-m0-main | 33/7 | 342 | 21/8 | 452 | 23/6 | 426 | 1220 | |
| h-m1-intonly | 36/4 | 243 | 21/9 | 495 | 24/5 | 381 | 1119 | +A17, poly1, poly2, MainFind |
| h-m1c-intonly-commit | 36/4 | 238 | 21/8 | 479 | 24/4 | 354 | 1071 | the same four |
| h-base-current (for orientation) | 36/4 | 266 | 23/8 | 444 | 27/2 | 348 | 1058 | +9 |

- INTONLY right after CONSTONLY gains 4 files and makes ITRS ~30% faster than the reference
  (also faster than the current `idpv1` on ITRS). Committing to it loses nothing here.
- `m2`/`m3` were not run: they contain a duplicate IRS attempt (INTONLY, then the full
  `IDPtoIRS` on the same IDP), which the series p below avoids.

How `IDPtoIRS` does depending on whether positions are removed (per IDP, from the `irs`-only
run of 10-09 on the small set; "nothing removed" approximates INTONLY):

| | conversions | IRS proved | IRS disproved (useless, fast) | open/timeout |
|---|---|---|---|---|
| ITRS, nothing removed | 33 | 22 (66%) | 8 | 3 |
| ITRS, positions removed | 8 | 2 (25%) | 6 | 0 |
| JBC, nothing removed | 42 | 35 (83%) | 3 | 4 |
| JBC, positions removed | 117 | 56 (47%) | 38 | 23 |

CONSTONLY applied to 15 sub-problems in the `qdp-constonly` run and proved 14 of them.

Code changes for the strategy (separate commits, jar 25bc35eba5, run prefix `k-`):

- `IDPtoIRS[Apply=NOTINTONLY]`: the complement of INTONLY, so that a strategy can treat
  the exact case separately without converting the same IDP to the same IRS twice.
- `IDPtoQDP[Ints=REMOVE]` fails if there is nothing to remove (the QDP would equal the
  ENCODE/CONSTONLY one).

### Series p: where to put the projections (small sets, 30 s, jar 25bc35eba5)

With `MAINREST = First(Solve(Timer(12000, idpFast)), AnyDelay(5000, Solve(idpSlow), Solve(IDPtoQDP[Apply=ALWAYSFILTER]:...)))`:

- `p1-t5` / `p1-t2` (head start for all projections, T1 = 5 s / 2 s):
  `idpv1 = AnyDelay(T1, Any(AnyDelay(5000, Solve(CONSTONLY), Solve(REMOVE)), Solve(IDPtoIRS)), MAINREST)`
- `p2` (head start only for the cheap conversions):
  `idpv1 = AnyDelay(5000, Solve(First(CONSTONLY, INTONLY)), Any(Solve(REMOVE), Solve(IDPtoIRS[Apply=NOTINTONLY]), MAINREST))`
- `p2c`: like `p2`, but committing: `idpv1 = First(CONSTONLY, INTONLY, Any(...))`

| run | ITRS Y/K | ITRS time | JBC Y/K | JBC time | JBC-Rec Y/K | JBC-Rec time | total | solved |
|---|---|---|---|---|---|---|---|---|
| h-m0-main | 33/7 | 342 | 21/8 | 452 | 23/6 | 426 | 1220 | 80 |
| h-m1c-intonly-commit | 36/4 | 238 | 21/8 | 479 | 24/4 | 354 | 1071 | 84 |
| k-p1-t5 | 36/4 | 275 | 23/8 | 478 | 26/3 | 361 | 1115 | 88 |
| k-p1-t2 | 36/4 | 247 | 22/9 | 478 | 26/2 | 365 | 1090 | 87 |
| k-p2 | 36/4 | 243 | 22/9 | 477 | 26/3 | 374 | 1094 | 87 |
| k-p2c | 36/4 | 235 | 22/8 | 443 | 26/2 | 327 | 1005 | 87 |
| h-base-current | 36/4 | 266 | 23/8 | 444 | 27/2 | 348 | 1058 | 89 |

- All p variants prove A17, poly1, poly2, BinarySearch, MainFind, Matrix, TaylorSeriesIte in
  addition to the reference; `p1-t5` also juLinkedListCreateEquals.
- `p2c` (committing to CONSTONLY/INTONLY, then REMOVE and `IDPtoIRS[Apply=NOTINTONLY]`
  parallel to the `aprove/main` rest) is the fastest variant so far: 5% faster than the
  current `idpv1`, 18% faster than the reference. Committing saves ~90 s against `p2`.
- Missing compared with the current `idpv1`: PartitionList, juHashMapCreateIteratorKeyLoop
  (both need the temporary projections).

How long do successful cheap proofs take? Per file 2-6 s wall time (incl. ~1 s JVM and the
front end) for all 61 INTONLY and 14 CONSTONLY proofs in the stored runs; the processor
times in the winning proofs are below 0.3 s. One outlier: MinusUserDefined.jar, 28.6 s
(nested `CaseAnalysis` in the IRS backend behind its 5 s / 7.5 s timers), proved by no
other technique in any run. So if the cheap stage should not commit forever, letting the
rest join after ~10 s is safe (`p2-t10`).

### Series q: temporary projections on top of `p2c` (small sets, 30 s)

All continue with `idpv1` after a temporary projection (so the cheap stage is retried),
and the temporary IRS projection uses `Apply=NOTINTONLY`.

- `q-A`: next to the normal projections: `idpv1Rest = Any(REMOVE, IRS, tempREMOVE, tempIRS, MAINREST)`.
- `q-B`: next to `idpSlow`, after the `idpFast` stage.
- `q-C`: as fallback of the normal projection: `First(Solve(Timer(8000, normal)), Solve(temporary))`.
- `q-D`: temporary projections first, the normal ones next to `idpSlow`.
- `p2-t10`: `p2` with the rest joining after 10 s instead of 5 s (no temporary projections).

(results follow)

## Status and next steps (2026-10-12, evening; superseded by the last section of this file)

Strategy series (one `idpv1` for ITRS and JBC, built up from `aprove/main`): cheap stage
and normal projections are measured (series m and p); `p2c` is the best so far.

The workspace is now in the repository (`bench/strategy-eval/`, see its `README.md`),
including the small input set and the `results.csv` of all runs. The jars and the full
outputs are not in git.

**Batch with jar 8ee98d809f (prefix `t-`, all crash fixes of 10-12; laptop, mains power):**
`t-m0-main`, `t-p2c`, `t-p2`, `t-p2-t10`, `t-q-A` are done on `small`; the queue was stopped
after `q-A` because the user had to leave. First look (106 files, 30 s; not analysed file
by file yet):

| Variant | Solved (YES+NO) | itrs Y/K | jbc Y/N/M/K | jbcrec Y/N/M/K | Total time |
|---|---|---|---|---|---|
| `t-m0-main` (the `aprove/main` `idpv1`) | 83 | 33/7 | 21/0/4/8 | 23/3/1/6 | 1280 s |
| `t-p2c` (cheap stage commits) | 91 | 36/4 | 22/1/2/8 | 26/3/2/2 | 1053 s |
| `t-p2` (cheap stage, 5 s head start) | 90 | 36/4 | 22/0/2/9 | 26/3/1/3 | 1131 s |
| `t-p2-t10` (late join at 10 s) | 90 | 36/4 | 22/0/2/9 | 26/3/1/3 | 1114 s |
| `t-q-A` (first temporary-projection variant) | 89 | 36/4 | 23/0/3/7 | 27/3/2/1 | 1094 s |

So far `p2c` is still the best in solved files and time; the late join does not pay off;
`q-A` gains two files over `p2c` and loses one (it has the same 86 YES but not the one JBC
NO that only `p2c` finds; `JBCNonTerm` verdicts are timing-dependent, see below). Which
files differ has not been looked at
(`python3 compare.py small --ref t-p2c --diff t-m0-main t-p2c t-p2 t-p2-t10 t-q-A`).

**Still to run:** `q-B q-C q-D base-current`.

- On the laptop (same machine as the `t-` runs, mains power only; check
  `ps -eo comm | grep -c minisat` = 0 and about 7 GB of free memory first). The jar is not
  in git; rebuild it from commit 8ee98d809f or from the tip (same sources) as
  `jars/aprove-8ee98d809f.jar`:

      cd bench/strategy-eval && JAR=jars/aprove-8ee98d809f.jar PREFIX=t- ./queue.sh small q-B q-C q-D base-current

- On another machine the laptop times are not comparable, so run the whole batch again
  with a new prefix (see "Resuming on another machine" in `bench/strategy-eval/README.md`):

      cd bench/strategy-eval && JAR=jars/aprove-<commit>.jar PREFIX=d- JOBS=<n> ./queue.sh small m0-main p2c p2 p2-t10 q-A q-B q-C q-D base-current

Then: compare (`compare.py small --ref <prefix>p2c --diff ...`, `matrix.py`), choose the
structure (cheap stage commit `p2c` vs. late join `p2-t10`; placement of the temporary
projections `q-*`), validate the choice on the full sets (`itrs-full`, `jbcrec-full`,
`jbc-full`; the JBC full validation was never finished), and put it into `current.strategy`
(only after asking the user).

Open from the review of the fixes (10-12): `ConstraintComparator` still ignores the kind of
a `Predicate` (`>` vs. `>=`, also origRule/uLeft/uRight) and compares function symbols by
hash code, so it can still return 0 for constraints that are not duplicates. Planned: a
small separate commit that compares the kind and the symbols themselves, then the ITRS
regression with `idpSlow` only (117 files, 15 s).

`IDPNonInf` fixes done on battery (commits on `idp-clean2`; contained in jar 8ee98d809f, not
in the jars measured so far):

- `PfUndefinedInt: Make the symbol unary`: the "arbitrary constant" feature of `IDPNonInf`
  was broken (arity 0 vs. unary use). ackTen.itrs is now proved by `idpSlow` in 2 s
  (KILLED in all runs before).
- `ConstraintComparator: Fix renaming of variables`: fixes "Quantors are not empty"
  (minsort, A15; A15 is still KILLED) **and a soundness bug that is also on `aprove/main`**:
  the comparator used for removing duplicate constraints identified constraints that are
  not renamings of each other (separate renaming per element of a constraint set, not
  injective, conflicts on the same variable ignored), so `reduce` dropped real constraints.
  Counterexample (`bench/strategy-eval/nonterm_disjunction.itrs`, non-terminating for r <= 0):
  `f(q, r) -> f(q + 1, r) :|: q <= 0 || r <= 0` got YES with every jar and strategy before
  the fix (also with the `aprove/main` `idpv1`), MAYBE after. On practical3.itrs, 17 real
  constraints were dropped this way (the file is KILLED anyway).
- Regression checks with `idpSlow` only: 18 NonInf-type ITRS files after the first two
  fixes, and all 117 ITRS files (15 s) before/after the comparator fix: verdicts unchanged
  (100 YES, 17 KILLED).

Further crash fixes on 10-12 (separate commits):

- `IdpCand1ShapeHeuristic: Handle unknown symbols`: `NullPointerException` for TRUE/FALSE
  in IDPs without booleans (incList.itrs).
- `IRChangeInformations: Fix iterator for array changes` (JBC front end): the iterator
  returned null for local array changes, so building the termination graph failed and
  AProVE answered MAYBE after ~4 s. Now BubbleSortR.jar (4 s), MergeSort.jar (9 s),
  Sudoku.jar (21 s) and MysteriousProgram.jar (14 s) are proved; Nim.jar and Gauss.jar reach
  the analysis but time out.
- `YicesEngine: Read values continued in the next line`: aborted
  `RankingReductionPairProcessor` on MysteriousProgram.jar and
  juLinkedListCreateLastIndexOf.jar.

- `AbstractFloat: Fix equals and hashCode` (JBC front end): both used the implementation of
  `Object`, so copies of the same float literal were never equal. This was the
  `AssertionError` in `State.addAbstractVariable` on juHashMapCreateEquals.jar and
  juHashMapCreatePutAll.jar (float constant 0.75, the load factor of `HashMap`). Both now
  reach the analysis; Equals got YES once in 45 s with 8 cores, both are KILLED at 60 s with
  4 cores. The other 15 benchmark files using floats or hash collections: verdicts unchanged.

Looked at and left alone:

- `AssertionError` in `IDPGPoloSolver.solve`: a developer check after a solution failed
  validation; without it the processor is just unsuccessful, so no proof is lost.
- `OutOfMemoryError` in the QDP KBO search: resource limit.

Other open points:

- JBC full-set validation was never finished (stopped for memory at file 106 of 222).
- All jars measured so far are older than the crash fixes of 10-12. Since the JBC front end
  fix changes which files reach `idpv1` at all, the baselines on the JBC sets have to be
  re-run with a new jar before comparing strategies there.
- `JBCNonTerm` finds the NO for Velroyen08-moduloLower.jar only sometimes (timing).

## Batch `d-` (desktop, 2026-10-12): all variants on `small`

Machine: AMD Ryzen 9 7950X (16 cores / 32 threads, SMT siblings are `i` and `i+16`), 61 GB RAM.
`JOBS=4 CORES=4 MEM=3g`: jobs are pinned to CPUs 0-15, so no two files share a physical core.
Jar `jars/aprove-852e64a802.jar` (tip `852e64a`, includes all crash fixes of 10-12). 106 files, 30 s.
Times are not comparable with the laptop (`t-`) runs; verdicts are.

| Variant | Solved | YES | NO | MAYBE | KILLED | Total time |
|---|---|---|---|---|---|---|
| `d-m0-main` | 82 | 79 | 3 | 5 | 18 (+1 ERROR) | 866 s |
| `d-p2c` | 89 | 86 | 3 | 5 | 12 | 609 s |
| `d-p2` | 89 | 86 | 3 | 3 | 14 | 685 s |
| `d-p2-t10` | 90 | 87 | 3 | 3 | 13 | 650 s |
| `d-q-A` | 92 | 89 | 3 | 5 | 9 | 554 s |
| `d-q-B` | 92 | 89 | 3 | 5 | 9 | 558 s |
| `d-q-C` | 92 | 89 | 3 | 5 | 9 | 537 s |
| `d-q-D` | 92 | 89 | 3 | 5 | 9 | 530 s |
| `d-base-current` | 92 | 88 | 4 | 3 | 11 | 629 s |

Per-file differences (`compare.py --ref d-p2c`, `matrix.py`):

- `m0-main` vs. `p2c`: `p2c` gains 8 files (A17, poly1, poly2, BinarySearch, Norm, Matrix,
  TaylorSeriesIte, juLinkedListCreateEquals) and loses only `choice.itrs` (m0 proves it in
  25 s; it is KILLED in every other variant, including `base-current`). Cheap stage first is
  clearly better. `choice.itrs` is a regression of the whole p/q family, not looked at yet.
- `p2c` vs. `p2`: same verdicts, `p2c` 76 s faster. The 5 s head start does not pay.
- `p2-t10` vs. `p2c`: +1 file (MinusUserDefined.jar, 17 s, KILLED in everything else), 40 s
  slower. A late join helps one file and costs time elsewhere.
- `q-A`, `q-B`, `q-C`, `q-D`: identical verdicts, +3 YES over `p2c`: PartitionList.jar,
  juHashMapCreateIteratorKeyLoop.jar (4 s in all q), juHashMapCreateHashCode.jar (10-23 s).
  Nothing lost. The temporary projections are what helps; their placement does not change
  verdicts. Time differences (530-558 s) are 5% and mostly come from which of the 9 K files
  hit 30 s vs. 45 s kills; treat as noise.
- `base-current` (current.strategy as in the tree): 92 solved as well, but a different set:
  it finds the NO of Velroyen08-moduloLower.jar and misses juHashMapCreateHashCode.jar;
  Velroyen08-doubleNeg.jar is KILLED (45 s) there.

Observation, not resolved: Velroyen08-moduloLower.jar. In `base-current` `JBCNonTerm` finds
the NO at the termination graph in 9 ms (0.7 s total). In `p2c`/`q-*` the answer is MAYBE
after 1.7 s, although the proof tree contains an `IntTRSPeriodicNontermProof` NO node below
the `SCCToIDPv1Proof` (SOUND) step; a NO below a SOUND-only step does not imply NO for the
program, so MAYBE is not wrong, but it means the `JBCNonTerm` branch of `jbcGraph` did not
deliver in time. Whether the early end of the cheap path cancels it needs a look.

Conclusions:

1. Cheap stage as a commit (`p2c`), not a head start or late join.
2. Add the four temporary projections (`q-*`); `q-A` is the smallest change (just two more
   entries in `idpv1Rest`), `q-D` is nominally fastest. No evidence on `small` to separate them.
3. Late join (`p2-t10`): not recommended.

Proposed final strategy: `q-A` (or `q-D`), then validate on the full sets (`itrs-full`,
`jbcrec-full`, `jbc-full`): at least `q-A` vs. `q-D` vs. `base-current`, and `m0-main` as
reference on `itrs-full` for `choice.itrs`-like regressions. Not done yet; `current.strategy`
is unchanged.

## Full-set validation `d-` (desktop, 2026-10-12): `q-A`, `q-D`, `base-current`

Same jar (`852e64a802`) and 30 s timeout, but `JOBS=8 CORES=4 MEM=5g` (all 32 threads, so files
share physical cores through SMT; slower per file than the `small` batch, comparable between
these three runs only). Inputs: `itrs-full` 117, `jbcrec-full` 143, `jbc-full` 222 (the 300 JBC
files minus the 78 NO files of the old baseline, hence no NO there).

| Set | Variant | YES | NO | MAYBE | KILLED | Time |
|---|---|---|---|---|---|---|
| itrs-full | `q-A` | 106 | 0 | 1 | 10 | 457 s |
| | `q-D` | 106 | 0 | 1 | 10 | 456 s |
| | `base-current` | 106 | 0 | 0 | 11 | 534 s |
| jbcrec-full | `q-A` | 93 | 41 | 2 | 7 | 652 s |
| | `q-D` | 94 | 41 | 2 | 6 | 613 s |
| | `base-current` | 94 | 41 | 1 | 7 | 646 s |
| jbc-full | `q-A` | 201 | 0 | 5 | 16 | 1176 s |
| | `q-D` | 202 | 0 | 5 | 15 | 1145 s |
| | `base-current` | 199 | 0 | 2 | 21 | 1316 s |

Files with different verdicts (all others identical in all three runs):

- itrs: practical3.itrs: `q-*` MAYBE after 2 s, `base-current` KILLED.
- jbcrec: Norm.jar: YES in `q-D` (19 s) and `base-current` (16 s), KILLED in `q-A`.
  EvenOdd.jar: `q-*` MAYBE after 2.5 s, `base-current` KILLED.
- jbc: Distances.jar, Graph.jar: YES only in `q-D` (17 s, 24 s), KILLED in the others.
  MinusUserDefined.jar: YES only in `q-A` (10 s). juHashMapCreateHashCode.jar: YES in `q-A`,
  `q-D` (21-22 s), KILLED in `base-current`. Velroyen08-doubleNeg/gcd/lcm.jar: `q-*` MAYBE
  after 2-3 s, `base-current` KILLED.

Conclusions:

- No YES/NO flip anywhere; the 41 NO of jbcrec-full are identical in all three runs. No
  soundness alarm.
- Both `q-*` are better than `base-current`: -13% time on itrs, -3..6% on jbcrec, -13% on jbc,
  and fewer KILLED (10/6-7/15-16 vs. 11/7/21). The only file `base-current` solves and `q-*`
  do not is none; `q-*` gain juHashMapCreateHashCode.jar (and Norm.jar for `q-D`).
- `q-D` vs. `q-A`: `q-D` is slightly ahead (+1 jbcrec, +1 jbc, 4-6% faster), but the
  differences are single files with 17-45 s times, i.e. at the edge of the timeout under load
  (Norm, Distances, Graph, MinusUserDefined flip with timing). Not a real separation.
- The 5 files where `q-*` answer MAYBE within 3 s and `base-current` runs until killed
  (practical3, EvenOdd, Velroyen08-doubleNeg/gcd/lcm) were not solved by `base-current`
  either at 30 s. Not checked whether `base-current` would solve them with a longer timeout.

Recommendation: `q-D` for `current.strategy` (fastest, at least as many solved on every
set). Waiting for the user's decision; `current.strategy` unchanged, nothing committed.

Applied 2026-10-12: `q-D` is now `idpv1`/`idpv1Rest` in `current.strategy` (not committed). `idpv1MainLoop` is kept (no longer referenced by `idpv1`, only by itself).

## Placement check `e-` (desktop, 2026-10-12): is `q-D` the right structure?

Question: are the temporary projections too prominent, and are the normal projections too late
(in `q-D` they only start after `idpFast` failed, up to 12 s in)? Full sets, same jar, 30 s,
`JOBS=8 MEM=5g`; `q-A` and `q-D` repeated to measure run-to-run noise.

- `q-E`: normal projections at once; temporary ones only in the slow group (with `idpSlow`).
- `q-G`: normal projections at once; temporary ones join after 2 s (`AnyDelay(2000, main path, temp)`).

| Set | `q-A` | `q-D` | `q-E` | `q-G` | (earlier `d-q-A` / `d-q-D`) |
|---|---|---|---|---|---|
| itrs-full YES/K | 106/10 | 106/10 | 106/10 | 106/10 | 106/10, 106/10 |
| jbcrec-full YES/K (NO 41 everywhere) | 94/6 | 95/5 | 95/5 | 95/5 | 93/7, 94/6 |
| jbc-full YES/K/M | 202/15/5 | 202/15/5 | 199/18/5 | 200/16/6 | 201/16/5, 202/15/5 |
| jbc-full time | 1147 s | 1143 s | 1237 s | 1218 s | 1176 s, 1145 s |

Findings:

- Noise: itrs identical; `q-D` reproduces (jbc 202/15/5, 1143 vs. 1145 s). On jbcrec the
  single files Norm.jar and MysteriousProgram.jar (10-20 s) flip between runs. Differences of
  one file there are noise.
- Later temporary projections cost: `q-E` and `q-G` lose Distances.jar and Graph.jar (YES at
  13-24 s with `q-D`), and `q-E` also juHashMapCreateHashCode.jar; 6-8% slower on jbc-full.
  So the temporary projections should stay early (prominent).
- Normal projections at once (`q-A`) vs. after `idpFast` (`q-D`): same on itrs and jbc counts;
  `q-D` solves Graph.jar in both runs where `q-A` is KILLED both times (the extra concurrent
  normal projections take CPU), `q-A` solves MinusUserDefined.jar (10 s) which `q-D` does not
  in any of its runs. No clear winner; `q-D` is marginally ahead. Late normal projections are
  not a problem on these sets.
- Not tested: dropping the normal projections entirely (the `p2c`-vs-`q-*` comparison on
  `small` suggests the temporary ones carry the gain), and different `Time=` (10 s) values of
  the temporary projections.

`current.strategy` stays on `q-D`.

## `Time=` of the temporary projections `f-` (desktop, 2026-10-12)

`q-D` with `Time=` of both temporary projections changed (`q-T3`, `q-T5`, `q-T20`; reference
`e-q-D` = 10000 ms). Full sets, same jar and settings as the `e-` batch.

| Set | 3 s | 5 s | 10 s (`q-D`) | 20 s |
|---|---|---|---|---|
| itrs-full YES/K | 106/10 | 106/10 | 106/10 | 106/10 |
| jbcrec-full YES/K | 95/5 | 94/6 | 95/5 | 94/6 |
| jbc-full YES/K/M | 203/14/5 | 203/14/5 | 202/15/5 | 202/14/6 |
| jbc-full time | 1143 s | 1184 s | 1143 s | 1157 s |

Only single timing-sensitive files differ: MysteriousProgram.jar (jbcrec, 10 s; flips between
identical runs), MinusUserDefined.jar (jbc; YES at 13/29 s with 3/5 s, KILLED with 10/20 s, but it
also flipped between the two `q-A` runs and the two `q-D` runs before) and MultiLasso.jar (MAYBE
once at 20 s). No evidence for a better value than 10000; 3000 is not worse. Keep `Time=10000`.

## 60 s run of the final strategy `g-` (desktop, 2026-10-12)

`final` (= `q-D` = new `current.strategy`), 60 s timeout, `JOBS=4 CORES=4 MEM=12g`, jar
`852e64a802`. (A first try with no `-Xmx` was stopped after 40 s: 8 JVMs grew to 9-11 GB RSS
each, free memory < 1 GB and 20 GB swap; `MEM=none` is therefore not usable with many files in
parallel, see the README.) Different job count and heap than the 30 s runs, so only verdicts are
compared, with `e-q-D` (30 s).

| Set | YES | NO | MAYBE | KILLED | 30 s `e-q-D` YES/K |
|---|---|---|---|---|---|
| itrs-full | 106 | 0 | 1 | 10 | 106/10 |
| jbcrec-full | 95 | 41 | 4 | 3 | 95/5 |
| jbc-full | 204 | 0 | 6 | 12 | 202/15 |

Changed files: jbc: MinusUserDefined.jar KILLED -> YES (17 s), juHashMapCreateEquals.jar
KILLED -> YES (32 s), juHashMapCreatePutAll.jar KILLED -> MAYBE (39 s); jbcrec: Domino.jar and
Nim.jar KILLED -> MAYBE (40/45 s). itrs unchanged: the 10 KILLED files (a.02, A15, choice,
collatz, Ex04, f91, A16, countUpNo, ...) do not finish within 60 s either. No verdict flips.
Doubling timeout and heap gains two files, so the remaining KILLED files are hard, not resource
problems.

## Status and next steps (2026-10-12, night)

**Done:** the strategy series is finished. The structure `q-D` is in `current.strategy` (commit
`current.strategy: Try cheap stage first in idpv1` on branch `idpv1-strategy`, directly on top of
upstream `7948abc`; the local commits `CLAUDE.md`, bench configs and this workspace are above it
as before). Summary of the evidence (all above in this file):

1. Cheap stage (`IDPtoQDP[Apply=CONSTONLY]`, `IDPtoIRS[Apply=INTONLY]`) as a commit (`First`):
   +8 files and -30% time vs. the `aprove/main` `idpv1` (`m0-main`) on `small`. A 5 s head start
   or a late join (`p2`, `p2-t10`) does not pay off.
2. Temporary projections early (in the same `Any` as `idpFast`/`idpSlow`): +3 files on `small`
   (PartitionList, juHashMapCreateIteratorKeyLoop, juHashMapCreateHashCode); moving them later
   (`q-E`, `q-G`) loses Distances.jar, Graph.jar and is 6-8% slower on jbc-full.
3. Normal projections at once (`q-A`) or after `idpFast` (`q-D`): no real difference; `q-D`
   chosen (marginally ahead, fastest). `Time=` of the temporary projections 3/5/10/20 s: no
   difference, kept 10000.
4. Full sets, 30 s: new strategy vs. old `idpv1`: itrs 106/106 YES but -15% time; jbcrec 95 vs.
   94 YES (41 NO both); jbc 202 vs. 199 YES, 15 vs. 21 KILLED, -13% time. No YES/NO flips.

**Branch and what to push:** `idpv1-strategy` (created from a detached HEAD). `git log
--oneline` should show, top to bottom: the commits with the results/docs of this session, the
workspace commit, bench configs, `CLAUDE.md`, `current.strategy: Try cheap stage first in
idpv1`, then upstream. Only the strategy commit is meant for upstream (PR); the commits above it
are local convenience. Push the branch, then on the notebook `git fetch && git checkout
idpv1-strategy`. The jars, `runs/*/out/` and `runs/*.log` are not in git (only `results.csv` and
`variant.txt` of every run are).

**Open (none blocks the strategy):**

- `choice.itrs` is proved by `m0-main` (25 s) but KILLED by every variant of the new family and
  by the old `current` (not looked at why; first check which technique proves it in `m0-main`).
- Velroyen08-moduloLower.jar: `JBCNonTerm` gives NO in 9 ms with the old strategy, the new one
  answers MAYBE after 1.7 s (the cheap path ends before `JBCNonTerm` delivers?). Also
  practical3.itrs, EvenOdd.jar, Velroyen08-doubleNeg/gcd/lcm.jar now give MAYBE after 2-3 s where
  the old strategy ran into the timeout; unknown whether the old one would solve them with more
  time.
- `idpv1MainLoop` is no longer used by `idpv1`; remove it (or keep for the old variants in
  `variants.sh`, which reference it).
- Follow-up for `ConstraintComparator` (it ignores the kind of a `Predicate` and compares function
  symbols by hash code; see the section above) and the ITRS regression with `idpSlow` only.
- Not tested: dropping the normal projections entirely.
- The JBC full-set validation is now done (jbc-full, 222 files without the 78 NO files, runs
  `d-`, `e-`, `f-`, `g-`); the JBC NO files were not re-run with the new strategy except
  jbcrec-full (41 NO unchanged).
- Prerequisite for any further comparison: only runs of the same machine, jar and settings; use
  `old-current` and `final` as references (the variant `base-current` now equals `final`).
