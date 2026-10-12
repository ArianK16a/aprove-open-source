# IDPv1 strategy evaluation: workspace and how to resume

Goal: find the most efficient `idpv1` strategy in `current.strategy` (used for ITRS and JBC),
considering verdicts and runtime. The processor notes are in `IDP-strategies.txt`, the
measurements, conclusions and the current status in `IDP-strategy-results.md` (both in the
repository root; read the "Status and next steps" section at the end of the latter first).

## Layout

```
bench/strategy-eval/
  run.py                       runs one variant on a file list
  runvariant.sh VARIANT SET [timeout]   runs a variant from variants.sh (default 30 s)
  queue.sh SET VARIANT...      runs several variants one after another
  variants.sh                  all variants: NAME|def ;; def ...
  compare.py SET [--ref RUN] [--diff] [RUN...]   verdict/time summary per subset vs. a reference run
  matrix.py SET RUN...         per-file matrix (time if proved, . MAYBE, K KILLED)
  routes.py / jbcroutes.py RUNDIR       which techniques the proofs use (need runs/<run>/out)
  reparse.py RUNDIR            re-reads verdicts from outputs (only for old runs)
  sets/*.txt                   file lists (paths relative to bench/strategy-eval/)
  TPDB-small/                  the small input set (40 ITRS, 33 JBC, 33 JBC-Rec files)
  nonterm_disjunction.itrs     non-terminating ITRS that was proved terminating before the
                               ConstraintComparator fix (must not be YES)
  jars/                        frozen AProVE builds (not in git, see below)
  runs/<run>_<set>/            results.csv (File;Result;Time_s) and variant.txt are in git;
                               out/ (full output), strategy.strategy (the exact strategy used)
                               and runs/<run>_<set>.log (progress, last line = summary) are not
```

A run name is `<prefix><variant>`; the prefix tells the jar and the machine:

| Prefix | Jar (commit of the build) | Machine |
|---|---|---|
| none, `c-` | 703dcc09a0 (first) | laptop (8 cores) |
| `h-` | 094bee3ece (IRS fixes) | laptop |
| `k-` | 25bc35eba5 (adds `NOTINTONLY`, `Ints=REMOVE` fails if nothing is removed) | laptop |
| `t-` | 8ee98d809f (all crash fixes of 2026-10-12, same sources as the commit adding this workspace) | laptop |
| `d-` | `852e64a802` (= `t-` sources, built from the tip of 2026-10-12; its built-in `current.strategy` is still the old `idpv1`, the runs pass `-s`) | desktop (Ryzen 9 7950X, 16 cores/32 threads, 61 GB), `JOBS=4` for `small`, `JOBS=8 MEM=5g` for the `*-full` sets |
| `e-` | same jar | desktop, `JOBS=8 MEM=5g`, 30 s (placement check: `q-A q-D q-E q-G`) |
| `f-` | same jar | desktop, `JOBS=8 MEM=5g`, 30 s (`Time=` of the temporary projections: `q-T3 q-T5 q-T20`) |
| `g-` | same jar | desktop, `JOBS=4 MEM=12g`, **60 s** (`final` = the strategy now in `current.strategy`) |

The runs without prefix of rounds 1 to 3 and all `n-*` runs have unreliable times (orphaned
SAT solvers, see the results file); only `c-`, `h-`, `k-` and `t-` runs are clean. Times of
different machines or jars must not be compared with each other; verdicts can.

Input sets:

- `small` (106 files) = `itrs-small` (40) + `jbc-small` (33) + `jbcrec-small` (33), all in
  `TPDB-small/` here. How they were picked is described in the results file.
- `itrs-full` (117), `jbc-full` (222), `jbcrec-full` (143): need the TPDB next to the
  repository, `../TPDB/Integer_TRS_Innermost` (old layout) and
  `../TPDB-ARI/Java_Bytecode{,_Recursive}` (ARI layout), seen from the repository root.

## How a variant works

`run.py` copies `src/aprove/predefinedstrategies/Auto/current.strategy` of the working tree
and replaces whole top-level definitions (`name = ...` up to the next line starting in
column 0). Each definition in `variants.sh` is `name=expr` on one line, several are separated
by ` ;; `. Example:

```
flat|idpv1=First(...) ;; idpv1Loop=Any(...)
```

So do not edit `current.strategy` while a queue is running. Each file runs as

```
taskset -c <cores> java -ea -Xmx3g -jar <jar> -m wst -p plain -t 30 -s <variant strategy> FILE
```

with 2 files in parallel on 4 cores each by default; the verdict is the first line of
stdout, the time is the wall time including JVM start-up. Each run gets its own process
group that is killed afterwards, so that SAT solvers started by AProVE do not survive as
orphans.

Rules for comparable times:

- Nothing else CPU-heavy on the machine while measuring (no builds, no second queue).
- On a laptop only on mains power.
- Before starting: `ps -eo comm | grep -c minisat` must print 0 (never use `pkill -f` with a
  pattern that matches your own command line; `pkill -x minisat` is fine), and there must be
  enough free memory (`JOBS` x 3 GB heap plus about 1 GB).
- All runs that are compared must come from the same machine, jar and settings.

## Building a jar

```
ant -f build-aprove.xml dist
mkdir -p bench/strategy-eval/jars
cp dist/lib/aprove.jar bench/strategy-eval/jars/aprove-$(git rev-parse --short=10 HEAD).jar
```

Always measure a frozen copy in `jars/`, not `dist/lib/aprove.jar` (the default if `JAR` is
not set), which changes with the next build.

## Running

```
cd bench/strategy-eval
JAR=jars/aprove-<commit>.jar PREFIX=d- ./queue.sh small m0-main p2c p2      # several variants
JAR=jars/aprove-<commit>.jar PREFIX=d- ./runvariant.sh q-A small            # one variant
python3 compare.py small --ref d-p2c --diff d-m0-main d-p2c d-p2
python3 matrix.py small d-m0-main d-p2c d-p2
```

Optional environment for a stronger machine (`MEM=none` omits `-Xmx`; do not use it with many
parallel files: on the 61 GB desktop 8 JVMs grew to 9-11 GB RSS each within 40 s and the machine
started to swap. Use `MEM=<n>g` with JOBS x n below the RAM, e.g. `JOBS=4 MEM=12g`): `JOBS` (files in parallel, default 2), `CORES`
(cores per file, default 4; job i is pinned to cores i*CORES .. i*CORES+CORES-1), `MEM`
(heap per file, default `3g`). Keep `CORES=4` so that the results stay similar to the
earlier ones, and raise `JOBS` (e.g. `JOBS=4` on 16 cores).

A queue takes about 9 to 10 minutes per variant on `small` with `JOBS=2`. Run it in the
background and wait for it to finish; its progress is in `runs/<run>_small.log`.

## Variant names that changed meaning

- `base-current` has empty definitions, i.e. it is whatever `current.strategy` of the working tree
  is. Since 2026-10-12 that is the new `idpv1` (= `q-D` = `final`). The `d-old-current_*` runs
  (renamed from `d-base-current_*`) were measured with the old `idpv1` of `aprove/main`; the
  variant `old-current` reproduces it. Older prefixes (`h-`, `k-`, `t-`) `base-current` runs are
  the old one too.
- `final` has the explicit definitions of `q-D`, independent of the tree.
- `q-E`, `q-G` (placement of the projections), `q-T3`, `q-T5`, `q-T20` (`Time=` of the
  temporary projections) were added on 2026-10-12, see the results file.

## Resuming on another machine (state of 2026-10-12, evening)

The batch for the desktop is finished (prefixes `d-` to `g-`) and the winner (`q-D`) is in
`current.strategy` on the branch `idpv1-strategy`. Nothing has to be re-run to continue. To
re-measure something on the notebook, the jars are not in git, so build one first
(`ant -f build-aprove.xml dist`, copy to `jars/aprove-<commit>.jar`) and use a new prefix; times
of different machines must not be compared, so measure the reference variants (`old-current`,
`final`) there as well:

```
JAR=jars/aprove-<commit>.jar PREFIX=n2- JOBS=2 ./queue.sh small old-current final
python3 compare.py small --ref n2-final --diff n2-old-current n2-final
```

Note that a jar built from the branch already contains the new `idpv1` as default strategy, but
the runner always passes `-s` with the variant's strategy, so `old-current` still measures the
old one. See "Status and next steps" in `IDP-strategy-results.md` for what is open.
