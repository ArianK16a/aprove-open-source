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

Optional environment for a stronger machine: `JOBS` (files in parallel, default 2), `CORES`
(cores per file, default 4; job i is pinned to cores i*CORES .. i*CORES+CORES-1), `MEM`
(heap per file, default `3g`). Keep `CORES=4` so that the results stay similar to the
earlier ones, and raise `JOBS` (e.g. `JOBS=4` on 16 cores).

A queue takes about 9 to 10 minutes per variant on `small` with `JOBS=2`. Run it in the
background and wait for it to finish; its progress is in `runs/<run>_small.log`.

## Resuming on another machine

The times measured on the laptop cannot be compared with a new machine, so the references
have to be measured again there. With a jar of the current tip and a new prefix (`d-`):

```
JAR=jars/aprove-<commit>.jar PREFIX=d- JOBS=<n> ./queue.sh small m0-main p2c p2 p2-t10 q-A q-B q-C q-D base-current
python3 compare.py small --ref d-p2c --diff d-m0-main d-p2c d-p2 d-p2-t10 d-q-A d-q-B d-q-C d-q-D d-base-current
```

Then follow "Status and next steps" in `IDP-strategy-results.md`. To try a new `idpv1` in
AProVE itself, copy the definitions of the winning variant from `variants.sh` (or from
`runs/<run>_small/strategy.strategy`) into `current.strategy`, but only after asking the user.
