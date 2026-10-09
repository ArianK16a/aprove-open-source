# AProVE

Java 25 framework for automated termination and complexity analysis (RWTH Aachen). Input programs (TRS, ITRS/IDP, Java bytecode, C/LLVM, Haskell, Prolog, ...) are translated into an internal *problem*, which *processors* transform, decompose or solve under the control of a *strategy*, using SAT/SMT solvers as backends.

Upstream docs: https://github.com/aprove-developers/aprove-open-source/wiki (developer guide, code conventions).

## Build

Ant only, no Maven/Gradle. The `-f` flag is required because the file is not named `build.xml`.

```
ant -f build-aprove.xml compile    # incremental compile into build/ (the normal dev loop)
ant -f build-aprove.xml dist       # builds dist/lib/aprove.jar (runnable jar)
ant -f build-aprove.xml cleanAll   # wipe build/, gen/ and dist/
```

- `compile` also runs `settings`, which copies `src/aprove/GlobalSettings.template` to `src/aprove/GlobalSettings.java` if it is missing. That file is gitignored local config, so never commit it.
- Parsers are generated (SableCC/ANTLR) into `gen/`, which is gitignored. Edit the grammars, not the output. `regenerateGrammars` forces a rebuild.
- Sources are compiled with `encoding="ISO-8859-1"`, so avoid non-Latin-1 characters in `.java` files.
- Native Z3 libs (`libz3.so`, `libz3java.so`) live in `lib/`.

## Run

```
java -jar dist/lib/aprove.jar <input-file>      # CLI mode (default)
java -jar dist/lib/aprove.jar -u bat ...        # batch mode; also: srv, dio
```

`aprove.Main` picks the mode from `-u`; the real CLI is `aprove.cli.Main`. Sample inputs, grouped by TPDB category, are in `examples/` (e.g. `examples/ITRS_Innermost/*.itrs`).

## Tests

There is no unit test suite in the tree (JUnit/Mockito jars are on the module path but unused). Verify changes by compiling, then running the jar on files from `examples/` and checking the verdict (`YES`/`NO`/`MAYBE`/complexity bound) and the proof output. For larger regression runs use `bench/benchmark.py` with a TOML config (see `bench/example_configs/`). Benchmark inputs (TPDB) are not in the repo. Results go to `bench/result` and `bench/results`.

## Layout

```
src/aprove/
  Main.java, cli/, api/       entry points: CLI, batch, server, Java API
  input/                      frontends and parsers per input language
  strategies/                 strategy engine (UserStrategies, Annotations, Machine, Abortions)
  predefinedstrategies/       .strategy files; Auto/current.strategy is the main default
  prooftree/                  obligations, proofs, proof export (plain/HTML/LaTeX/CPF)
  solver/, runtime/           SAT/SMT solver glue and runtime support
  verification/
    dpframework/              main TRS/DP framework: TRSProblem, DPProblem (QDP), IDPProblem, JBCProblem, ...
    idpframework/             newer "IDPv2" implementation
    complexity/, confluence/, relative/, probabilistic/, theoremprover/, diophantine/, oldframework/
lib/                          third-party jars
bench/                        benchmark harness (Python, TOML configs, Dockerfile)
examples/                     sample inputs by category
```

## Core concepts and conventions

- **Problem**: a `BasicObligation` (e.g. `QDPProblem`, `IDPProblem`, `IRSProblem`).
- **Processor**: subclass of `Processor.ProcessorSkeleton` (for IDP: `IDPProcessor`, implementing `isIDPApplicable` and `processIDPProblem`). It returns a `Result` built through `ResultFactory`, such as `proved(newProblem, YNMImplication.SOUND, proof)`, `unsuccessful(...)`, or `provedWithNewStrategy(...)`. Each processor ships a `Proof` class (usually a `DefaultProof`) whose `export` prints the human-readable step.
- **Processors are instantiated per strategy use and may be reused**, so keep per-run state in locals, not instance fields.
- **Strategy parameters**: a processor declares `@ParamsViaArgumentObject` on its constructor and an `Arguments` class. Its fields and setters become the `[Name = Value]` parameters in `.strategy` files (e.g. `IDPtoQDP[Ints=REMOVE, TempFilter=True, Time=10000, Strategy="idpQDPRuleRemoval"]`). `std.strategy` maps strategy names to classes with `declare Name = class defaults [...]`, which also allows aliases with preset parameters. Renaming or removing a setter breaks the `.strategy` files that use it, so grep them (`grep -rn ProcessorName src/aprove/predefinedstrategies`).
- **Sub-strategies**: a processor can run a named strategy on a derived problem with `Machine.theMachine.startSubMachine(...)`. `IDPtoQDP` and `IDPtoIRS` do this in their `TempFilter` mode through the shared `IDPTemporaryFilter`/`IDPConversion` helpers, which map the remaining rules back to IDP nodes.
- **IDP pipeline**: `IDPProblem` is an integer rewrite problem (P/R rules plus a dependency graph with edge conditions). It is converted to a QDP by `IDPtoQDP`, either with a pos/neg encoding of integers (`Ints=ENCODE`, the default) or by removing integer positions (`Ints=REMOVE`, which also removes booleans since QDPs cannot express them). `IDPtoIRS` does the converse and removes non-integer positions to get an IRS (only for unbounded integers). `IDPtoIRS[Apply=INTONLY]` only applies if nothing but predefined symbols and variables occurs below the root of the P rules, so no nested term is abstracted to a fresh variable. `Apply=NOTINTONLY` is its complement. `IDPtoQDP[Ints=REMOVE]` fails if there is nothing to remove (the QDP would equal the `ENCODE` one). Both fail on IDPs that are not well-typed, e.g. with `f(Nil)` and `f(1)`.
- Wildcard imports (`import foo.bar.*;`) are the norm in this codebase. Match the surrounding file's style (4-space indent, `final` on locals and parameters, javadoc on classes).

## Git workflow

- Commit messages: imperative subject of at most 50 characters, capitalized, no trailing period, blank line, then a body explaining what and why. Prefix with the component when useful (`TerminationSCCToIDPv1Processor: ...`, `current.strategy: ...`).
- Keep unrelated fixes in separate commits.
- `main` is the primary branch. PRs use `.github/pull_request_template.md` (summary of what/why/how, testing notes).
- The working tree usually has untracked scratch files (`bench/arian.toml`, ad-hoc `examples/ITRS_Innermost/*.itrs`). Do not add or commit them unless asked.

## Benchmark setup (bench/)

Benchmarks run AProVE over a whole TPDB category in parallel via `bench/benchmark.py`, by default inside Docker.

**Inputs** live next to the repo, outside it:
- `../TPDB` (old TPDB layout): e.g. `Integer_TRS_Innermost` (ITRS, `.itrs`, category `Mixed_ITRS_2014`), `Java_Bytecode`, `TRS_Innermost`, ...
- `../TPDB-ARI` (ARI layout): `Java_Bytecode` (11 suites such as `Aprove_09`, `Costa_Julia_09`, `Java_Util`, 300 `.jar` files) and `Java_Bytecode_Recursive` (143 files), plus the other categories.
- `../TPDB-small`: quick regression subsets with the same layout (`Java_Bytecode` 39, `Java_Bytecode_Recursive` 25, `Integer_TRS_Innermost` 17 files). They were picked from earlier runs: files only solved by the newer IDP processors, regressions, unstable/unsolved files, NO examples as a soundness guard, and some stable YES files. Each subdir has an `expected.csv` (`File;Group;Expected;Time_ms`) from commit `3505feb` (ITRS: after switching ITRS to `idpv1`) run with the small configs (30s timeout); a small run takes about 40s per subdir. `../TPDB-small/compare.py <TPDB-small/Subdir> <outdir>` lists files whose verdict changed and exits 1 if one went from YES to NO or the other way round. See `../TPDB-small/README.md`.

**Configs**: `bench/example_configs/*.toml` are the upstream examples; `bench/arian_*.toml` are the local ones: full sets `arian_Java_Bytecode.toml`, `arian_Java_Bytecode_Recursive.toml`, `arian_ITRS_Innermost.toml` (10s timeout, comparable with the existing result folders), and small sets `arian_small_<Subdir>.toml` on `../TPDB-small` (30s timeout so timeouts don't decide the verdicts, output to `small-results/<Subdir>`). Keys: `FOLDER`, `SUBDIR`, `CATEGORY`, `TIMEOUT` (s), `IMAGE`, `OUTDIR`, `APROVE_JAR`, `EXTENSION`, `CORES_PER_FILE`. Defaults and the other options (`--local`, `-m` JVM heap, `-j` core budget) are in `parse_args`/`DEFAULTS` in `benchmark.py`. Per-category result handling is in `bench/handlers/` (`__default__.py` is the fallback). The CLI flags mirror the TOML keys.

**Docker image**: build once with `docker build . -t aprove:itrs`. It only provides the runtime. The AProVE under test is the host jar mounted in via `APROVE_JAR`, so the image normally must not be rebuilt; only rebuild the jar.

**Workflow to test a change**:
```
ant -f build-aprove.xml cleanAll   # optional but harmless
ant -f build-aprove.xml dist       # ~25s, produces dist/lib/aprove.jar
cd bench && python benchmark.py -c arian_small_Java_Bytecode.toml -o small-results/<variant>/Java_Bytecode
python3 ../../TPDB-small/compare.py ../../TPDB-small/Java_Bytecode small-results/<variant>/Java_Bytecode
python benchmark.py -c arian_Java_Bytecode.toml                 # full set, when the small set looks good
```
- Start with the small sets. Java_Bytecode_Recursive and ITRS are the smaller full sets. Both JBC and ITRS go through the `idpv1` strategy, so they exercise the IDP processors (`IDPtoIRS`, `IDPtoQDP`, temporary filters).
- To wait for a background benchmark, rely on the task completion notification. Don't poll with `pgrep -f benchmark.py`, because the polling shell's own command line matches the pattern.
- Run the benchmark in the background; it takes a long time (Java_Bytecode: 300 files, 10s timeout, 8 cores/file, so only 4 files in parallel). Its stdout is a carriage-return progress bar, so redirect it to a file and read only the tail (the final table), never the whole log.
- The run prints the jar's commit ID (`git rev-parse HEAD` at build time), so commit before benchmarking if the result should be attributable.
- The final table counts `YES`/`NO`/`MAYBE`/`KILLED`/`ERROR`. Baselines for commit `3505feb` (10s): Java_Bytecode YES 201, NO 78, MAYBE 5, KILLED 16; Java_Bytecode_Recursive YES 90, NO 41, MAYBE 6, KILLED 6; ITRS (`Mixed_ITRS_2014`, 117 files, 30s, `idpv1` strategy) YES 106, KILLED 11. Timing noise at 10s flips a few files between YES and KILLED from run to run. Only a switch between YES and NO is a real alarm.
- To compare runs file by file, read the first line of each `results/**/*.out` (the verdict, possibly prefixed by `KILLED`). Older result folders have no `summary.csv`.

**Outputs**: `OUTDIR` gets `summary.csv` (`File;Result;FullResult;InputPath;Time_ms`), `results/<suite>/<file>.out` with the full proof output, and `error.log`. `OUTDIR` is reused if it exists, so a rerun can overwrite earlier results. Use a fresh `OUTDIR` name per variant to keep them. Existing runs to compare against are kept in `bench/itrs-results/`, `bench/java-results/` and `bench/recursive-java-results/` (one folder per variant, e.g. `main-branch-idpv1`, `idpv1-removeterm`).
