#!/usr/bin/env python3
"""Run AProVE with a strategy variant on a list of files and record verdicts and times.

A variant is a copy of current.strategy in which top-level definitions are replaced:

  run.py --name irs-only --set 'idpv1=Solve(IDPRemoveTerm:RunDefaultStrategyForObligation)' \
         --files sets/itrs-small.txt -t 30

Each run is pinned to its own CPU subset (taskset) so that parallel runs do not
compete for cores. Results are appended to runs/<name>/results.csv
(File;Result;Time_s) and the full output is kept in runs/<name>/out/.
"""
import argparse
import concurrent.futures
import csv
import os
import re
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
BASE_STRATEGY = REPO / "src/aprove/predefinedstrategies/Auto/current.strategy"
VALID = {"YES", "NO", "MAYBE", "KILLED"}


def replace_definition(text: str, name: str, expr: str) -> str:
    """Replaces the top-level definition `name = ...` (up to the next line starting
    at column 0) by `name = expr`. Appends the definition if it does not exist."""
    lines = text.split("\n")
    start = None
    for i, line in enumerate(lines):
        if re.match(rf"^{re.escape(name)}\s*=", line):
            start = i
            break
    if start is None:
        return text + f"\n{name} = {expr}\n"
    end = start + 1
    while end < len(lines) and (lines[end] == "" or lines[end][0] in " \t"):
        end += 1
    # keep trailing blank lines
    while end > start + 1 and lines[end - 1] == "":
        end -= 1
    return "\n".join(lines[:start] + [f"{name} = {expr}"] + lines[end:])


def make_strategy(sets: list[str], path: Path) -> None:
    text = BASE_STRATEGY.read_text(encoding="latin-1")
    for s in sets:
        name, expr = s.split("=", 1)
        text = replace_definition(text, name.strip(), expr.strip())
    path.write_text(text, encoding="latin-1")


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--name", required=True)
    p.add_argument("--set", action="append", default=[], help="name=expr, replaces a top-level definition")
    p.add_argument("--strategy", type=Path, help="use this strategy file instead of generating one")
    p.add_argument("--files", type=Path, required=True, help="file with one input path per line")
    p.add_argument("-t", "--timeout", type=int, default=30)
    p.add_argument("--jar", type=Path, default=REPO / "dist/lib/aprove.jar")
    p.add_argument("-j", "--jobs", type=int, default=2)
    p.add_argument("--cores", type=int, default=4, help="cores per job")
    p.add_argument("--mem", default="3g")
    p.add_argument("--resume", action="store_true", help="skip files that already have a result")
    args = p.parse_args()

    rundir = HERE / "runs" / args.name
    (rundir / "out").mkdir(parents=True, exist_ok=True)
    strategy = args.strategy
    if strategy is None:
        strategy = rundir / "strategy.strategy"
        make_strategy(args.set, strategy)
    (rundir / "variant.txt").write_text("\n".join(args.set) + "\n")

    files = [Path(l.strip()) for l in args.files.read_text().splitlines() if l.strip() and not l.startswith("#")]
    csv_path = rundir / "results.csv"
    done = set()
    if args.resume and csv_path.exists():
        with csv_path.open() as f:
            done = {row["File"] for row in csv.DictReader(f, delimiter=";")}
    else:
        csv_path.write_text("File;Result;Time_s\n")
    files = [f for f in files if str(f) not in done]

    free_slots = list(range(args.jobs))
    slot_lock = threading.Lock()
    csv_lock = threading.Lock()

    def run_one(path: Path) -> tuple[str, str, float]:
        with slot_lock:
            slot = free_slots.pop()
        try:
            cpus = f"{slot * args.cores}-{slot * args.cores + args.cores - 1}"
            cmd = ["taskset", "-c", cpus, "java", "-ea", f"-Xmx{args.mem}", "-jar", str(args.jar),
                   "-m", "wst", "-p", "plain", "-t", str(args.timeout), "-s", str(strategy), str(path)]
            t0 = time.monotonic()
            # Own process group, so that solvers started by AProVE (minisat, yices, ...) can be
            # killed with it. Otherwise they survive as orphans and steal CPU from later runs.
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                    errors="replace", start_new_session=True)
            try:
                stdout, stderr = proc.communicate(timeout=args.timeout + 15)
                first = stdout.splitlines()[0].strip() if stdout.strip() else ""
                result = first if first in VALID else "ERROR"
            except subprocess.TimeoutExpired:
                result = "KILLED"
                stdout, stderr = "", ""
            finally:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            if result == "KILLED":
                stdout, stderr = proc.communicate()
            out = (stdout or "") + "\n===== stderr =====\n" + (stderr or "")
            elapsed = time.monotonic() - t0
            outname = str(path).lstrip("./").replace("/", "__")
            (rundir / "out" / f"{outname}.out").write_text(out)
            with csv_lock:
                with csv_path.open("a") as f:
                    f.write(f"{path};{result};{elapsed:.1f}\n")
            return str(path), result, elapsed
        finally:
            with slot_lock:
                free_slots.append(slot)

    counts: dict[str, int] = {}
    total = 0.0
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for i, (path, result, elapsed) in enumerate(ex.map(run_one, files), 1):
            counts[result] = counts.get(result, 0) + 1
            total += elapsed
            print(f"[{i}/{len(files)}] {result:6} {elapsed:6.1f}s {path}", flush=True)
    print(f"{args.name}: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) + f", total {total:.0f}s")


if __name__ == "__main__":
    main()
