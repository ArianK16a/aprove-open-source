#!/usr/bin/env python3
"""Summarises runs on a set: verdicts and times per subset, and differences to a reference.

  compare.py SET [--ref RUN] [RUN...]     (runs default to all runs/*_SET)
"""
import argparse
import csv
from pathlib import Path

HERE = Path(__file__).resolve().parent


def subset(path: str) -> str:
    if "Integer_TRS" in path:
        return "itrs"
    if "Java_Bytecode_Recursive" in path:
        return "jbcrec"
    return "jbc"


def load(run: Path) -> dict[str, tuple[str, float]]:
    with (run / "results.csv").open() as f:
        return {r["File"]: (r["Result"], float(r["Time_s"])) for r in csv.DictReader(f, delimiter=";")}


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("set")
    p.add_argument("runs", nargs="*")
    p.add_argument("--ref", default="base-current")
    p.add_argument("--diff", action="store_true", help="list the files that differ from the reference")
    args = p.parse_args()
    names = args.runs or sorted(d.name[: -len(args.set) - 1] for d in (HERE / "runs").glob(f"*_{args.set}") if (d / "results.csv").exists())
    ref = load(HERE / "runs" / f"{args.ref}_{args.set}")
    subsets = sorted({subset(f) for f in ref})
    header = f"{'variant':22}" + "".join(f" | {s:^31}" for s in subsets) + " | +YES -YES"
    print(header)
    print(f"{'':22}" + "".join(f" | {'Y':>3} {'N':>3} {'M':>3} {'K':>3} {'time':>6} {'tYES':>6}" for _ in subsets))
    for name in names:
        res = load(HERE / "runs" / f"{name}_{args.set}")
        line = f"{name:22}"
        for s in subsets:
            rows = [v for f, v in res.items() if subset(f) == s]
            c = {k: sum(1 for r, _ in rows if r == k) for k in ("YES", "NO", "MAYBE", "KILLED")}
            t = sum(t for _, t in rows)
            ty = sum(t for r, t in rows if r == "YES")
            line += f" | {c['YES']:>3} {c['NO']:>3} {c['MAYBE']:>3} {c['KILLED']:>3} {t:>6.0f} {ty:>6.0f}"
        gained = [f for f, (r, _) in res.items() if r in ("YES", "NO") and ref.get(f, ("", 0))[0] not in ("YES", "NO")]
        lost = [f for f, (r, _) in res.items() if r not in ("YES", "NO") and ref.get(f, ("", 0))[0] in ("YES", "NO")]
        conflict = [f for f, (r, _) in res.items() if {r, ref.get(f, ("", 0))[0]} == {"YES", "NO"}]
        line += f" | {len(gained):>4} {len(lost):>4}" + (f"  CONFLICT {conflict}" if conflict else "")
        print(line)
        if args.diff and (gained or lost):
            print("      + " + " ".join(Path(f).name for f in gained))
            print("      - " + " ".join(Path(f).name for f in lost))


if __name__ == "__main__":
    main()
