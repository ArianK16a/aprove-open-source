#!/usr/bin/env python3
"""Per-file matrix: time if the variant proves the file (YES/NO), '.' for MAYBE, 'K' for KILLED.

  matrix.py SET RUN...      (only files that at least one run proves are listed)
"""
import csv
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(run: str, set_: str) -> dict[str, tuple[str, float]]:
    with (HERE / "runs" / f"{run}_{set_}" / "results.csv").open() as f:
        return {r["File"]: (r["Result"], float(r["Time_s"])) for r in csv.DictReader(f, delimiter=";")}


def main() -> None:
    set_, runs = sys.argv[1], sys.argv[2:]
    data = {r: load(r, set_) for r in runs}
    files = sorted(set().union(*(d.keys() for d in data.values())))
    short = [r[:9] for r in runs]
    print(f"{'file':34}" + "".join(f"{s:>10}" for s in short))
    for f in files:
        cells = []
        solved = False
        for r in runs:
            res, t = data[r].get(f, ("?", 0))
            if res in ("YES", "NO"):
                cells.append(f"{res[0]}{t:.0f}")
                solved = True
            else:
                cells.append({"KILLED": "K", "MAYBE": "."}.get(res, "?"))
        if solved:
            name = Path(f).parent.name[:8] + "/" + Path(f).name
            print(f"{name[:34]:34}" + "".join(f"{c:>10}" for c in cells))


if __name__ == "__main__":
    main()
