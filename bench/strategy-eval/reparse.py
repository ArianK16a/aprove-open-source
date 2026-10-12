#!/usr/bin/env python3
"""Re-reads the verdicts of a run from its outputs (first line that is a verdict)."""
import csv, re, sys
from pathlib import Path
for run in sys.argv[1:]:
    d = Path(run); rows = list(csv.DictReader((d / "results.csv").open(), delimiter=";"))
    for r in rows:
        out = d / "out" / (r["File"].lstrip("./").replace("/", "__") + ".out")
        if r["Result"] == "ERROR" and out.exists():
            m = re.search(r"^(YES|NO|MAYBE|KILLED)$", out.read_text(errors="replace"), re.M)
            if m: r["Result"] = m.group(1)
    with (d / "results.csv").open("w") as f:
        f.write("File;Result;Time_s\n")
        for r in rows: f.write(f"{r['File']};{r['Result']};{r['Time_s']}\n")
