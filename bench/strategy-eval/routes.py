#!/usr/bin/env python3
"""Classifies the proofs of a run by the processors used after the first IDP_v1 obligation."""
import csv, re, sys, collections
from pathlib import Path
d = Path(sys.argv[1])
rows = list(csv.DictReader((d / "results.csv").open(), delimiter=";"))
routes = collections.Counter(); ex = collections.defaultdict(list)
for r in rows:
    out = d / "out" / (r["File"].lstrip("./").replace("/", "__") + ".out")
    txt = out.read_text(errors="replace") if out.exists() else ""
    head = txt.split("\n\n----------------------------------------")[0]
    steps = re.findall(r"^\s*\(\d+\) (\w+?)(?:Proof|Processor)? \[", head, re.M)
    if r["Result"] != "YES":
        key = r["Result"]
    elif "IDP_v1" not in head:
        key = "no IDP (" + (steps[0] if steps else "?") + ")"
    else:
        tags = []
        for s in steps:
            s = s.replace("IDPtoIRS", "IDPRemoveTerm")  # former name
            for k in ["IDPRemoveTerm", "IDPRemoveInt", "IDPtoQDP", "IDPNonInf", "IDPTemporaryFilter", "IDPDependencyGraph", "IntTRS", "QDP", "PolynomialOrder", "RankingReductionPair"]:
                if s.startswith(k) and k not in tags: tags.append(k)
        key = "+".join(t for t in tags if t in ("IDPRemoveTerm", "IDPRemoveInt", "IDPtoQDP", "IDPNonInf", "IDPTemporaryFilter")) or "IDP graph only"
    routes[key] += 1; ex[key].append(Path(r["File"]).name)
for k, v in routes.most_common():
    print(f"{v:4} {k}: {' '.join(ex[k][:8])}{' ...' if len(ex[k]) > 8 else ''}")
