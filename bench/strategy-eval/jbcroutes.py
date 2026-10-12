#!/usr/bin/env python3
"""Per file: which IDP techniques appear in the proof (all SCCs), with time."""
import csv, re, sys, collections
from pathlib import Path
d = Path(sys.argv[1])
rows = list(csv.DictReader((d / "results.csv").open(), delimiter=";"))
cnt = collections.Counter(); ex = collections.defaultdict(list)
for r in rows:
    out = d / "out" / (r["File"].lstrip("./").replace("/", "__") + ".out")
    head = out.read_text(errors="replace").split("\n\n----------------------------------------")[0] if out.exists() else ""
    steps = set(re.findall(r"^\s*\(\d+\) (\w+?) \[", head, re.M))
    tags = []
    for k, label in [("IDPtoIRS", "IRS"), ("IDPRemoveTerm", "IRS"), ("IDPRemoveInt", "RemoveInt"), ("IDPtoQDP", "QDP"), ("IDPNonInf", "NonInf"), ("IDPTemporaryFilter", "Temp"), ("JBCNonTerm", "JBCNonTerm"), ("SCCToIDPv1", "IDP")]:
        if any(s.startswith(k) for s in steps): tags.append(label)
    key = r["Result"] + " " + "+".join(tags)
    cnt[key] += 1; ex[key].append(f"{Path(r['File']).name}:{float(r['Time_s']):.0f}")
for k, v in cnt.most_common():
    print(f"{v:4} {k}: {' '.join(ex[k][:6])}{' ...' if len(ex[k]) > 6 else ''}")
