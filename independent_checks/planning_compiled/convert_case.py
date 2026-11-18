#!/usr/bin/env python3
"""Convert one case of the repository's data/planning/petersen.json to
the plain-text format read by petersen.c:

  line 1: n m
  line 2: caps[0] .. caps[m-1]
  next n lines: costs[i][0] .. costs[i][m-1]   (original variable order;
  the C program applies the branching order itself)

Usage: python3 convert_case.py REPO CASE_NAME OUT.txt
"""
import json
import sys
from pathlib import Path

repo, name, out = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3])
data = json.loads((repo / "data/planning/petersen.json").read_text())
case = [c for c in data if c["name"] == name][0]
spec = case["specification"]
caps = [r["max"] for r in spec["resources"]]
costs = [v["costs"] for v in spec["variables"]]
with out.open("w") as f:
    f.write(f"{len(costs)} {len(caps)}\n")
    f.write(" ".join(map(str, caps)) + "\n")
    for c in costs:
        f.write(" ".join(map(str, c)) + "\n")
print(f"wrote {out}: n={len(costs)} m={len(caps)} caps={caps}")
