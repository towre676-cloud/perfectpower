#!/usr/bin/env python3
"""Extra-budget probe (not part of the deliverable pipeline): reruns the
frontier refinement of attempt_50.py with 15,000,000 expansions to measure
how fast the count interval shrinks past the stated 3,000,000 budget."""
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from attempt_50 import frontier_interval

repo = HERE.parents[1]  # repository root
d = json.loads((repo / "data/planning/petersen.json").read_text())
spec = [c for c in d if c["name"] == "petersen_50"][0]["specification"]
caps = [r["max"] for r in spec["resources"]]
costs = [v["costs"] for v in spec["variables"]]
t0 = time.time()
fr = frontier_interval(caps, costs, (3, 4), 15_000_000, 1500)
print(fr)
print("width", fr["upper"] - fr["lower"],
      "relwidth", (fr["upper"] - fr["lower"]) / fr["lower"])
print("total wall", round(time.time() - t0, 1))
