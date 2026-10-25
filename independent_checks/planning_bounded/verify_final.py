#!/usr/bin/env python3
"""End-to-end audit of the final refined petersen_50 frontier state.

Streams the RAM heap pickle and every spill file, re-sums all node
bounds, and checks  exact + sum(lo) == floor  and
exact + sum(hi) == ceiling  against the spill manifest.  Also
re-counts one deep frontier node by plain distribution-free
recursion and checks it lies inside its stored bounds.
"""
import json
import pickle
from pathlib import Path

import bounded_count as bc
from refine import plain_count

HERE = Path(__file__).resolve().parent


def main():
    spill = HERE / "spill"
    man = json.loads((spill / "manifest.json").read_text())
    slo = shi = nodes = 0
    deepest = None
    files = [spill / "ram_heap.pkl"] + [spill / nm for nm in man["spill_files"]]
    for fp in files:
        with open(fp, "rb") as f:
            entries = pickle.load(f)
        for (negw, negi, used, lo, hi) in entries:
            slo += lo
            shi += hi
            nodes += 1
            if deepest is None or -negi > -deepest[1]:
                deepest = (negw, negi, used, lo, hi)
        print(f"{fp.name}: cumulative nodes={nodes} sum_lo={slo} sum_hi={shi}",
              flush=True)
    exact = man["exact"]
    ok_lo = exact + slo == man["floor"]
    ok_hi = exact + shi == man["ceiling"]
    print(f"accounting: exact+sum(lo)={exact+slo} floor={man['floor']} ok={ok_lo}")
    print(f"accounting: exact+sum(hi)={exact+shi} ceiling={man['ceiling']} ok={ok_hi}")
    print(f"nodes total={nodes} interval=[{man['floor']}, {man['ceiling']}] "
          f"width={man['ceiling']-man['floor']}")

    caps, costs = bc.load_case(HERE.parents[1], "petersen_50")  # repository root
    n, m = len(costs), len(caps)
    order = sorted(range(n), key=lambda i: -sum(costs[i][j] / caps[j] for j in range(m)))
    items = [tuple(costs[i]) for i in order]
    check = None
    if deepest is not None and n - (-deepest[1]) <= 22:
        _, negi, used, lo, hi = deepest
        val = plain_count(caps, items, -negi, used)
        check = {"depth": -negi, "stored_interval": [lo, hi],
                 "plain_recursion_count": val, "inside": lo <= val <= hi}
    print("deepest-node check:", check)
    out = {"nodes_total": nodes, "exact_constant": exact,
           "floor": man["floor"], "ceiling": man["ceiling"],
           "width": man["ceiling"] - man["floor"],
           "identity_lo_ok": ok_lo, "identity_hi_ok": ok_hi,
           "deepest_node_check": check}
    (HERE / "petersen_50_final_audit.json").write_text(json.dumps(out, indent=1))
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
