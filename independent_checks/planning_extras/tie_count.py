#!/usr/bin/env python3
"""Exact maximiser (tie) counts for Petersen planning instances.

Wave one (attempt_50.py) PROVED the petersen_50 optimum 16537 by an
exhausted exact branch-and-bound but did not count how many feasible
points attain it.  This script counts ties exactly, for any case whose
optimum is already proved:

  * the bound machinery is copied from attempt_50.py's prove_optimum
    (same efficiency order, same per-resource fractional-knapsack
    tables, same Lagrangian prices: float coordinate descent proposes
    prices, they are snapped to nonnegative integers at scale 4096,
    and every pruning comparison is exact integer arithmetic -- any
    nonnegative prices give a valid bound by weak duality);
  * the search is re-aimed at a FIXED target OPT (the proved optimum):
      - a node is pruned iff val > OPT (can never come back down:
        all profits are positive), or val + bound < OPT (its subtree
        provably contains no optimal point);
      - a node with val == OPT contributes exactly one optimal point
        (the all-exclude completion; any further inclusion would
        exceed OPT since profits are positive) and is pruned;
      - every other node is branched, include-first.
    The search is exhausted (subject to the stated node/time budget,
    whose exhaustion is reported, in which case the count is a lower
    bound only and is labelled as such), so the tie count is exact,
    produced by enumeration -- no symmetry assumptions.

Validation (run before any new number is trusted): the counter must
reproduce maximiser_count = 1 on petersen_15, petersen_20 and
petersen_28, whose receipts state 1 and whose optima wave one's
recount reproduced independently.  petersen_10 is skipped here: its
profits are in tenths (published optimum 8706.1), outside this
integer-profit counter's stated scope.

Usage: python3 tie_count.py [--repo PATH] CASE [CASE ...]
Writes tie_count_results.json next to this script; per-case progress
is printed so a background run can be followed in its log.
"""
import argparse
import json
import sys
import time
from bisect import bisect_right
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
NODE_BUDGET = 400_000_000
TIME_BUDGET = 7200.0


def load_case(repo, name):
    data = json.loads((repo / "data/planning/petersen.json").read_text())
    case = [c for c in data if c["name"] == name][0]
    spec = case["specification"]
    caps = [r["max"] for r in spec["resources"]]
    costs = [v["costs"] for v in spec["variables"]]
    profits = []
    for v in spec["variables"]:
        q = Q(str(v["profit"]))
        assert q.denominator == 1, f"{name}: non-integer profit {v['profit']}"
        profits.append(int(q))
    return case, caps, costs, profits


def count_optima(caps, costs, profits, OPT, node_budget, time_budget,
                 label=""):
    """Exact number of feasible points with profit == OPT (OPT must
    be the proved optimum).  Returns a dict; 'exhausted' False means
    the budget stopped the search and 'tie_count' is a lower bound."""
    n, m = len(costs), len(caps)
    assert all(p > 0 for p in profits), "counter assumes positive profits"
    assert all(int(p) == p for p in profits), "integer profits required"
    profits = [int(p) for p in profits]
    order = sorted(range(n), key=lambda i: (-profits[i] / sum(
        costs[i][j] / caps[j] for j in range(m)), -profits[i]))
    it = [costs[i] for i in order]
    ip = [profits[i] for i in order]

    # per-depth, per-resource fractional-knapsack tables (as attempt_50)
    frac = []
    for i in range(n + 1):
        row = []
        suffix = list(range(i, n))
        for j in range(m):
            sfx = sorted(suffix, key=lambda t: (
                -(Q(ip[t], it[t][j])) if it[t][j] else float("-inf"), -ip[t]))
            cpref, ppref = [0], [0]
            items_j = []
            for t in sfx:
                cpref.append(cpref[-1] + it[t][j])
                ppref.append(ppref[-1] + ip[t])
                items_j.append((it[t][j], ip[t]))
            row.append((cpref, ppref, items_j))
        frac.append(row)

    def frac_bound(i, j, rem):
        cpref, ppref, items_j = frac[i][j]
        lo = bisect_right(cpref, rem) - 1
        add = ppref[lo]
        rem2 = rem - cpref[lo]
        if lo < len(items_j) and rem2 > 0:
            c, p = items_j[lo]
            if c == 0:
                add += p
            else:
                add += (rem2 * p) // c
        return add

    # Lagrangian prices, exactly as attempt_50 (float proposal, then
    # snapped to nonnegative integers at scale 4096; validity by weak
    # duality for ANY nonnegative prices).
    SCALE = 4096

    def dual_value(lam):
        return sum(lam[j] * caps[j] for j in range(m)) + sum(
            max(0.0, ip[t] - sum(lam[j] * it[t][j] for j in range(m)))
            for t in range(n))

    lam = [0.0] * m
    for _sweep in range(60):
        changed = False
        for j in range(m):
            cands = {0.0}
            for t in range(n):
                if it[t][j] > 0:
                    rest = ip[t] - sum(lam[l] * it[t][l]
                                       for l in range(m) if l != j)
                    v = rest / it[t][j]
                    if v >= 0:
                        cands.add(v)
            cur = dual_value(lam)
            best_v, best_f = lam[j], cur
            for v in cands:
                old = lam[j]
                lam[j] = v
                fv = dual_value(lam)
                lam[j] = old
                if fv < best_f - 1e-9:
                    best_f, best_v = fv, v
            if best_v != lam[j]:
                lam[j] = best_v
                changed = True
        if not changed:
            break
    LAM = [max(0, int(round(x * SCALE))) for x in lam]
    suffix_red = [0] * (n + 1)
    for t in range(n - 1, -1, -1):
        red = SCALE * ip[t] - sum(LAM[j] * it[t][j] for j in range(m))
        suffix_red[t] = suffix_red[t + 1] + (red if red > 0 else 0)
    root_lag_bound = (sum(LAM[j] * caps[j] for j in range(m))
                      + suffix_red[0]) // SCALE

    ties = 0
    nodes = 0
    exhausted = True
    t0 = time.time()
    stack = [(0, (0,) * m, 0)]
    while stack:
        i, used_t, val = stack.pop()
        nodes += 1
        if nodes % 1_000_000 == 0:
            el = time.time() - t0
            print(f"  [{label}] nodes={nodes} ties={ties} "
                  f"stack={len(stack)} elapsed={el:.1f}s", flush=True)
            if nodes > node_budget or el > time_budget:
                exhausted = False
                break
        if val > OPT:
            continue
        if val == OPT:
            ties += 1  # all-exclude completion; profits positive
            continue
        if i == n:
            continue
        room = [caps[j] - used_t[j] for j in range(m)]
        extra = (sum(LAM[j] * room[j] for j in range(m))
                 + suffix_red[i]) // SCALE
        if val + extra >= OPT:
            fextra = min(frac_bound(i, j, room[j]) for j in range(m))
            if fextra < extra:
                extra = fextra
        if val + extra < OPT:
            continue
        c = it[i]
        stack.append((i + 1, used_t, val))
        nxt = tuple(used_t[j] + c[j] for j in range(m))
        if all(nxt[j] <= caps[j] for j in range(m)):
            stack.append((i + 1, nxt, val + ip[i]))
    return {"optimum_target": OPT, "tie_count": ties, "nodes": nodes,
            "exhausted": exhausted,
            "seconds": round(time.time() - t0, 3),
            "root_lagrangian_bound": root_lag_bound,
            "lagrangian_prices_scaled_4096": LAM}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(HERE.parents[1]))  # default: repository root
    ap.add_argument("--budget-nodes", type=int, default=NODE_BUDGET)
    ap.add_argument("--budget-seconds", type=float, default=TIME_BUDGET)
    ap.add_argument("cases", nargs="+",
                    help="case names; OPT is taken from published_optimum "
                         "(must already be proved -- this script counts, "
                         "it does not prove optimality)")
    args = ap.parse_args()
    repo = Path(args.repo)
    out_path = HERE / "tie_count_results.json"
    results = {}
    if out_path.exists():
        results = json.loads(out_path.read_text())
    for name in args.cases:
        case, caps, costs, profits = load_case(repo, name)
        OPT = int(case["published_optimum"])
        print(f"=== {name}: counting points at OPT={OPT} ===", flush=True)
        r = count_optima(caps, costs, profits, OPT,
                         args.budget_nodes, args.budget_seconds, label=name)
        r["case"] = name
        results[name] = r
        print(f"{name}: tie_count={r['tie_count']} nodes={r['nodes']} "
              f"exhausted={r['exhausted']} ({r['seconds']}s)", flush=True)
        out_path.write_text(json.dumps(results, indent=1))
    print("wrote", out_path)


if __name__ == "__main__":
    sys.exit(main())
