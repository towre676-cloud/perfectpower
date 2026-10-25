#!/usr/bin/env python3
"""Independent exact recount of the solved public Petersen planning cases.

Three independent methods are implemented here from scratch (stdlib only,
exact integer / Fraction arithmetic throughout):

  A. brute_force   -- Gray-code enumeration of all 2^n assignments.
  B. mitm_dict     -- meet-in-the-middle over a cost-tuple dictionary.
  C. collapse_dfs  -- recursive counting that collapses a whole subcube
                      when every remaining item fits in the remaining
                      capacities (also returns optimum and tie count).

Their results are compared against the repository's stated receipts in
receipts/planning/hybrid/benchmark.json (read, never written).  Optionally
(--repo-engine) the repository's own CompletionPlanner is also run for the
same cases and its summaries are compared as a fourth source.

Usage:  python3 recount_small_cases.py [--repo PATH] [--repo-engine]
Writes: recount_results.json next to this script.
"""
import argparse
import json
import sys
import time
from fractions import Fraction as Q
from math import lcm
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load_cases(repo):
    data = json.loads((repo / "data/planning/petersen.json").read_text())
    bench = json.loads((repo / "receipts/planning/hybrid/benchmark.json").read_text())
    stated = {}
    for case in bench["cases"]:
        if case["counting"]["status"] == "complete":
            stated[case["name"]] = case["counting"]["answers"]
    return {c["name"]: c for c in data}, stated


def spec_arrays(spec):
    caps = tuple(r["max"] for r in spec["resources"])
    lows = tuple(r.get("min", 0) for r in spec["resources"])
    costs = [tuple(v["costs"]) for v in spec["variables"]]
    profits = [Q(v["profit"]) for v in spec["variables"]]
    return lows, caps, costs, profits


def replay(point, lows, caps, costs, profits):
    used = [0] * len(caps)
    score = Q(0)
    for x, c, p in zip(point, costs, profits):
        if x:
            score += p
            for j in range(len(caps)):
                used[j] += c[j]
    feasible = all(lo <= u <= hi for lo, u, hi in zip(lows, used, caps))
    return feasible, score, used


# ---------------------------------------------------------------- method A
def brute_force(spec):
    lows, caps, costs, profits = spec_arrays(spec)
    n, m = len(costs), len(caps)
    scale = lcm(*(p.denominator for p in profits))
    units = [int(p * scale) for p in profits]
    used = [0] * m
    value = 0
    prev = 0
    count = 0
    best = None
    ties = 0
    best_mask = None
    feasible_points = []  # lex order (project_1 is the most significant bit)
    for i in range(1 << n):
        mask = i ^ (i >> 1)
        if i:
            changed = mask ^ prev
            j = n - changed.bit_length()
            sign = 1 if mask & changed else -1
            row = costs[j]
            for k in range(m):
                used[k] += sign * row[k]
            value += sign * units[j]
        prev = mask
        if all(lows[k] <= used[k] <= caps[k] for k in range(m)):
            count += 1
            point = [(mask >> (n - 1 - t)) & 1 for t in range(n)]
            feasible_points.append(point)
            if best is None or value > best:
                best, ties, best_mask = value, 1, mask
            elif value == best:
                ties += 1
        if count > 2_000_000:
            raise RuntimeError("brute force recording cap exceeded")
    point = [(best_mask >> (n - 1 - t)) & 1 for t in range(n)]
    # feasible_points was collected in Gray-code visit order; the planner's
    # rank is the position in mask order (project_1 = most significant bit).
    ranked = sorted(feasible_points,
                    key=lambda p: sum(x << (n - 1 - t) for t, x in enumerate(p)))
    return {"count": count, "maximum": str(Q(best, scale)), "maximizer_count": ties,
            "point": point, "points": ranked}


# ---------------------------------------------------------------- method B
def enumerate_half(costs, profits_scaled, lows, caps, idxs):
    """dict cost-tuple -> [count, best, ties] over subsets of idxs (feasible)."""
    m = len(caps)
    table = {(0,) * m: [1, 0, 1]}
    for i in idxs:
        c, p = costs[i], profits_scaled[i]
        additions = {}
        for key, (cnt, b, t) in table.items():
            nk = tuple(key[j] + c[j] for j in range(m))
            if all(lows[j] <= nk[j] <= caps[j] for j in range(m)):
                if nk in additions:
                    a = additions[nk]
                    a[0] += cnt
                    nb = b + p
                    if nb > a[1]:
                        a[1], a[2] = nb, t
                    elif nb == a[1]:
                        a[2] += t
                else:
                    additions[nk] = [cnt, b + p, t]
        for nk, a in additions.items():
            if nk in table:
                cur = table[nk]
                cur[0] += a[0]
                if a[1] > cur[1]:
                    cur[1], cur[2] = a[1], a[2]
                elif a[1] == cur[1]:
                    cur[2] += a[2]
            else:
                table[nk] = a
    return table


def mitm_dict(spec):
    lows, caps, costs, profits = spec_arrays(spec)
    n, m = len(costs), len(caps)
    scale = lcm(*(p.denominator for p in profits))
    units = [int(p * scale) for p in profits]
    half = n // 2
    right = enumerate_half(costs, units, (0,) * m, caps, range(half, n))
    left = enumerate_half(costs, units, (0,) * m, caps, range(0, half))
    right_items = list(right.items())
    count = 0
    best = None
    ties = 0
    for lk, (lc, lb, lt) in left.items():
        rem = tuple(caps[j] - lk[j] for j in range(m))
        for rk, (rc, rb, rt) in right_items:
            if all(rk[j] <= rem[j] for j in range(m)):
                count += lc * rc
                tot = lb + rb
                if best is None or tot > best:
                    best, ties = tot, lt * rt
                elif tot == best:
                    ties += lt * rt
    return {"count": count, "maximum": str(Q(best, scale)), "maximizer_count": ties}


# ---------------------------------------------------------------- method C
def collapse_dfs(spec, node_cap=400_000_000):
    """Recursive count/optimum/ties. Items are reordered internally by
    decreasing normalised cost; the returned point is in original order."""
    lows, caps, costs, profits = spec_arrays(spec)
    assert all(lo == 0 for lo in lows), "collapse_dfs written for zero lower bounds"
    n, m = len(costs), len(caps)
    scale = lcm(*(p.denominator for p in profits))
    units = [int(p * scale) for p in profits]
    order = sorted(range(n), key=lambda i: -sum(costs[i][j] / caps[j] for j in range(m)))
    it = [costs[i] for i in order]
    iu = [units[i] for i in order]
    suff_cost = [[0] * m for _ in range(n + 1)]
    suff_pos = [0] * (n + 1)       # sum of positive profits of items i..
    suff_pos_mask = [0] * (n + 1)  # reordered-coordinate mask of positive items i..
    for i in range(n - 1, -1, -1):
        for j in range(m):
            suff_cost[i][j] = suff_cost[i + 1][j] + it[i][j]
        suff_pos[i] = suff_pos[i + 1] + (iu[i] if iu[i] > 0 else 0)
        suff_pos_mask[i] = suff_pos_mask[i + 1] | ((1 << (n - 1 - i)) if iu[i] > 0 else 0)
    nodes = 0

    def dfs(i, cur, cur_mask):
        nonlocal nodes
        nodes += 1
        if nodes > node_cap:
            raise RuntimeError("collapse_dfs node cap exceeded")
        s = suff_cost[i]
        for j in range(m):
            if cur[j] + s[j] > caps[j]:
                break
        else:
            # every completion is feasible: 2^(n-i) of them; the best adds
            # exactly the positive-profit remaining items (profits here are
            # all positive, so the maximiser is unique within the subcube).
            return (1 << (n - i)), suff_pos[i], 1, cur_mask | suff_pos_mask[i]
        if i == n:
            return 1, 0, 1, cur_mask
        c = it[i]
        cnt0, b0, t0, mk0 = dfs(i + 1, cur, cur_mask)
        nxt = tuple(cur[j] + c[j] for j in range(m))
        for j in range(m):
            if nxt[j] > caps[j]:
                return cnt0, b0, t0, mk0
        cnt1, b1, t1, mk1 = dfs(i + 1, nxt, cur_mask | (1 << (n - 1 - i)))
        b1 += iu[i]
        if b1 > b0:
            return cnt0 + cnt1, b1, t1, mk1
        if b1 == b0:
            return cnt0 + cnt1, b0, t0 + t1, mk0
        return cnt0 + cnt1, b0, t0, mk0

    count, best, ties, mask = dfs(0, (0,) * m, 0)
    point_reordered = [(mask >> (n - 1 - t)) & 1 for t in range(n)]
    point = [0] * n
    for pos, orig in enumerate(order):
        point[orig] = point_reordered[pos]
    return {"count": count, "maximum": str(Q(best, scale)), "maximizer_count": ties,
            "point": point, "nodes": nodes}


def main():
    ap = argparse.ArgumentParser()
    # Default --repo is the repository root, when this script is run
    # from independent_checks/planning/ inside a checkout.
    ap.add_argument("--repo", default=str(HERE.parents[2]),
                    help="path to the (read-only) perfectpower checkout")
    ap.add_argument("--repo-engine", action="store_true")
    args = ap.parse_args()
    repo = Path(args.repo)
    cases, stated = load_cases(repo)
    results = {}
    plan = [("petersen_6", ["brute_force", "mitm_dict", "collapse_dfs"]),
            ("petersen_10", ["brute_force", "mitm_dict", "collapse_dfs"]),
            ("petersen_15", ["brute_force", "mitm_dict", "collapse_dfs"]),
            ("petersen_20", ["brute_force", "mitm_dict", "collapse_dfs"]),
            ("petersen_28", ["collapse_dfs"])]
    brute_points = {}
    for name, methods in plan:
        spec = cases[name]["specification"]
        entry = {"stated": {"count": stated[name]["count"],
                            "maximum": stated[name]["optimization"]["maximum"],
                            "maximizer_count": stated[name]["optimization"]["maximizer_count"],
                            "point": stated[name]["optimization"]["point"]},
                 "methods": {}}
        for meth in methods:
            t0 = time.time()
            if meth == "brute_force":
                r = brute_force(spec)
                brute_points[name] = r.pop("points")
            elif meth == "mitm_dict":
                r = mitm_dict(spec)
            else:
                r = collapse_dfs(spec)
            r["seconds"] = round(time.time() - t0, 3)
            ok = (r["count"] == entry["stated"]["count"]
                  and Q(r["maximum"]) == Q(entry["stated"]["maximum"])
                  and r["maximizer_count"] == entry["stated"]["maximizer_count"]
                  and ("point" not in r or r["point"] == entry["stated"]["point"]))
            r["agrees_with_receipt"] = ok
            entry["methods"][meth] = r
            print(f"{name} {meth}: count={r['count']} max={r['maximum']} "
                  f"ties={r['maximizer_count']} agree={ok} ({r['seconds']}s)", flush=True)
        # bank replay: the five receipt bank points must be feasible, their
        # lex ranks must match for brute-forced cases, profits <= optimum.
        lows, caps, costs, profits = spec_arrays(spec)
        bank_checks = []
        for b in stated[name]["bank"]:
            feas, score, _ = replay(b["point"], lows, caps, costs, profits)
            chk = {"rank_stated": b["rank"], "feasible": feas,
                   "profit": str(score), "profit_le_optimum": score <= Q(entry["stated"]["maximum"])}
            if name in brute_points:
                pts = brute_points[name]
                chk["rank_recomputed"] = pts.index(b["point"]) if b["point"] in pts else None
                chk["rank_agrees"] = chk["rank_recomputed"] == b["rank"] == b["reverse_rank"]
            bank_checks.append(chk)
        entry["bank_replay"] = bank_checks
        entry["bank_all_ok"] = all(c["feasible"] and c["profit_le_optimum"]
                                   and c.get("rank_agrees", True) for c in bank_checks)
        results[name] = entry

    # petersen_6 extra receipt: receipts/planning/petersen_6.json states
    # completions(prefix=[1]) = count 12, maximum 3300, maximizer_count 1.
    spec6 = cases["petersen_6"]["specification"]
    lows, caps, costs, profits = spec_arrays(spec6)
    cond = [p for p in brute_points["petersen_6"] if p[0] == 1]
    scores = [replay(p, lows, caps, costs, profits)[1] for p in cond]
    mx = max(scores)
    results["petersen_6_prefix_receipt"] = {
        "stated": {"count": 12, "maximum": "3300", "maximizer_count": 1},
        "recomputed": {"count": len(cond), "maximum": str(mx),
                       "maximizer_count": sum(1 for s in scores if s == mx)}}
    print("petersen_6 prefix[1]:", results["petersen_6_prefix_receipt"], flush=True)

    if args.repo_engine:
        sys.path.insert(0, str(repo / "python"))
        from perfectpower.planning import CompletionPlanner
        for name, _ in plan:
            t0 = time.time()
            s = CompletionPlanner(cases[name]["specification"]).summary()
            got = {"count": s["count"], "maximum": s["optimization"]["maximum"],
                   "maximizer_count": s["optimization"]["maximizer_count"],
                   "point": s["optimization"]["point"], "strategy": s["strategy"],
                   "seconds": round(time.time() - t0, 3)}
            got["agrees_with_receipt"] = (
                got["count"] == results[name]["stated"]["count"]
                and Q(got["maximum"]) == Q(results[name]["stated"]["maximum"])
                and got["maximizer_count"] == results[name]["stated"]["maximizer_count"]
                and got["point"] == results[name]["stated"]["point"])
            results[name]["repo_engine"] = got
            print(f"{name} repo_engine({got['strategy']}): count={got['count']} "
                  f"agree={got['agrees_with_receipt']} ({got['seconds']}s)", flush=True)

    out = HERE / "recount_results.json"
    out.write_text(json.dumps(results, indent=1))
    print("wrote", out.name)
    all_ok = all(all(m["agrees_with_receipt"] for m in e["methods"].values())
                 and e["bank_all_ok"] for e in results.values() if "methods" in e)
    print("ALL_AGREE" if all_ok else "MISMATCH_FOUND")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
