#!/usr/bin/env python3
"""Bounded exact attempt on the unresolved petersen_50 full count.

The instance: 50 binary projects, 5 resources, caps (800, 650, 550, 550,
650), all profits positive integers, published optimum 16537.  The repo's
native MITM index supports at most 42 independent binary variables, so
the full feasible count is out of its reach.

What this script does, all in exact integer / Fraction arithmetic,
stdlib only:

  1. Cross-checks the two repo transcriptions of the instance agree.
  2. Replays the benchmark receipt's optimal point (feasibility, profit).
  3. PROVES the optimum independently with an exact branch-and-bound
     combining two exact bounds at every node: the minimum over
     resources of the fractional-knapsack bound (exact integer floors),
     and a Lagrangian bound from nonnegative resource prices found by
     floating-point coordinate descent at the root and then snapped to
     integers at scale 4096 -- every pruning comparison itself is exact
     integer arithmetic, and any nonnegative prices give a valid bound.
     The receipt point is *not* used as an incumbent; the incumbent is
     built by greedy heuristics, and optimality is certified by the
     exhausted search tree (node count reported).
  4. Computes EXACT subset-sum distributions for every single resource
     and every pair of resources (integer-encoded DP over all 2^50
     subsets).  From these, rigorous bounds on the feasible count:
       upper: min over pairs of #{subsets satisfying that pair},
       lower: union bound  2^50 - sum_j #{violating j},
       and the second Bonferroni truncation (reported even if weak).
  5. Refines the count interval by best-first frontier expansion:
     branch on all 50 projects (largest normalised cost first); every
     unexplored frontier node carries a rigorous interval
       [ pair_le - sum_{other resources} viol ,  min(single_le, pair_le) ]
     built from exact suffix distributions (per-resource prefix counts
     and a 2-resource prefix-sum grid for the tightest pair).  Nodes
     whose whole suffix fits are counted exactly (subcube collapse).

BUDGET (stated up front, as required): branch-and-bound at most
20,000,000 nodes / 1200 s; frontier expansion at most 3,000,000
expansions / 1200 s.  Actual usage is recorded in attempt50_results.json.
If the budget is exhausted -- as expected -- the output is a rigorous
interval for the count, never a heuristic point estimate dressed up as
an exact count.

Usage: python3 attempt_50.py [--repo PATH]
Writes attempt50_results.json next to this script and prints a summary.
"""
import argparse
from bisect import bisect_right
import heapq
import itertools
import json
import time
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
BB_NODE_BUDGET = 20_000_000
BB_TIME_BUDGET = 1200.0
FRONTIER_EXPANSION_BUDGET = 3_000_000
FRONTIER_TIME_BUDGET = 1200.0


def load(repo):
    data = json.loads((repo / "data/planning/petersen.json").read_text())
    case = [c for c in data if c["name"] == "petersen_50"][0]
    example = json.loads(
        (repo / "examples/planning/petersen_50_optimization.json").read_text())
    bench = json.loads(
        (repo / "receipts/planning/hybrid/benchmark.json").read_text())
    bench50 = [c for c in bench["cases"] if c["name"] == "petersen_50"][0]
    return case, example, bench50


# --------------------------------------------------------------------------
# exact branch-and-bound for the optimum
# --------------------------------------------------------------------------
def prove_optimum(caps, costs, profits):
    n, m = len(costs), len(caps)
    order = sorted(range(n), key=lambda i: (-profits[i] / sum(costs[i][j] / caps[j]
                                                             for j in range(m)),
                                            -profits[i]))
    it = [costs[i] for i in order]
    ip = [profits[i] for i in order]

    # greedy incumbents: efficiency order + per-resource ratio orders
    def greedy(ordr):
        used = [0] * m
        val = 0
        chosen = [0] * n
        for i in ordr:
            if all(used[j] + costs[i][j] <= caps[j] for j in range(m)):
                for j in range(m):
                    used[j] += costs[i][j]
                val += profits[i]
                chosen[i] = 1
        return val, chosen

    best_val, best_point = -1, None
    cand_orders = [order]
    for j in range(m):
        cand_orders.append(sorted(range(n), key=lambda i: (
            -(profits[i] / costs[i][j]) if costs[i][j] else float("-inf"),
            -profits[i])))
    for ordr in cand_orders:
        v, p = greedy(ordr)
        if v > best_val:
            best_val, best_point = v, p

    # per-depth, per-resource fractional-knapsack data: items i.. in
    # decreasing profit/cost_j order, with prefix sums.
    frac = []  # frac[i][j] = (cost_prefix, profit_prefix, tail_items)
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
        """Exact upper bound (integer floor) on extra profit from items
        i.. using only resource j with remaining capacity rem."""
        cpref, ppref, items_j = frac[i][j]
        lo = bisect_right(cpref, rem) - 1
        add = ppref[lo]
        rem2 = rem - cpref[lo]
        if lo < len(items_j) and rem2 > 0:
            c, p = items_j[lo]
            if c == 0:
                add += p  # zero-cost items sort first; defensive only
            else:
                add += (rem2 * p) // c  # floor: profits integral
        return add

    # Lagrangian prices: float coordinate descent at the root proposes
    # prices; they are then snapped to nonnegative integers at scale
    # SCALE and used only through exact integer arithmetic.  Any
    # nonnegative prices yield a valid bound (weak duality), so the
    # float phase can only affect speed, never correctness.
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
                    rest = ip[t] - sum(lam[l] * it[t][l] for l in range(m) if l != j)
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
    # suffix sums of reduced profits red_t = max(0, SCALE*p_t - LAM.cost_t)
    suffix_red = [0] * (n + 1)
    for t in range(n - 1, -1, -1):
        red = SCALE * ip[t] - sum(LAM[j] * it[t][j] for j in range(m))
        suffix_red[t] = suffix_red[t + 1] + (red if red > 0 else 0)
    root_lag_bound = (sum(LAM[j] * caps[j] for j in range(m))
                      + suffix_red[0]) // SCALE

    nodes = 0
    t0 = time.time()
    exhausted = True
    # explicit stack: (i, used tuple, value, chosen mask over ordered items)
    stack = [(0, (0,) * m, 0, 0)]
    best_mask_ord = 0
    # seed best from greedy over ordered items for mask bookkeeping
    gv, _ = greedy(order)
    # rebuild the greedy mask in ordered coordinates
    used = [0] * m
    gmask = 0
    for pos, i in enumerate(order):
        if all(used[j] + costs[i][j] <= caps[j] for j in range(m)):
            for j in range(m):
                used[j] += costs[i][j]
            gmask |= 1 << (n - 1 - pos)
    if gv == best_val:
        best_mask_ord = gmask
    while stack:
        i, used_t, val, mask = stack.pop()
        nodes += 1
        if nodes > BB_NODE_BUDGET or (nodes % 200000 == 0
                                      and time.time() - t0 > BB_TIME_BUDGET):
            exhausted = False
            stack.append((i, used_t, val, mask))
            break
        if val > best_val:
            best_val, best_mask_ord = val, mask
        if i == n:
            continue
        room = [caps[j] - used_t[j] for j in range(m)]
        # Lagrangian bound (exact integers), then fractional bounds.
        extra = (sum(LAM[j] * room[j] for j in range(m))
                 + suffix_red[i]) // SCALE
        if val + extra > best_val:
            fextra = min(frac_bound(i, j, room[j]) for j in range(m))
            if fextra < extra:
                extra = fextra
        if val + extra <= best_val:
            continue
        c = it[i]
        # exclude branch pushed first so include is explored first
        stack.append((i + 1, used_t, val, mask))
        nxt = tuple(used_t[j] + c[j] for j in range(m))
        if all(nxt[j] <= caps[j] for j in range(m)):
            stack.append((i + 1, nxt, val + ip[i], mask | (1 << (n - 1 - i))))
    point = [0] * n
    for pos, orig in enumerate(order):
        point[orig] = (best_mask_ord >> (n - 1 - pos)) & 1
    return {"optimum": best_val, "point": point, "nodes": nodes,
            "exhausted": exhausted, "seconds": round(time.time() - t0, 3),
            "greedy_seed": int(greedy(order)[0]),
            "root_lagrangian_bound": root_lag_bound,
            "lagrangian_prices_scaled_4096": LAM}


# --------------------------------------------------------------------------
# exact single / pair subset-sum distributions
# --------------------------------------------------------------------------
def distributions(caps, costs):
    n, m = len(costs), len(caps)
    totals = [sum(c[j] for c in costs) for j in range(m)]
    singles = []
    for j in range(m):
        states = {0: 1}
        for c in costs:
            a = c[j]
            if a == 0:
                states = {s: cnt * 2 for s, cnt in states.items()}
                continue
            new = dict(states)
            for s, cnt in states.items():
                ns = s + a
                new[ns] = new.get(ns, 0) + cnt
            states = new
        le = sum(cnt for s, cnt in states.items() if s <= caps[j])
        singles.append({"resource": j, "total_cost": totals[j],
                        "count_le_cap": le, "violations": (1 << n) - le,
                        "distinct_sums": len(states)})
    pairs = []
    for j, k in itertools.combinations(range(m), 2):
        W = totals[k] + 1
        states = {0: 1}
        for c in costs:
            add = c[j] * W + c[k]
            if add == 0:
                states = {s: cnt * 2 for s, cnt in states.items()}
                continue
            new = dict(states)
            for s, cnt in states.items():
                ns = s + add
                new[ns] = new.get(ns, 0) + cnt
            states = new
        le = inter = 0
        for s, cnt in states.items():
            a, b = divmod(s, W)
            if a <= caps[j] and b <= caps[k]:
                le += cnt
            if a > caps[j] and b > caps[k]:
                inter += cnt
        pairs.append({"resources": [j, k], "count_le_both": le,
                      "both_violations": inter, "distinct_sums": len(states)})
    return singles, pairs


# --------------------------------------------------------------------------
# frontier interval refinement
# --------------------------------------------------------------------------
def frontier_interval(caps, costs, pair, expansions_budget, time_budget):
    """pair = the two resource indices used for the exact 2-resource
    suffix grid.  Branching order: decreasing normalised cost."""
    n, m = len(costs), len(caps)
    order = sorted(range(n), key=lambda i: -sum(costs[i][j] / caps[j]
                                                for j in range(m)))
    it = [costs[i] for i in order]
    suff_tot = [[0] * m for _ in range(n + 1)]
    for i in range(n - 1, -1, -1):
        for j in range(m):
            suff_tot[i][j] = suff_tot[i + 1][j] + it[i][j]

    # per-resource suffix prefix-count arrays: pref[j][i][s] = number of
    # subsets of items i.. whose resource-j sum is <= s (s capped at cap).
    pref = []
    for j in range(m):
        cap = caps[j]
        dist = [0] * (cap + 2)
        dist[0] = 1
        per_i = [None] * (n + 1)
        run = 0
        arr = [0] * (cap + 1)
        for s in range(cap + 1):
            run += dist[s]
            arr[s] = run
        per_i[n] = arr
        for i in range(n - 1, -1, -1):
            a = it[i][j]
            ndist = dist[:]
            if a == 0:
                ndist = [x * 2 for x in dist]
            else:
                for s in range(cap + 1 - a):
                    if dist[s]:
                        ndist[s + a] += dist[s]
                # sums above cap are irrelevant for <=cap queries but the
                # empty/violating mass is recovered via 2^(n-i) - le.
            dist = ndist
            run = 0
            arr = [0] * (cap + 1)
            for s in range(cap + 1):
                run += dist[s]
                arr[s] = run
            per_i[i] = arr
        pref.append(per_i)

    def single_le(j, i, rem):
        if rem < 0:
            return 0
        if rem >= caps[j]:
            return pref[j][i][caps[j]]
        return pref[j][i][rem]

    # 2-resource suffix prefix-sum grids for the chosen pair.
    pj, pk = pair
    Tj = suff_tot[0][pj]
    Tk = suff_tot[0][pk]
    W = Tk + 1
    grids = [None] * (n + 1)
    dist = {0: 1}
    grids[n] = dist
    for i in range(n - 1, -1, -1):
        add = it[i][pj] * W + it[i][pk]
        nd = dict(dist)
        if add == 0:
            nd = {s: c * 2 for s, c in dist.items()}
        else:
            for s, cnt in dist.items():
                ns = s + add
                nd[ns] = nd.get(ns, 0) + cnt
        dist = nd
        grids[i] = dist
    # convert each dict to a 2D prefix-sum flat list, capped at the caps
    # (queries never exceed caps, so clamp coordinates there).
    CJ, CK = caps[pj], caps[pk]
    grid_ps = [None] * (n + 1)
    # Build exact capped grids: keep only a<=CJ and b<=CK mass (over-cap
    # subsets can never satisfy rem<=cap in that coordinate, so dropping
    # them is exact for every query this program makes).
    for i in range(n + 1):
        g = [0] * ((CJ + 1) * (CK + 1))
        for s, cnt in grids[i].items():
            a, b = divmod(s, W)
            if a <= CJ and b <= CK:
                g[a * (CK + 1) + b] += cnt
        for a in range(CJ + 1):
            base = a * (CK + 1)
            for b in range(1, CK + 1):
                g[base + b] += g[base + b - 1]
        for a in range(1, CJ + 1):
            base = a * (CK + 1)
            prev = (a - 1) * (CK + 1)
            for b in range(CK + 1):
                g[base + b] += g[prev + b]
        grid_ps[i] = g
    grids = None

    def pair_le(i, remj, remk):
        if remj < 0 or remk < 0:
            return 0
        a = min(remj, CJ)
        b = min(remk, CK)
        return grid_ps[i][a * (CK + 1) + b]

    def node_interval(i, used):
        """Rigorous [lo, hi] for completions of items i.. given used."""
        rem_items = n - i
        total = 1 << rem_items
        rems = [caps[j] - used[j] for j in range(m)]
        if any(r < 0 for r in rems):
            return (0, 0)
        if all(used[j] + suff_tot[i][j] <= caps[j] for j in range(m)):
            return (total, total)  # subcube collapse: exact
        hi = total
        for j in range(m):
            v = single_le(j, i, rems[j])
            if v < hi:
                hi = v
        ple = pair_le(i, rems[pj], rems[pk])
        if ple < hi:
            hi = ple
        lo = ple
        for j in range(m):
            if j in (pj, pk):
                continue
            lo -= total - single_le(j, i, rems[j])
            if lo < 0:
                lo = 0
                break
        if lo > hi:
            lo = hi
        return (lo, hi)

    t0 = time.time()
    lo0, hi0 = node_interval(0, (0,) * m)
    exact = 0
    heap = []  # (-width, counter, i, used, lo, hi)
    counter = itertools.count()
    if lo0 == hi0:
        exact = lo0
        flo = fhi = lo0
    else:
        heapq.heappush(heap, (-(hi0 - lo0), next(counter), 0, (0,) * m, lo0, hi0))
        flo, fhi = lo0, hi0
    expansions = 0
    while heap and expansions < expansions_budget:
        if expansions % 5000 == 0 and time.time() - t0 > time_budget:
            break
        negw, _, i, used, lo, hi = heapq.heappop(heap)
        flo -= lo
        fhi -= hi
        expansions += 1
        c = it[i]
        children = [(i + 1, used)]
        nxt = tuple(used[j] + c[j] for j in range(m))
        if all(nxt[j] <= caps[j] for j in range(m)):
            children.append((i + 1, nxt))
        else:
            # include-branch infeasible: the exclude child *is* the node.
            children = [(i + 1, used)]
        for ci, cused in children:
            if ci == n:
                exact += 1
                flo += 1
                fhi += 1
                continue
            clo, chi = node_interval(ci, cused)
            if clo == chi:
                exact += clo
                flo += clo
                fhi += chi
            else:
                heapq.heappush(heap, (-(chi - clo), next(counter), ci, cused, clo, chi))
                flo += clo
                fhi += chi
    return {"exact_counted": exact, "lower": flo, "upper": fhi,
            "expansions": expansions, "frontier_nodes": len(heap),
            "seconds": round(time.time() - t0, 3),
            "root_interval": [lo0, hi0], "pair_used": list(pair),
            "completed": not heap}


def main():
    ap = argparse.ArgumentParser()
    # Default --repo is the repository root, when this script is run
    # from independent_checks/planning/ inside a checkout.
    ap.add_argument("--repo", default=str(HERE.parents[1]))  # repository root
    args = ap.parse_args()
    repo = Path(args.repo)
    case, example, bench50 = load(repo)
    spec = case["specification"]
    caps = [r["max"] for r in spec["resources"]]
    costs = [v["costs"] for v in spec["variables"]]
    profits = [int(v["profit"]) for v in spec["variables"]]
    n = len(costs)
    results = {"instance": {"n": n, "caps": caps,
                            "published_optimum": case["published_optimum"]}}

    results["spec_crosscheck"] = {
        "data_vs_example_identical": example["specification"] == spec}
    rp = bench50["native_optimization"]["point"]
    used = [sum(x * c[j] for x, c in zip(rp, costs)) for j in range(len(caps))]
    results["receipt_point_replay"] = {
        "feasible": all(u <= caps[j] for j, u in enumerate(used)),
        "profit": sum(x * p for x, p in zip(rp, profits)),
        "used": used}
    print("spec crosscheck:", results["spec_crosscheck"], flush=True)
    print("receipt point replay:", results["receipt_point_replay"], flush=True)

    t0 = time.time()
    opt = prove_optimum(caps, costs, profits)
    opt["agrees_with_published"] = (opt["optimum"] == int(case["published_optimum"])
                                    and opt["exhausted"])
    results["optimization_proof"] = opt
    print(f"B&B optimum={opt['optimum']} nodes={opt['nodes']} "
          f"exhausted={opt['exhausted']} ({opt['seconds']}s)", flush=True)

    t0 = time.time()
    singles, pairs = distributions(caps, costs)
    total_subsets = 1 << n
    s1 = sum(s["violations"] for s in singles)
    s2 = sum(p["both_violations"] for p in pairs)
    best_pair = min(pairs, key=lambda p: p["count_le_both"])
    results["resource_distributions"] = {
        "singles": singles, "pairs": pairs,
        "seconds": round(time.time() - t0, 3),
        "union_lower_bound": total_subsets - s1,
        "bonferroni2_upper_bound": total_subsets - s1 + s2,
        "best_pair_upper_bound": best_pair["count_le_both"],
        "best_pair": best_pair["resources"],
        "total_subsets": total_subsets}
    print(f"distributions ({results['resource_distributions']['seconds']}s): "
          f"union lower={total_subsets - s1}, best pair upper="
          f"{best_pair['count_le_both']} pair={best_pair['resources']}, "
          f"bonferroni2 upper={total_subsets - s1 + s2}", flush=True)

    fr = frontier_interval(caps, costs, tuple(best_pair["resources"]),
                           FRONTIER_EXPANSION_BUDGET, FRONTIER_TIME_BUDGET)
    results["frontier_refinement"] = fr
    print(f"frontier: expansions={fr['expansions']} frontier={fr['frontier_nodes']} "
          f"interval=[{fr['lower']}, {fr['upper']}] ({fr['seconds']}s)", flush=True)

    lo = max(results["resource_distributions"]["union_lower_bound"], fr["lower"])
    hi = min(results["resource_distributions"]["best_pair_upper_bound"], fr["upper"])
    results["final_count_interval"] = {"lower": lo, "upper": hi,
                                       "exact_count": None,
                                       "status": "open_within_stated_budget"}
    out = HERE / "attempt50_results.json"
    out.write_text(json.dumps(results, indent=1))
    print("FINAL INTERVAL", lo, hi, flush=True)
    print("wrote", out.name)


if __name__ == "__main__":
    main()
