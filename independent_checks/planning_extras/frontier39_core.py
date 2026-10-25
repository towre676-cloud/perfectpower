#!/usr/bin/env python3
"""petersen_39 feasible-count closure attempt (30M-expansion budget).

The frontier_interval function below is copied VERBATIM from wave
one's attempt_50.py (same suffix distributions, same node intervals,
same best-first expansion, same subcube collapse) with exactly three
insertions, each marked by the strings rss_cap_kb / stopped_reason /
[frontier] progress prints:
  1. an optional RSS guard: if the process resident set exceeds
     rss_cap_kb at a 5,000-expansion checkpoint, expansion stops and
     the CURRENT rigorous interval is returned (flo/fhi are rigorous
     at every instant of the original algorithm);
  2. progress prints every progress_every expansions;
  3. stopped_reason / peak_rss_kb fields in the result dict.
Equivalence with the original is validated empirically in the driver
(petersen_28 must close identically under both implementations).

Driver: chooses the resource pair by wave one's criterion (the pair
minimising count_le_both in the exact distributions), validates on
petersen_28 (known count 208817578), then runs petersen_39 with
30,000,000 expansions / 5400 s / RSS cap 2,600,000 KB.
"""
import heapq
import itertools
import json
import time
from bisect import bisect_right
from pathlib import Path


def _rss_kb():
    try:
        return int(Path("/proc/self/statm").read_text().split()[1]) * 4
    except Exception:
        return 0


def frontier_interval(caps, costs, pair, expansions_budget, time_budget,
                      rss_cap_kb=None, progress_every=250000):
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
    stopped_reason = None
    peak_rss = _rss_kb()
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
        if expansions % 5000 == 0:
            r = _rss_kb()
            if r > peak_rss:
                peak_rss = r
            if rss_cap_kb is not None and r > rss_cap_kb:
                stopped_reason = "rss_guard"
                break
            if progress_every and expansions % progress_every == 0:
                print(f"    [frontier] expansions={expansions} "
                      f"frontier={len(heap)} interval=[{flo}, {fhi}] "
                      f"width={fhi - flo} rss={r} KB", flush=True)
            if time.time() - t0 > time_budget:
                stopped_reason = "time_budget"
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
            "completed": not heap and stopped_reason is None,
            "stopped_reason": stopped_reason, "peak_rss_kb": peak_rss}


# ---------------------------------------------------------------------------
# driver appended in frontier39.py (see file tail)
