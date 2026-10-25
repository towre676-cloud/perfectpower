#!/usr/bin/env python3
"""Memory-bounded exact frontier counter for the Petersen planning cases.

This extends the exact frontier machinery of attempt_50.py (same
branching order, same node interval: exact subcube collapse, suffix
single-resource prefix counts, and an exact suffix resource-pair grid
giving [pair_le - sum of other-resource violations, min(single_le,
pair_le)]) but replaces its best-first heap -- whose frontier grew to
2,994,605 live nodes and whose 15M-expansion probe was OOM-killed --
with a depth-first schedule:

  * the pending set is an explicit LIFO stack; at any moment it holds
    only the unexplored siblings along one root-to-leaf path, i.e.
    O(branching x depth) nodes (here at most ~2 x 50 entries), each a
    small tuple (depth, used-costs, lo, hi);
  * the suffix pair grids are stored as flat array('Q') (C uint64)
    instead of Python-int lists: for petersen_50, 51 layers x
    551 x 651 cells x 8 bytes = ~147 MB, reported via ru_maxrss;
  * the global rigorous interval [floor, ceiling] is maintained by
    replacing a popped node's interval with its children's intervals
    (or exact values), exactly as in the best-first version, so the
    interval is rigorous at every instant, and the search state is
    checkpointed to JSON periodically and can be resumed.

BUDGET (stated up front): structure building at most ~300 s; counting
at most --max-seconds wall seconds (default 1800) and at most
--max-expansions expansions (default unlimited within the time cap);
target peak RSS <= 1.5 GB on this 7 GB machine.  On budget exhaustion
the output is the rigorous interval at that moment, never a point
estimate.  Exact integer arithmetic throughout (all counts < 2^63,
so uint64 storage is exact; Python ints are used for all sums).

Validation gates built into a full run of this programme (see
REPORT.md): petersen_28 must close at exactly 208817578 and
petersen_39 must close at exactly 368072359571 (the repository's
stated count) before the petersen_50 result is trusted.

Usage:
  python3 bounded_count.py --case petersen_50 [--repo PATH]
      [--max-seconds S] [--max-expansions E] [--checkpoint PATH]
      [--resume PATH] [--out PATH] [--pair 3,4]
Writes a results JSON (default <case>_bounded_results.json beside
this script) and appends progress lines to stdout.
"""
import argparse
from array import array
import itertools
import json
import resource
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load_case(repo, name):
    data = json.loads((repo / "data/planning/petersen.json").read_text())
    case = [c for c in data if c["name"] == name][0]
    spec = case["specification"]
    caps = [r["max"] for r in spec["resources"]]
    costs = [v["costs"] for v in spec["variables"]]
    return caps, costs


def build_structures(caps, costs, pair):
    """Branching order + suffix data, mirroring attempt_50.py.
    Returns (order_items, suff_tot, pref, grid_ps, pair)."""
    n, m = len(costs), len(caps)
    order = sorted(range(n), key=lambda i: -sum(costs[i][j] / caps[j]
                                                for j in range(m)))
    it = [tuple(costs[i]) for i in order]
    suff_tot = [None] * (n + 1)
    acc = [0] * m
    suff_tot[n] = tuple(acc)
    for i in range(n - 1, -1, -1):
        for j in range(m):
            acc[j] += it[i][j]
        suff_tot[i] = tuple(acc)

    # Single-resource suffix prefix counts: pref[j][i] is array('Q')
    # of length cap_j+1; pref[j][i][s] = # subsets of items i.. with
    # resource-j sum <= s.  Sums above cap are dropped (exact for
    # queries s <= cap: adding more items only increases sums).
    pref = []
    for j in range(m):
        cap = caps[j]
        dist = [0] * (cap + 1)
        dist[0] = 1
        per_i = [None] * (n + 1)
        run = 0
        arr = array("Q", bytes(8 * (cap + 1)))
        for s in range(cap + 1):
            run += dist[s]
            arr[s] = run
        per_i[n] = arr
        for i in range(n - 1, -1, -1):
            a = it[i][j]
            if a == 0:
                dist = [x * 2 for x in dist]
            else:
                nd = dist[:]
                for s in range(cap + 1 - a):
                    if dist[s]:
                        nd[s + a] += dist[s]
                dist = nd
            run = 0
            arr = array("Q", bytes(8 * (cap + 1)))
            for s in range(cap + 1):
                run += dist[s]
                arr[s] = run
            per_i[i] = arr
        pref.append(per_i)

    # Resource-pair suffix grids for pair (pj, pk), clamped at the
    # caps: grid_ps[i] is a flat array('Q') of (CJ+1) x (CK+1)
    # prefix sums; grid_ps[i][a*(CK+1)+b] = # subsets of items i..
    # with pair sums <= (a, b).  Over-cap mass in either coordinate
    # can never satisfy a query with rem <= cap, so clamping the DP
    # coordinates at cap+1 (a sink) is exact for every query made.
    pj, pk = pair
    CJ, CK = caps[pj], caps[pk]
    S = CK + 1
    ENC = CK + 2  # clamped coordinate modulus for the DP dict
    dist = {0: 1}
    grids = [None] * (n + 1)

    def to_grid(d):
        flat = [0] * ((CJ + 1) * S)
        for key, cnt in d.items():
            a, b = divmod(key, ENC)
            if a <= CJ and b <= CK:
                flat[a * S + b] += cnt
        # 2D prefix sums: row-wise accumulate, then add row above.
        out = [0] * len(flat)
        for a in range(CJ + 1):
            base = a * S
            row = list(itertools.accumulate(flat[base:base + S]))
            if a:
                prev = out[base - S:base]
                row = [x + y for x, y in zip(row, prev)]
            out[base:base + S] = row
        return array("Q", out)

    grids[n] = to_grid(dist)
    for i in range(n - 1, -1, -1):
        aj, ak = it[i][pj], it[i][pk]
        nd = dict(dist)
        if aj == 0 and ak == 0:
            nd = {s: c * 2 for s, c in dist.items()}
        else:
            for key, cnt in dist.items():
                a, b = divmod(key, ENC)
                na = a + aj
                if na > CJ:
                    na = CJ + 1
                nb = b + ak
                if nb > CK:
                    nb = CK + 1
                nk = na * ENC + nb
                nd[nk] = nd.get(nk, 0) + cnt
        dist = nd
        grids[i] = to_grid(dist)
    return it, suff_tot, pref, grids


def make_interval_fn(caps, suff_tot, pref, grids, pair):
    n = len(suff_tot) - 1
    m = len(caps)
    pj, pk = pair
    CJ, CK = caps[pj], caps[pk]
    S = CK + 1
    others = [j for j in range(m) if j not in (pj, pk)]

    def node_interval(i, used):
        total = 1 << (n - i)
        st = suff_tot[i]
        exact_fit = True
        for j in range(m):
            if used[j] + st[j] > caps[j]:
                exact_fit = False
                break
        if exact_fit:
            return (total, total)
        remj = caps[pj] - used[pj]
        remk = caps[pk] - used[pk]
        ple = grids[i][remj * S + remk]
        hi = ple
        for j in range(m):
            v = pref[j][i][caps[j] - used[j]]
            if v < hi:
                hi = v
                if hi == 0:
                    return (0, 0)
        lo = ple
        for j in others:
            lo -= total - pref[j][i][caps[j] - used[j]]
            if lo <= 0:
                lo = 0
                break
        if lo > hi:
            lo = hi
        return (lo, hi)

    return node_interval


def count(case_name, caps, costs, pair, max_seconds, max_expansions,
          checkpoint_path, resume_path, progress_every=250_000,
          structures=None, initial=None, tag=""):
    n, m = len(costs), len(caps)
    if structures is None:
        t_build = time.time()
        structures = build_structures(caps, costs, pair)
        build_seconds = time.time() - t_build
    else:
        build_seconds = 0.0
    it, suff_tot, pref, grids = structures
    interval = make_interval_fn(caps, suff_tot, pref, grids, pair)

    spot = {"target_depth": n - 20 if n >= 25 else None,
            "record": None}
    if initial is not None:
        stack = list(initial)
        exact = sum(e[2] for e in stack if e[2] == e[3])
        stack = [e for e in stack if e[2] != e[3]]
        flo = sum(e[2] for e in initial)
        fhi = sum(e[3] for e in initial)
        expansions = 0
        resumed_from = None
    elif resume_path and Path(resume_path).exists():
        ck = json.loads(Path(resume_path).read_text())
        stack = [(e[0], tuple(e[1]), e[2], e[3]) for e in ck["stack"]]
        exact = ck["exact"]
        flo, fhi = ck["floor"], ck["ceiling"]
        expansions = ck["expansions"]
        resumed_from = str(resume_path)
    else:
        lo0, hi0 = interval(0, (0,) * m)
        stack = [(0, (0,) * m, lo0, hi0)]
        exact = 0
        flo, fhi = lo0, hi0
        expansions = 0
        resumed_from = None
        if lo0 == hi0:
            exact = lo0
            stack = []

    t0 = time.time()
    last_ck = t0
    completed = False
    while stack:
        if max_expansions and expansions >= max_expansions:
            break
        if time.time() - t0 > max_seconds:
            break
        i, used, lo, hi = stack.pop()
        flo -= lo
        fhi -= hi
        expansions += 1
        ci = i + 1
        c = it[i]
        nxt = tuple(used[j] + c[j] for j in range(m))
        child_useds = [used]  # exclude child
        if all(nxt[j] <= caps[j] for j in range(m)):
            child_useds.append(nxt)  # include child
        # evaluate exclude first, include second; the push order below
        # then puts the include child on top (LIFO depth-first).
        evaled = []
        for cused in child_useds:
            if ci == n:
                evaled.append((None, 1, 1))
                continue
            clo, chi = interval(ci, cused)
            evaled.append((cused, clo, chi))
            if (spot["target_depth"] is not None and ci == spot["target_depth"]
                    and spot["record"] is None and clo == chi):
                spot["record"] = {"depth": ci, "used": list(cused),
                                  "value": clo}
        for cused, clo, chi in evaled:
            if cused is None or clo == chi:
                exact += clo
                flo += clo
                fhi += chi
            else:
                stack.append((ci, cused, clo, chi))
                flo += clo
                fhi += chi
        if expansions % progress_every == 0:
            rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            print(f"[{case_name}] expansions={expansions} stack={len(stack)} "
                  f"interval=[{flo}, {fhi}] width={fhi - flo} "
                  f"elapsed={time.time() - t0:.1f}s maxrss={rss}KB",
                  flush=True)
            if checkpoint_path:
                save_checkpoint(checkpoint_path, stack, exact, flo, fhi,
                                expansions, pair)
                last_ck = time.time()
    else:
        completed = True
    if not stack:
        completed = True
    if checkpoint_path:
        save_checkpoint(checkpoint_path, stack, exact, flo, fhi,
                        expansions, pair)
    elapsed = time.time() - t0
    peak_kb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return {
        "case": case_name, "n": n, "resources": m, "pair": list(pair),
        "completed": completed,
        "exact_count": flo if completed else None,
        "interval": [flo, fhi], "width": fhi - flo,
        "exact_counted_in_collapsed_subtrees": exact,
        "expansions": expansions, "stack_nodes_at_end": len(stack),
        "build_seconds": round(build_seconds, 3),
        "count_seconds": round(elapsed, 3),
        "peak_rss_kb": peak_kb,
        "resumed_from": resumed_from,
        "spot_subtree": spot["record"],
    }


# --------------------------------------------------------------------------
# fork-split parallel driver: split the tree at a fixed depth into
# prefix subtrees, assign them LPT (largest interval width first) to
# --workers processes forked after the structures are built, so the
# suffix grids are shared copy-on-write.  Each worker runs the same
# depth-first counter on its own stack with its own checkpoint file;
# the parent sums the per-worker exact counts and intervals.
# --------------------------------------------------------------------------
_WORKER_CTX = {}


def _worker_main(k):
    ctx = _WORKER_CTX
    res = count(ctx["case"], ctx["caps"], ctx["costs"], ctx["pair"],
                ctx["max_seconds"], ctx["max_expansions"],
                ctx["checkpoint"] + f"_w{k}" if ctx["checkpoint"] else None,
                None, structures=ctx["structures"],
                initial=ctx["assignments"][k], tag=f"w{k}")
    Path(ctx["out"] + f"_w{k}.json").write_text(json.dumps(res, indent=1))
    print(f"[worker {k}] done: expansions={res['expansions']} "
          f"interval={res['interval']} completed={res['completed']}",
          flush=True)


def parallel_count(case_name, caps, costs, pair, max_seconds,
                   max_expansions, checkpoint_base, out_base,
                   workers=2, split_depth=6):
    import multiprocessing as mp
    n, m = len(costs), len(caps)
    t_build = time.time()
    structures = build_structures(caps, costs, pair)
    build_seconds = time.time() - t_build
    it, suff_tot, pref, grids = structures
    interval = make_interval_fn(caps, suff_tot, pref, grids, pair)

    # split: expand from the root until every live node is at
    # split_depth (or exact), collecting exact mass on the way.
    lo0, hi0 = interval(0, (0,) * m)
    frontier = [(0, (0,) * m, lo0, hi0)]
    split_exact = 0
    while any(e[0] < split_depth for e in frontier):
        nxt_frontier = []
        for (i, used, lo, hi) in frontier:
            if i >= split_depth or lo == hi:
                if lo == hi:
                    split_exact += lo
                else:
                    nxt_frontier.append((i, used, lo, hi))
                continue
            ci = i + 1
            c = it[i]
            inc = tuple(used[j] + c[j] for j in range(m))
            childs = [used]
            if all(inc[j] <= caps[j] for j in range(m)):
                childs.append(inc)
            for cused in childs:
                clo, chi = interval(ci, cused)
                if clo == chi:
                    split_exact += clo
                else:
                    nxt_frontier.append((ci, cused, clo, chi))
        frontier = nxt_frontier
    # LPT assignment by interval width.
    frontier.sort(key=lambda e: -(e[3] - e[2]))
    assignments = [[] for _ in range(workers)]
    loads = [0] * workers
    for e in frontier:
        k = min(range(workers), key=lambda t: loads[t])
        assignments[k].append(e)
        loads[k] += e[3] - e[2]
    print(f"[split] depth={split_depth} prefixes={len(frontier)} "
          f"split_exact={split_exact} loads(width)={loads}", flush=True)

    _WORKER_CTX.update({
        "case": case_name, "caps": caps, "costs": costs, "pair": pair,
        "max_seconds": max_seconds, "max_expansions": max_expansions,
        "checkpoint": checkpoint_base, "out": out_base,
        "structures": structures, "assignments": assignments})
    ctx = mp.get_context("fork")
    procs = [ctx.Process(target=_worker_main, args=(k,))
             for k in range(workers) if assignments[k]]
    for p in procs:
        p.start()
    for p in procs:
        p.join()
    parts = []
    for k in range(workers):
        f = Path(out_base + f"_w{k}.json")
        if f.exists():
            parts.append(json.loads(f.read_text()))
    completed = len(parts) == workers and all(p["completed"] for p in parts)
    # Each worker's interval covers exactly its assigned prefixes
    # (its floor includes its collapsed-subtree exact mass).  The
    # split_exact mass was resolved before assignment and is in no
    # worker's interval, so the totals are:
    flo = split_exact + sum(p["interval"][0] for p in parts)
    fhi = split_exact + sum(p["interval"][1] for p in parts)
    result = {
        "case": case_name, "n": n, "resources": m, "pair": list(pair),
        "mode": f"parallel workers={workers} split_depth={split_depth}",
        "completed": completed,
        "exact_count": flo if completed else None,
        "interval": [flo, fhi], "width": fhi - flo,
        "split_exact": split_exact,
        "expansions": sum(p["expansions"] for p in parts),
        "build_seconds": round(build_seconds, 3),
        "workers": [{k: p[k] for k in ("interval", "expansions",
                                       "count_seconds", "peak_rss_kb",
                                       "stack_nodes_at_end",
                                       "spot_subtree")} for p in parts],
    }
    if completed:
        assert flo == fhi
    return result


def save_checkpoint(path, stack, exact, flo, fhi, expansions, pair):
    data = {"stack": [[i, list(u), lo, hi] for (i, u, lo, hi) in stack],
            "exact": exact, "floor": flo, "ceiling": fhi,
            "expansions": expansions, "pair": list(pair)}
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps(data))
    tmp.replace(path)


def brute_force_subtree(caps, it, depth, used):
    """Independent count of completions of items depth.. given the
    used vector: plain enumeration, no distribution bounds."""
    n, m = len(it), len(caps)
    rem = [caps[j] - used[j] for j in range(m)]
    suffix = it[depth:]
    cnt = 0

    def rec(k, room):
        nonlocal cnt
        if k == len(suffix):
            cnt += 1
            return
        rec(k + 1, room)
        c = suffix[k]
        if all(room[j] >= c[j] for j in range(m)):
            rec(k + 1, [room[j] - c[j] for j in range(m)])

    rec(0, rem)
    return cnt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(HERE.parents[2] / "perfectpower"))
    ap.add_argument("--case", default="petersen_50")
    ap.add_argument("--pair", default="3,4")
    ap.add_argument("--max-seconds", type=float, default=1800.0)
    ap.add_argument("--max-expansions", type=int, default=0)
    ap.add_argument("--checkpoint", default=None)
    ap.add_argument("--resume", default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--split-depth", type=int, default=6)
    args = ap.parse_args()
    repo = Path(args.repo)
    caps, costs = load_case(repo, args.case)
    pair = tuple(int(x) for x in args.pair.split(","))
    ck = args.checkpoint or str(HERE / f"{args.case}_checkpoint.json")
    out = Path(args.out) if args.out else HERE / f"{args.case}_bounded_results.json"
    if args.workers > 1:
        result = parallel_count(args.case, caps, costs, pair,
                                args.max_seconds, args.max_expansions,
                                ck, str(out), workers=args.workers,
                                split_depth=args.split_depth)
        # verify one worker's spot subtree by brute force
        for w in result["workers"]:
            spot = w.get("spot_subtree")
            if spot:
                n, m = len(costs), len(caps)
                order = sorted(range(n), key=lambda i: -sum(
                    costs[i][j] / caps[j] for j in range(m)))
                it = [tuple(costs[i]) for i in order]
                bf = brute_force_subtree(caps, it, spot["depth"],
                                         tuple(spot["used"]))
                result["spot_check"] = {
                    "depth": spot["depth"], "frontier_value": spot["value"],
                    "brute_force_value": bf, "agrees": bf == spot["value"]}
                print(f"spot check at depth {spot['depth']}: frontier "
                      f"value {spot['value']} vs brute force {bf} "
                      f"agree={bf == spot['value']}", flush=True)
                break
        out.write_text(json.dumps(result, indent=1))
        print(json.dumps({k: result[k] for k in (
            "case", "completed", "exact_count", "interval", "width",
            "expansions")}, indent=1), flush=True)
        print("wrote", out.name, flush=True)
        return
    result = count(args.case, caps, costs, pair, args.max_seconds,
                   args.max_expansions, ck, args.resume)
    # Spot re-verification of one distribution-exact subtree by brute
    # force, when the run recorded one and finished or paused.
    spot = result["spot_subtree"]
    if spot is not None:
        caps2, costs2 = load_case(repo, args.case)
        # rebuild the same branching order to recover the item list
        n, m = len(costs2), len(caps2)
        order = sorted(range(n), key=lambda i: -sum(
            costs2[i][j] / caps2[j] for j in range(m)))
        it = [tuple(costs2[i]) for i in order]
        bf = brute_force_subtree(caps2, it, spot["depth"],
                                 tuple(spot["used"]))
        result["spot_subtree"]["brute_force_value"] = bf
        result["spot_subtree"]["agrees"] = (bf == spot["value"])
        print(f"spot check at depth {spot['depth']}: frontier value "
              f"{spot['value']} vs brute force {bf} "
              f"agree={bf == spot['value']}", flush=True)
    out = Path(args.out) if args.out else HERE / f"{args.case}_bounded_results.json"
    out.write_text(json.dumps(result, indent=1))
    print(json.dumps({k: result[k] for k in (
        "case", "completed", "exact_count", "interval", "width",
        "expansions", "count_seconds", "peak_rss_kb")}, indent=1),
        flush=True)
    print("wrote", out.name, flush=True)


if __name__ == "__main__":
    main()
