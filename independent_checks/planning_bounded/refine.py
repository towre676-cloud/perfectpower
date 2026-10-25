#!/usr/bin/env python3
"""Bounded best-first refinement of the petersen_50 frontier left by
the depth-first workers in bounded_count.py.

Starts from the two worker checkpoints (a partition of the whole
tree: an exact constant plus 56 frontier nodes with rigorous
intervals), verifies the accounting identity, then expands
widest-first exactly as attempt_50.py's frontier_interval did,
under a hard live-heap cap and a time cap.  Stopping at any moment
leaves a rigorous interval: exact constant + sum of frontier
bounds.  The refined frontier is pickled periodically so this
pass is itself resumable.
"""
import argparse
import heapq
import json
import pickle
import resource
import time
from pathlib import Path

import bounded_count as bc

HERE = Path(__file__).resolve().parent


def plain_count(caps, items, i, used):
    """Distribution-free exact count of completions of items[i:]
    from used capacities (plain recursion; small subtrees only)."""
    if i == len(items):
        return 1
    total = plain_count(caps, items, i + 1, used)
    inc = tuple(used[j] + items[i][j] for j in range(len(caps)))
    if all(inc[j] <= caps[j] for j in range(len(caps))):
        total += plain_count(caps, items, i + 1, inc)
    return total


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--max-seconds", type=float, default=2400)
    ap.add_argument("--max-live", type=int, default=2_000_000)
    ap.add_argument("--out", default=str(HERE / "petersen_50_refined_results.json"))
    ap.add_argument("--frontier-out", default=str(HERE / "petersen_50_refined_frontier.pkl"))
    ap.add_argument("--frontier-in", default=None)
    args = ap.parse_args()

    caps, costs = bc.load_case(Path(args.repo), "petersen_50")
    pair = (3, 4)
    n, m = len(costs), len(caps)
    t0 = time.time()
    structures = bc.build_structures(caps, costs, pair)
    it, suff_tot, pref, grids = structures
    interval = bc.make_interval_fn(caps, suff_tot, pref, grids, pair)
    print(f"structures built in {time.time()-t0:.1f}s", flush=True)

    split_exact = 211070361143360  # from the parallel run's split log
    if args.frontier_in:
        with open(args.frontier_in, "rb") as f:
            state = pickle.load(f)
        exact = state["exact"]
        heap = state["heap"]
        heapq.heapify(heap)
        flo, fhi = state["floor"], state["ceiling"]
        start_exp = state["expansions"]
        print(f"resumed refined frontier: {len(heap)} nodes, "
              f"width {fhi-flo}", flush=True)
    else:
        exact = split_exact
        flo = fhi = split_exact
        heap = []
        start_exp = 0
        for k in (0, 1):
            ck = json.loads((HERE / f"petersen_50_checkpoint.json_w{k}").read_text())
            assert ck["exact"] + sum(e[2] for e in ck["stack"]) == ck["floor"]
            assert ck["exact"] + sum(e[3] for e in ck["stack"]) == ck["ceiling"]
            exact += ck["exact"]
            flo += ck["floor"]
            fhi += ck["ceiling"]
            for (i, used, lo, hi) in ck["stack"]:
                heapq.heappush(heap, (-(hi - lo), -i, tuple(used), lo, hi))
        print(f"frontier reconstructed: exact constant {exact}, "
              f"{len(heap)} nodes, interval [{flo}, {fhi}] "
              f"width {fhi-flo}", flush=True)

    t_start = time.time()
    expansions = start_exp
    last_ck = expansions
    status = "time budget exhausted"
    while heap and time.time() - t_start < args.max_seconds:
        negw, negi, used, lo, hi = heapq.heappop(heap)
        i = -negi
        flo -= lo
        fhi -= hi
        ci = i + 1
        c = it[i]
        inc = tuple(used[j] + c[j] for j in range(m))
        childs = [used]
        if all(inc[j] <= caps[j] for j in range(m)):
            childs.append(inc)
        kids = [(cused, *interval(ci, cused)) for cused in childs]
        live_kids = [kd for kd in kids if kd[1] != kd[2]]
        if len(heap) + len(live_kids) > args.max_live:
            # restore the popped node untouched and stop: the heap
            # remains a rigorous frontier covering the whole tree.
            heapq.heappush(heap, (negw, negi, used, lo, hi))
            flo += lo
            fhi += hi
            status = "live-frontier cap reached"
            break
        for cused, clo, chi in kids:
            flo += clo
            fhi += chi
            if clo != chi:
                heapq.heappush(heap, (-(chi - clo), -ci, cused, clo, chi))
            else:
                exact += clo
        expansions += 1
        if expansions % 500_000 == 0:
            print(f"refine expansions={expansions} live={len(heap)} "
                  f"width={fhi-flo} elapsed={time.time()-t_start:.0f}s "
                  f"maxrss={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}KB",
                  flush=True)
        if expansions - last_ck >= 2_000_000:
            last_ck = expansions
            with open(args.frontier_out, "wb") as f:
                pickle.dump({"exact": exact, "heap": heap,
                             "floor": flo, "ceiling": fhi,
                             "expansions": expansions}, f)
    if not heap:
        status = "frontier exhausted (closed)"
    with open(args.frontier_out, "wb") as f:
        pickle.dump({"exact": exact, "heap": heap, "floor": flo,
                     "ceiling": fhi, "expansions": expansions}, f)

    # internal consistency check: deepest frontier node recounted by
    # plain distribution-free recursion must lie inside [lo, hi].
    check = None
    if heap:
        for cand in sorted(heap, key=lambda e: e[1]):
            _, negi, used, lo, hi = cand
            if n - (-negi) <= 22:
                val = plain_count(caps, list(it), -negi, used)
                check = {"depth": -negi, "frontier_interval": [lo, hi],
                         "plain_recursion_count": val,
                         "inside": lo <= val <= hi}
                print("consistency check:", check, flush=True)
                break

    result = {
        "case": "petersen_50",
        "stage": "best-first refinement of the depth-first frontier",
        "status": status,
        "completed": not heap,
        "exact_count": flo if not heap else None,
        "interval": [flo, fhi],
        "width": fhi - flo,
        "exact_counted_constant": exact,
        "live_frontier_nodes": len(heap),
        "refine_expansions": expansions,
        "refine_seconds": round(time.time() - t_start, 1),
        "peak_rss_kb": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "consistency_check": check,
        "prior_interval": [698342755629882, 703790474857480],
        "prior_width": 703790474857480 - 698342755629882,
        "strictly_narrower_than_prior": (fhi - flo) < 703790474857480 - 698342755629882,
    }
    Path(args.out).write_text(json.dumps(result, indent=1))
    print(json.dumps(result, indent=1), flush=True)


if __name__ == "__main__":
    main()
