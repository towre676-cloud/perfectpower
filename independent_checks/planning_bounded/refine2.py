#!/usr/bin/env python3
"""Disk-backed best-first refinement of the petersen_50 frontier.

Continues refine.py's frontier (loaded from its pickle) with the
widest nodes kept in a RAM heap capped at --ram-cap entries; when
the heap exceeds the cap, its smallest-width tail is pickled to a
spill file under --spill-dir and reloaded FIFO as the heap drains.
Expansion order is therefore approximately widest-first (exactly
widest-first within the RAM tier), while the interval accounting
-- exact constant + sum of all live nodes' bounds -- stays rigorous
regardless of order.  Stops at a width target, a time cap, or
frontier exhaustion.  State (RAM heap pickle + spill manifest) is
saved at exit and periodically, so the pass is resumable.
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


def save_state(spill_dir, heap, spill_files, exact, flo, fhi, expansions):
    with open(spill_dir / "ram_heap.pkl", "wb") as f:
        pickle.dump(heap, f)
    (spill_dir / "manifest.json").write_text(json.dumps({
        "exact": exact, "floor": flo, "ceiling": fhi,
        "expansions": expansions,
        "spill_files": [p.name for p in spill_files]}, indent=1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--frontier-in", default=str(HERE / "petersen_50_refined_frontier.pkl"))
    ap.add_argument("--spill-dir", default=str(HERE / "spill"))
    ap.add_argument("--max-seconds", type=float, default=1800)
    ap.add_argument("--ram-cap", type=int, default=1_600_000)
    ap.add_argument("--keep", type=int, default=1_100_000)
    ap.add_argument("--target-width", type=int, default=4_900_000_000_000)
    ap.add_argument("--out", default=str(HERE / "petersen_50_refined2_results.json"))
    ap.add_argument("--resume-spill", action="store_true")
    args = ap.parse_args()

    spill_dir = Path(args.spill_dir)
    spill_dir.mkdir(exist_ok=True)
    caps, costs = bc.load_case(Path(args.repo), "petersen_50")
    pair = (3, 4)
    n, m = len(costs), len(caps)
    t0 = time.time()
    structures = bc.build_structures(caps, costs, pair)
    it, suff_tot, pref, grids = structures
    interval = bc.make_interval_fn(caps, suff_tot, pref, grids, pair)
    print(f"structures built in {time.time()-t0:.1f}s", flush=True)

    if args.resume_spill:
        man = json.loads((spill_dir / "manifest.json").read_text())
        exact, flo, fhi = man["exact"], man["floor"], man["ceiling"]
        expansions = man["expansions"]
        with open(spill_dir / "ram_heap.pkl", "rb") as f:
            heap = pickle.load(f)
        heapq.heapify(heap)
        spill_files = [spill_dir / name for name in man["spill_files"]]
        spilled = 0
        for p in spill_files:
            with open(p, "rb") as f:
                spilled += len(pickle.load(f))
        spill_seq = 1000
        print(f"resumed from spill state: ram={len(heap)} "
              f"spilled={spilled} width={fhi-flo}", flush=True)
    else:
        with open(args.frontier_in, "rb") as f:
            state = pickle.load(f)
        exact, flo, fhi = state["exact"], state["floor"], state["ceiling"]
        expansions = state["expansions"]
        heap = state["heap"]
        heapq.heapify(heap)
        spill_files = []
        spilled = 0
        spill_seq = 0
    print(f"loaded frontier: live={len(heap)} width={fhi-flo} "
          f"exact={exact}", flush=True)

    t_start = time.time()
    status = "time budget exhausted"
    while time.time() - t_start < args.max_seconds:
        if not heap:
            if spill_files:
                nxt = spill_files.pop(0)
                with open(nxt, "rb") as f:
                    heap = pickle.load(f)
                heapq.heapify(heap)
                spilled -= len(heap)
                nxt.unlink()
                print(f"reloaded spill ({len(heap)} nodes); "
                      f"spilled remaining={spilled}", flush=True)
                continue
            status = "frontier exhausted (closed)"
            break
        if fhi - flo <= args.target_width:
            status = "target width reached"
            break
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
        for cused in childs:
            clo, chi = interval(ci, cused)
            flo += clo
            fhi += chi
            if clo != chi:
                heapq.heappush(heap, (-(chi - clo), -ci, cused, clo, chi))
            else:
                exact += clo
        expansions += 1
        if len(heap) > args.ram_cap:
            heap.sort()  # widest first (key is -width)
            spill_part = heap[args.keep:]
            heap = heap[:args.keep]
            heapq.heapify(heap)
            p = spill_dir / f"spill_{spill_seq:04d}.pkl"
            spill_seq += 1
            with open(p, "wb") as f:
                pickle.dump(spill_part, f)
            spill_files.append(p)
            spilled += len(spill_part)
            save_state(spill_dir, heap, spill_files, exact, flo, fhi,
                       expansions)
            print(f"spilled {len(spill_part)} nodes to {p.name}; "
                  f"total live={len(heap)+spilled} width={fhi-flo}",
                  flush=True)
        if expansions % 250_000 == 0:
            print(f"refine2 expansions={expansions} ram={len(heap)} "
                  f"spilled={spilled} width={fhi-flo} "
                  f"elapsed={time.time()-t_start:.0f}s "
                  f"maxrss={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}KB",
                  flush=True)
    save_state(spill_dir, heap, spill_files, exact, flo, fhi, expansions)
    result = {
        "case": "petersen_50",
        "stage": "disk-backed best-first refinement (refine2)",
        "status": status,
        "completed": status.startswith("frontier exhausted"),
        "exact_count": flo if status.startswith("frontier exhausted") else None,
        "interval": [flo, fhi],
        "width": fhi - flo,
        "exact_counted_constant": exact,
        "live_frontier_nodes_total": len(heap) + spilled,
        "ram_heap_nodes": len(heap),
        "spilled_nodes": spilled,
        "total_refine_expansions_incl_refine1": expansions,
        "refine2_seconds": round(time.time() - t_start, 1),
        "peak_rss_kb": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "prior_interval": [698342755629882, 703790474857480],
        "prior_width": 703790474857480 - 698342755629882,
        "strictly_narrower_than_prior": (fhi - flo) < 703790474857480 - 698342755629882,
        "resume": "python3 refine2.py --frontier-in spill/ram_heap.pkl "
                  "with spill/manifest.json accounting + remaining "
                  "spill files (see REPORT.md)",
    }
    Path(args.out).write_text(json.dumps(result, indent=1))
    print(json.dumps(result, indent=1), flush=True)


if __name__ == "__main__":
    main()
