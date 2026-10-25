#!/usr/bin/env python3
"""Driver for the petersen_39 count closure (see frontier39_core.py
for the monitored frontier copy and its provenance).

Steps:
  1. Choose the resource pair for petersen_28 and petersen_39 by wave
     one's criterion: exact distributions (attempt_50.py imported
     read-only), pair minimising count_le_both.
  2. Validation: wave one's ORIGINAL frontier_interval must close
     petersen_28 exactly (208817578), and the monitored copy must
     reproduce the original's result field-for-field (bar timings).
  3. Closure run: monitored copy on petersen_39, budget
     30,000,000 expansions / 5400 s / RSS cap 2,600,000 KB.

Usage: python3 frontier39.py [--repo PATH] [--skip-validation]
Writes frontier39_results.json next to this script.
"""
import argparse
import importlib.util
import json
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
WAVE1 = HERE.parent / "planning" / "attempt_50.py"  # wave one's script, in-repo

spec = importlib.util.spec_from_file_location("attempt50", str(WAVE1))
A = importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)
spec2 = importlib.util.spec_from_file_location(
    "frontier39_core", str(HERE / "frontier39_core.py"))
C = importlib.util.module_from_spec(spec2)
spec2.loader.exec_module(C)


def load_case(repo, name):
    data = json.loads((repo / "data/planning/petersen.json").read_text())
    case = [c for c in data if c["name"] == name][0]
    sp = case["specification"]
    caps = [r["max"] for r in sp["resources"]]
    costs = [v["costs"] for v in sp["variables"]]
    profits = [int(v["profit"]) for v in sp["variables"]]
    return caps, costs, profits


def best_pair(caps, costs):
    singles, pairs = A.distributions(caps, costs)
    bp = min(pairs, key=lambda p: p["count_le_both"])
    return tuple(bp["resources"]), bp


def strip_volatile(d):
    return {k: v for k, v in d.items()
            if k not in ("seconds", "peak_rss_kb", "stopped_reason")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(HERE.parents[2]))  # default: repository root
    ap.add_argument("--skip-validation", action="store_true")
    ap.add_argument("--expansions", type=int, default=30_000_000)
    ap.add_argument("--time-budget", type=float, default=5400.0)
    ap.add_argument("--rss-cap-kb", type=int, default=2_600_000)
    args = ap.parse_args()
    repo = Path(args.repo)
    out_path = HERE / "frontier39_results.json"
    results = {}

    caps28, costs28, _ = load_case(repo, "petersen_28")
    pair28, bp28 = best_pair(caps28, costs28)
    print(f"petersen_28 best pair {bp28['resources']} "
          f"count_le_both={bp28['count_le_both']}", flush=True)
    caps39, costs39, _ = load_case(repo, "petersen_39")
    pair39, bp39 = best_pair(caps39, costs39)
    print(f"petersen_39 caps={caps39} best pair {bp39['resources']} "
          f"count_le_both={bp39['count_le_both']}", flush=True)
    results["pair_choice"] = {
        "criterion": "pair minimising count_le_both (wave one)",
        "petersen_28": {"pair": list(pair28),
                        "count_le_both": bp28["count_le_both"]},
        "petersen_39": {"pair": list(pair39),
                        "count_le_both": bp39["count_le_both"],
                        "caps": caps39}}
    out_path.write_text(json.dumps(results, indent=1))

    if not args.skip_validation:
        print("validation: original frontier_interval on petersen_28...",
              flush=True)
        t0 = time.time()
        orig = A.frontier_interval(caps28, costs28, pair28, 10_000_000, 1800.0)
        print(f"  original: {orig} ({time.time()-t0:.1f}s)", flush=True)
        assert orig["completed"] and orig["lower"] == orig["upper"] == 208817578, \
            "original frontier failed to close petersen_28"
        print("validation: monitored copy on petersen_28...", flush=True)
        t0 = time.time()
        copy = C.frontier_interval(caps28, costs28, pair28, 10_000_000, 1800.0,
                                   rss_cap_kb=None, progress_every=0)
        print(f"  copy: {copy} ({time.time()-t0:.1f}s)", flush=True)
        assert strip_volatile(copy) == strip_volatile(orig), \
            "monitored copy disagrees with original on petersen_28"
        results["validation_petersen_28"] = {
            "known_count": 208817578, "original": orig, "copy": copy,
            "identical_apart_from_volatile_fields": True}
        out_path.write_text(json.dumps(results, indent=1))
        print("validation PASSED", flush=True)

    print(f"closure run: petersen_39, pair={pair39}, "
          f"budget={args.expansions} expansions / {args.time_budget}s / "
          f"RSS cap {args.rss_cap_kb} KB", flush=True)
    fr = C.frontier_interval(caps39, costs39, pair39, args.expansions,
                             args.time_budget, rss_cap_kb=args.rss_cap_kb,
                             progress_every=250_000)
    print(f"petersen_39 frontier: {fr}", flush=True)
    results["petersen_39_frontier"] = fr
    stated = 368072359571
    results["petersen_39_verdict"] = {
        "stated_count": stated,
        "closed": bool(fr["completed"] and fr["lower"] == fr["upper"]),
        "exact_count": fr["lower"] if fr["lower"] == fr["upper"] else None,
        "agrees_with_stated": (fr["lower"] == fr["upper"] == stated),
        "interval": [fr["lower"], fr["upper"]],
        "interval_width": fr["upper"] - fr["lower"]}
    out_path.write_text(json.dumps(results, indent=1))
    print("VERDICT:", results["petersen_39_verdict"], flush=True)
    print("wrote", out_path)


if __name__ == "__main__":
    main()
