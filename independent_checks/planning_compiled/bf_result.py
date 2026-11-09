#!/usr/bin/env python3
"""Emit the petersen_50 result JSON from the best-first state file.

Reads bf50/state.bin (BFS1 format, documented in petersen.c), combines
its rigorous interval with the depth-first campaign's interval (via
aggregate.py on campaign50b/) and the Python campaign's audited
interval, and writes petersen_50_result.json.  Rigorous intervals
intersect: every campaign's [lo, hi] provably contains the exact
count, so the intersection does too.
"""
import json
import struct
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

PYTHON_AUDITED = [699497138009147, 703473996819983]


def read_bf_state(path):
    with open(path, "rb") as f:
        head = f.read(16)
        assert head[:4] == b"BFS1", head[:4]
        n, m, npairs = struct.unpack_from("<III", head, 4)
        rest = f.read(8 * npairs + 40)
        pairs = struct.unpack_from("<" + "I" * (2 * npairs), rest, 0)
        exact, flo, fhi, expansions, heap_len = struct.unpack_from(
            "<QQQQQ", rest, 8 * npairs)
    return {
        "n": n, "m": m,
        "pairs": [[pairs[2 * i], pairs[2 * i + 1]] for i in range(npairs)],
        "exact_accumulated": exact,
        "interval": [flo, fhi],
        "width": fhi - flo,
        "expansions": expansions,
        "heap_nodes": heap_len,
        "closed_exactly": heap_len == 0 and flo == fhi,
    }


def main():
    bf = read_bf_state(HERE / "bf50" / "state.bin")
    agg = subprocess.run(
        [sys.executable, str(HERE / "aggregate.py"), str(HERE / "campaign50b")],
        capture_output=True, text=True)
    dfs = json.loads(agg.stdout)
    lo = max(bf["interval"][0], dfs["interval"][0], PYTHON_AUDITED[0])
    hi = min(bf["interval"][1], dfs["interval"][1], PYTHON_AUDITED[1])
    assert lo <= hi, "interval intersection empty -- inconsistency!"
    out = {
        "case": "petersen_50",
        "best_first_campaign": bf,
        "dfs_prefix_campaign": {
            "prefixes_solved": dfs["prefixes_solved"],
            "prefixes_total": dfs["prefixes_total"],
            "interval": dfs["interval"],
            "width": dfs["width"],
            "total_expansions": dfs["total_expansions"],
            "completed": dfs["completed"],
        },
        "python_campaign_audited_interval": PYTHON_AUDITED,
        "combined_rigorous_interval": [lo, hi],
        "combined_width": hi - lo,
        "combined_relative_width": (hi - lo) / lo,
        "exact_count": lo if lo == hi else None,
        "closed_exactly": lo == hi,
        "resumable_state": "bf50/state.bin (rerun petersen5 bfseed with the "
                           "same state path); campaign50b/ prefix state via "
                           "aggregate.py + claim.txt reset",
    }
    dest = HERE / "petersen_50_result.json"
    dest.write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
