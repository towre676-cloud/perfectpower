#!/usr/bin/env python3
"""Aggregate a petersen50_c campaign directory into the current
global rigorous interval.

Reads PREFIX.bin (header: split_exact, sum_lo, sum_hi; per-prefix
lo/hi) and all results_w*.jsonl in the campaign dir.

The global interval is
  [ split_exact + sum(solved exact) + sum(unsolved lo),
    split_exact + sum(solved exact) + sum(unsolved hi) ]
Duplicate result lines for a prefix (possible after a resume) are
counted once; all copies must agree on the exact value.

Prints the smallest unsolved prefix index (the value claim.txt
should be reset to before relaunching workers after a stop), the
number of solved/unsolved prefixes, total expansions and seconds,
and -- with --out -- writes a summary JSON.
"""
import argparse
import glob
import json
import struct
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("dir")
ap.add_argument("--prefix", default="prefixes.bin")
ap.add_argument("--out", default=None)
args = ap.parse_args()
d = Path(args.dir)

blob = (d / args.prefix).read_bytes()
assert blob[:4] == b"PFX1"
n, m, depth, count = struct.unpack_from("<4I", blob, 4)
split_exact, sum_lo, sum_hi = struct.unpack_from("<3Q", blob, 20)
off = 44
recs = []
for _ in range(count):
    dep = blob[off]
    used = struct.unpack_from(f"<{m}H", blob, off + 4)
    lo, hi = struct.unpack_from("<2Q", blob, off + 4 + 2 * m)
    recs.append((dep, used, lo, hi))
    off += 4 + 2 * m + 16

solved = {}
total_exp = 0
total_sec = 0.0
timeouts = []
for path in glob.glob(str(d / "results_w*.jsonl")):
    for line in Path(path).read_text().splitlines():
        r = json.loads(line)
        total_exp += r.get("expansions", 0)
        total_sec += r.get("seconds", 0.0)
        if "exact" in r:
            idx = r["prefix"]
            if idx in solved:
                assert solved[idx] == r["exact"], f"prefix {idx} disagreement"
            solved[idx] = r["exact"]
        elif r.get("timeout"):
            timeouts.append(r["prefix"])

unsolved = [k for k in range(count) if k not in solved]
floor = split_exact + sum(solved.values()) + sum(recs[k][2] for k in unsolved)
ceil = split_exact + sum(solved.values()) + sum(recs[k][3] for k in unsolved)
summary = {
    "split_depth": depth,
    "prefixes_total": count,
    "prefixes_solved": len(solved),
    "prefixes_unsolved": len(unsolved),
    "smallest_unsolved_prefix": min(unsolved) if unsolved else None,
    "timeout_prefixes": sorted(set(timeouts)),
    "split_exact": split_exact,
    "interval": [floor, ceil],
    "width": ceil - floor,
    "completed": not unsolved,
    "exact_count": floor if not unsolved else None,
    "total_expansions": total_exp,
    "total_worker_seconds": round(total_sec, 3),
}
print(json.dumps(summary, indent=1))
if args.out:
    Path(args.out).write_text(json.dumps(summary, indent=1))
