# Petersen_50 exact count: a compiled counter, multi-pair bounds, and a best-first campaign

## Budget, stated up front

Structure building at most ~300 s per case; validation counting at
most ~900 s; the petersen_50 counting phase at most ~5,400 s of
counting per strategy (a depth-first prefix campaign and a
best-first refinement ran concurrently on the machine's two cores,
each with its own cap). Target peak RSS below ~3 GB total; measured
peaks are reported per run below. All arithmetic is exact integer
arithmetic (uint64 storage; counts are below 2^63; the lower-bound
differences are computed in int64 with magnitudes below 2^56). The
only floating point anywhere is the branching-order key, which
replicates CPython's `sum()` bit-for-bit (see "Port fidelity").

## What was built

`petersen.c` (built by the included `Makefile` as `petersen`, and as
`petersen5` with `-DMAXM=5` for the m = 5 cases) is a C port of the
exact frontier machinery of `attempt_50.py` / `bounded_count.py`:

- branching order: decreasing normalised cost
  sum_j costs[i][j]/caps[j], ties in original index order;
- suffix total cost vectors; suffix single-resource prefix counts;
- exact suffix resource-pair grids (subset DP clamped at the caps);
- node interval: exact subcube collapse if the whole suffix fits;
  otherwise hi = min over the pair counts and all single-resource
  counts, lo = max over pairs of (pair count − the other resources'
  violation counts), clamped to [0, hi].

With the single pair (3,4) this is exactly the Python machinery.
The generalisation to several pairs is the one deliberate extension:
`attempt_50.py`'s own report named "a second pair grid added to the
node bounds" as a plausible route to closure, and §Calibration shows
why. The campaign below uses the six pairs
(3,4), (1,4), (0,4), (0,1), (1,3), (2,4).

Modes: `root` (root interval + order), `dfs` (whole-tree depth-first
count with `bounded_count.count`'s exact stack discipline), `bf`
(best-first with DFS dives at a heap cap), `split` (level expansion
to a fixed depth, writing a binary prefix file), `worker`
(disk-checkpointed depth-first solution of split prefixes, claimed
dynamically), `bfseed` (best-first refinement seeded from a split
file, checkpointing its whole heap to a binary state file every
120 s; resumable by rerunning with the same state path).

Checkpoint formats are documented in the `petersen.c` header: the
prefix file (`PFX1`) and the best-first state file (`BFS1`) are
little-endian binary with the global accounting in their headers,
and `aggregate.py` recomputes a campaign's global interval from the
prefix file plus the per-prefix result lines at any moment.

## Port fidelity (how the port was verified against the Python)

- Root intervals reproduce the Python ones exactly for all three
  cases (petersen_28 [87,665,255, 212,273,251], petersen_39
  [88,921,646,116, 392,803,463,712], petersen_50
  [88,254,953,452,712, 746,335,444,328,064] — the last being the
  required reconciliation value).
- Branching orders match the Python order index-for-index on all
  three cases. This required one non-obvious replication: CPython's
  `sum()` uses Neumaier compensated summation for floats, and the
  naive C accumulation breaks an exact tie (petersen_50 items 13 and
  29, key 879/114400) the other way; the C keys use the same
  compensated algorithm.
- Whole-tree depth-first expansion counts are *identical* to the
  Python campaign's on both validation cases (see gates): the port
  expands the same nodes in the same order, just faster.

## Validation gates (both passed before petersen_50 was touched)

**Gate 1 — petersen_28 closes exactly at 208,817,578**, with
1,288,947 depth-first expansions, exactly the Python count, in
0.161 s of counting (Python: 7.9 s), peak RSS 62.7 MB.

**Gate 2 — petersen_39 closes exactly at 368,072,359,571**, with
136,680,243 depth-first expansions, exactly the Python count, in
13.5 s (Python: 693.7 s), peak RSS 101 MB. A best-first run of the
port closes the same case with the same total expansion count, as
it must: run to completion, every schedule expands the same set of
non-exact nodes; the schedules differ only in memory profile and in
how fast the interval narrows per expansion.

Single-thread depth-first speed of the port: ~8–10 million
expansions/second, versus the Python campaign's
~1.3×10^4–2.3×10^5/second depending on stage — a factor of roughly
50 on identical work.

## Calibration: multi-pair bounds shrink the tree itself

Total expansion counts to close petersen_39 exactly (schedule-
independent), by bound strength — data in `pair_calibration.json`:

| pair grids | expansions | vs (3,4) alone |
|---|---|---|
| (3,4) | 136,680,243 | 1× |
| (3,4),(1,4) | 122,569,754 | 0.90× |
| (3,4),(1,4),(0,4) | 59,958,733 | 0.44× |
| + (0,1) | 14,022,233 | 0.10× |
| + (1,3) | 9,651,527 | 0.071× |
| + (2,4) | 8,585,148 | 0.063× |
| all ten pairs | 7,270,504 | 0.053× (but 2.4× slower wall-clock: per-node cost and cache pressure grow) |

The six-pair set is the wall-clock optimum on the calibration case
(2.1 s versus 13.5 s single-pair). On petersen_28 the same set also
closes exactly (921,324 expansions). On petersen_50 the six-pair
root interval is [159,575,572,988,122, 746,335,444,328,064]: the
lower bound is raised from the single-pair 88,254,953,452,712 by
pair (1,4), the upper bound is unchanged (pair (3,4) is the tight
one at the root), and the interval is a strict tightening of — hence
consistent with — the reproduced single-pair root interval.

## petersen_50: two C campaigns — the count is CLOSED

**Exact feasible count of petersen_50: 702,508,860,122,761.**
The best-first campaign below exhausted its frontier (heap empty,
interval a single point) at 3,530.0 s of its final run segment.
The value lies inside the Python campaign's audited interval
[699,497,138,009,147, 703,473,996,819,983], inside the six-pair
depth-first campaign's interval [691,091,625,831,361,
703,631,266,985,368], and inside the abandoned single-pair
campaign's partial interval [677,205,149,345,632,
708,957,902,784,392] — every rigorous interval produced by any
implementation contains it. Machine-readable result:
`petersen_50_result.json` (generated by `bf_result.py` from the
final state file; the generator asserts the interval intersection
is non-empty before writing).

**Depth-first prefix campaign** (`campaign50/`, then `campaign50b/`):
split at depth 13, prefixes claimed dynamically by two workers.
With single-pair bounds this was abandoned after 18 prefixes
(6.51×10^9 expansions): the widest depth-13 subtrees each cost
2.3–4.3×10^8 expansions, and at the observed decay the full tree was
clearly beyond budget — the compiled speed alone does not fix the
schedule, because depth-first width is back-loaded. With six-pair
bounds the same campaign (3,734 prefixes, split exact constant
479,210,271,767,118) solved 76 prefixes exactly (6,486,774,808
expansions, 1,851.0 worker-seconds) before the best-first campaign
closed the count; its final interval, above, stands as an
independent-accounting consistency check. (One subtree exact count,
58,625,927,720, recurs identically in the single-pair and six-pair
campaigns.) A relaunch of its worker after an interruption failed
immediately on a missing case-file argument (`bad case` in
`campaign50b/worker0.err`); by then the refinement was the live
effort and the prefix campaign was not resumed again.

**Best-first refinement** (`bf50/`): seeded from the same depth-13
split, one process expanding the globally widest node, diving
(depth-first exact solution) whenever the heap reached its cap. It
consumed the Python campaign's lesson — best-first narrows width
fastest — with compiled throughput and six-pair bounds. Three
segments, all resuming the same `BFS1` state file: a probe (heap
cap 20,000,000; 194,602,607 expansions; interval
[701,960,034,308,882, 702,623,486,404,229], width 663,452,095,347 —
already ~6× narrower than the audited Python interval and strictly
inside it); a first main run (cap 30,000,000) interrupted at
377.9 s with the checkpoint at width 520,759,808,658
(2,091,093,908 expansions); and the resumed run, which ran
3,530.0 s to completion. Width in the resumed run fell steadily at
~1–3×10^8 per second, the heap began its final drain at width
~7×10^9, and the run ended `RESULT completed=1
exact=702508860122761 width=0`. Totals for the refinement:
24,921,515,942 expansions, peak RSS 2,192,872 KB (2.09 GiB). At
the Python campaign's best observed throughput (~2.3×10^5
expansions/second) those expansions alone would have taken ~30
hours; at its late-stage rate (~1.3×10^4/second), ~22 days — the
binding constraint was throughput, exactly as the Python report
diagnosed, and the compiled counter removed it.

Memory against the < 3 GB target: the best-first process peaked at
2.09 GiB and ran alone during the closing segment. During the
first segment the depth-first worker (peak 1,021,884 KB) ran
concurrently on the second core, for a combined peak of
~3.07 GiB — marginally over the combined target, reported as
measured.

## A note on the Python campaign's saved frontier

The `spill/` state shipped with the Python campaign could *not* be
resumed from: its `manifest.json` lists 305 spill files, of which 9
(`spill_1000.pkl`–`spill_1008.pkl`) are absent from disk, so the
manifest's accounting (exact 515,963,708,285,855, interval
[700,640,418,722,252, 703,048,919,377,106]) cannot be re-verified
from the files present and the state is not self-consistent. The
last *audited* Python interval is the report's
[699,497,138,009,147, 703,473,996,819,983], verified end-to-end by
`verify_final.py` at the time. That is the prior rigorous interval
this work reconciles against; the C campaigns started fresh, as the
task permitted, after reproducing the single-pair root interval
exactly.

## Classification

**Proved** (exact, by exhausted finite arguments replayable from
the sources here): the petersen_28 count 208,817,578 and the
petersen_39 count 368,072,359,571 under the compiled counter, with
expansion counts identical to the Python implementation under the
shared bounds; under the six-pair bounds both cases also close
exactly (921,324 and 8,585,148 expansions). **And the petersen_50
feasible count is exactly 702,508,860,122,761**, by exhaustion of
the best-first frontier: every node of the six-pair search tree
was either expanded or collapsed by an exact subcube/pair-grid
count, and the final accounting is a single point. The proof rests
on the validity of the node bounds (each pair grid counts exactly
the suffix subsets satisfying its two resources; taking hi as a
minimum over valid upper counts and lo as a maximum over valid
lower counts preserves rigour) and on the implementation, which
was verified node-for-node against the independent Python
machinery on both validation gates under the shared single-pair
bounds, and which closes both validation cases exactly under the
six-pair bounds as well. Three independently accounted rigorous
intervals (Python audited; C single-pair DFS partial; C six-pair
DFS partial) all contain the value. **Computed exactly as rigorous
bounds** along the way: the campaign intervals quoted above, now
superseded by the exact count. **Open**: nothing about the
petersen_50 feasible count. (The petersen_50 *maximiser* count of
exactly 1 was already proved by the earlier Python tie-counter
campaign, perfectpower PR #7; it is not re-derived here.)

## Files

`petersen.c`, `Makefile`, `convert_case.py` (repository JSON →
the counter's text format), `aggregate.py` (campaign accounting),
`spill_census.py` (the audit that found the spill state
incomplete), `bf_result.py` (final result generator),
`pair_calibration.json`, `petersen_28_validation.json`,
`petersen_39_validation.json`, `petersen_50_result.json`
(combined result: exact count 702,508,860,122,761,
`closed_exactly: true`), the case files `petersen_28.txt`,
`petersen_39.txt`, `petersen_50.txt`, campaign directories
`campaign50/` (single-pair DFS, abandoned), `campaign50b/`
(six-pair DFS), `bf50/` (best-first state — final state has an
empty heap and a point interval — and logs, including the closing
`RESULT` line in `bf50/bfseed_run.log`). The repository at
`~/workspace/research/perfectpower` was read, never edited, and
nothing was committed to GitHub.
