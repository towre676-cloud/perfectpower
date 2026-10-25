# Petersen_50 exact count: a memory-bounded frontier attempt

## Budget, stated up front

Structure building at most ~300 s per case; counting at most 5,400 s
per worker for petersen_50 (two workers, fork-split at depth 6) and
600–1,500 s for the validation cases; target peak RSS at most
1.5 GB total on this 7 GB / 2-core machine (the run shares the
machine with other work). On budget exhaustion the output is the
rigorous interval at that moment, with per-worker checkpoints that
make the run resumable (see "How to resume"). All arithmetic is exact
integer arithmetic; all counts are below 2^63, so the uint64 storage
used for the suffix grids is exact.

## What changed versus attempt_50.py, and what was reused

Reused unchanged, by construction: the branching order (decreasing
normalised cost), the node interval (exact subcube collapse; upper
bound the minimum of the suffix single-resource prefix counts and
the exact suffix resource-pair (4,5) count; lower bound the pair
count minus the exact violation counts of the other three resources),
and the suffix distributions themselves, rebuilt by the same
recurrences. The root interval reproduces attempt_50.py's exactly:
[88,254,953,452,712, 746,335,444,328,064], and the pair (4,5) root
count 746,335,444,328,064 is the prior best-pair upper bound.

Changed, for memory: (1) the best-first heap, whose live frontier
reached 2,994,605 nodes in the prior run and whose 15M-expansion
probe was OOM-killed, is replaced by a depth-first LIFO stack. The
pending set holds only unexplored siblings along one root-to-leaf
path — observed stack sizes stayed below ~50 entries in every run —
so pending-set memory is O(depth), not O(frontier). (2) The suffix
pair grids are flat `array('Q')` (147 MB for petersen_50) instead of
Python-int lists (~650 MB). (3) A fork-split parallel mode: the tree
is split at depth 6 (52 prefix subtrees for petersen_50;
211,070,361,143,360 portfolios were already counted exactly during
the split, cutting the total width from 658,080,490,875,352 to
84,854,332,298,872), prefixes are assigned largest-width-first to two
worker processes forked after the structures are built, so the grids
are shared copy-on-write. Each worker checkpoints its own stack
periodically (checkpoint JSON next to the results, suffix `_w0` /
`_w1`), and each worker's interval covers exactly its assigned
prefixes, so the totals are plain sums.

## Validation gates (both passed before petersen_50 was touched)

**petersen_28 closes exactly.** Single-worker depth-first run:
208,817,578, the repository's stated count, width 0, after
1,288,947 expansions in 7.9 s of counting (10.7 s wall including
structure building), peak RSS 86.7 MB, maximum stack in single
digits of live siblings per path. A subtree whose value was fixed
purely by the distribution bounds (depth 8 in branching order,
value 1,048,556) was re-counted by plain enumeration of its
2^20 completions: 1,048,556, exact agreement. The parallel mode
was also validated on this case (workers' totals 68,275,571 +
98,599,381 + split-exact 41,942,626 = 208,817,578).

**petersen_39 closes exactly.** Single-worker depth-first run:
368,072,359,571, the repository's stated count, width 0, after
136,680,243 expansions in 693.7 s (11.6 min wall), peak RSS
142.4 MB, stack never above ~21 entries. Spot subtree at depth 19:
frontier value 1,048,544 versus brute-force enumeration 1,048,544.
This case also calibrates the schedule honestly: the count is
~1,760 times the petersen_28 count and needed ~106 times the
expansions, and its width fell slowly for most of the run before
collapsing near the end — depth-first widths are back-loaded,
because whole subtrees must finish before their width leaves the
total.

## petersen_50: outcome — interval narrowed 27%, count not closed

The exact count did **not** close within budget. The final rigorous
interval is

**[699,497,138,009,147, 703,473,996,819,983], width 3,976,858,810,836,**

which is strictly narrower than the prior
[698,342,755,629,882, 703,790,474,857,480] (width 5,447,719,227,598)
by 27.0%, and lies strictly inside it — so the two independent
campaigns corroborate each other, and the count is now pinned to
0.57% relative width. The stage-by-stage accounting:

**Stage 1, split and depth-first workers.** Splitting at depth 6
counted 211,070,361,143,360 portfolios exactly and left 52 prefix
subtrees of combined width 84,854,332,298,872. The two workers then
ran 456,500,000 and 440,750,000 depth-first expansions (897,250,000
total, ~3,880 s wall) at a peak of 166 MB RSS each and stack sizes
never above ~31, counting a further 173,566,396,242,754 portfolios
exactly (combined exact constant 384,636,757,386,114), before the
run was terminated by an external SIGTERM — not by its 5,400 s
budget and not by memory. Their checkpoints survived intact and
their accounting identities (exact + sum of stack bounds = floor /
ceiling) verify exactly. As petersen_39 predicted, depth-first
width is back-loaded: the workers' combined interval at that point,
[630,849,041,851,724, 715,526,688,518,671], was still wide, because
each worker was deep inside individual subtrees whose widths leave
the total only when the subtree finishes.

**Stage 2, best-first refinement of the checkpoint frontier.** The
56 checkpoint frontier nodes were then expanded widest-first —
attempt_50.py's own schedule, applied on top of the depth-first
progress instead of from the root. Round 1 (in-RAM heap capped at
2,000,000 live nodes, 2,003,412 expansions, 35 s) reached width
5,947,627,999,739, with a depth-48 frontier node re-counted by plain
distribution-free recursion (1, inside its stored bounds [0, 1]).
Round 2 (disk-backed spill, refine2.py; 2,159,184 further
expansions, 76 s) reached width 4,899,998,807,447 with 4,156,809
live nodes of which 2,900,005 were spilled to disk. Round 3
(resumed from the spill state, 15,781,104 further expansions,
1,204 s) reached the final width 3,976,858,810,836 with exact
constant 427,102,461,235,926 and 19,851,001 live frontier nodes
(1,350,957 in RAM, 18,500,044 on disk in `spill/`, 709 MB).

**Peak memory, honestly.** The depth-first stage met the design
goal easily (166 MB per worker against a 1.5 GB target — the
contrast with the OOM-killed 15M-expansion best-first probe is the
point of the exercise). Refinement round 2 peaked at 1,889,968 KB,
above the 1.5 GB target, while first sorting the already-oversized
2M-node heap inherited from round 1; rounds 1 and 3 peaked at
1,254,164 KB and 1,121,344 KB. No run came near the machine's
7.9 GB and nothing was OOM-killed.

**Final audit.** `verify_final.py` streamed the entire saved
frontier — RAM heap plus every spill file, all 19,851,001 nodes —
and re-summed every bound: exact constant 427,102,461,235,926 plus
the node lower bounds equals the floor 699,497,138,009,147, and
plus the upper bounds equals the ceiling 703,473,996,819,983,
exactly. A deepest frontier node (depth 48) re-counted by plain
recursion gave 1, inside its stored interval [0, 1].

**Why the count did not close.** Best-first width is now falling
by a factor ~0.81 per ~16M expansions, but the live frontier grows
by roughly one node per expansion, so exhausting it is a far larger
campaign than this budget: the refinement would have to resolve
~2×10^7 growing frontier subtrees, and the depth-first experience
(897M expansions without exhausting even one depth-6 prefix
subtree) shows individual subtrees at this scale are themselves
large. The binding constraint is total node throughput
(~1.3–5.7×10^4 expansions/second in Python depending on stage),
not memory — memory stayed bounded by design throughout, which was
the defect that killed the prior strategy. (Throughput ranged from
~1.3×10^4 expansions/second in the spill-heavy refinement round to
~2.3×10^5/second aggregate in the depth-first stage.) The three
refinement rounds ran under successive caps of 2,400 s, 1,800 s, and
1,200 s, recorded with all other budget data in
`checkpoints_summary.json`. The saved frontier
state makes the campaign resumable exactly where it stopped
(below), and the same scripts in a compiled implementation, or with
a second pair grid added to the node bounds, are the plausible
routes to closure.

## Classification

**Proved** (exact, by exhausted finite arguments replayable from the
scripts): the petersen_28 count 208,817,578 and the petersen_39 count
368,072,359,571 under this counter (both matching the repository's
receipts, each with a brute-force spot re-verification of a
distribution-exact subtree). **Computed exactly as rigorous
bounds**: every stage interval for petersen_50 above, culminating in
[699,497,138,009,147, 703,473,996,819,983] (width 3,976,858,810,836,
0.57% relative), end-to-end audited against its saved frontier.
**Open**: the exact petersen_50 feasible count itself, now known to
lie in that interval.

## How to resume

The full frontier state lives in `spill/` (`manifest.json` with the
exact constant, floor, ceiling, and expansion count; `ram_heap.pkl`;
and the `spill_*.pkl` node files). Continue with
`python3 refine2.py --repo ~/workspace/research/perfectpower
--resume-spill --target-width <width> --max-seconds <seconds>`.
The global interval is at all times the exact constant plus the
sums of all live nodes' bounds, in RAM and on disk alike. The two
depth-first worker checkpoints
(`petersen_50_checkpoint.json_w0` / `_w1`) are an alternative,
independent resume point via `bounded_count.py --resume`.

## Files

`bounded_count.py` (depth-first counter with `--workers /
--split-depth` fork-split mode), `refine.py` (in-RAM best-first
refinement), `refine2.py` (disk-backed refinement with
`--resume-spill`), `verify_final.py` (the end-to-end audit),
`checkpoints_summary.json` (budget, validation, all stages, final
audit), `petersen_28_bounded_results.json`,
`petersen_28_parallel_results.json`,
`petersen_39_bounded_results.json`,
`petersen_50_refined_results.json`,
`petersen_50_refined2_results.json`,
`petersen_50_refined3_results.json`, `petersen_50_final_audit.json`,
`petersen_50_checkpoint.json_w0` / `_w1`, `spill/` (resumable
frontier state), `petersen_50_run.log`, `petersen_50_refine.log`,
`petersen_50_refine2.log`, `petersen_50_refine3.log`, and this
report. The repository at `~/workspace/research/perfectpower` was
read, never edited; this package is submitted on the branch `muse/planning-bounded-count`.


## Postscript (added when submitting)

After this report was written, the saved frontier was resumed once more (`resume_run.log`, ~5,000,000 further expansions over ~90 minutes before the machine restarted). The width moved from 3,976,858,810,836 to about 3,976,817,002,588 — confirming the report's diagnosis directly: at this frontier shape the width decays far too slowly for best-first refinement in Python to close the count, and the binding constraint is node throughput, not memory. The spill state (not included here; ~700 MB) remains exactly resumable with the command in the report.
