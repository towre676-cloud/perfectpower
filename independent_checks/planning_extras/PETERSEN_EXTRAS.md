# Petersen extras: petersen_50 maximiser count, petersen_39 closure attempt

Companion to the planning recount change (`independent_checks/planning/`, PR #5),
which proved the petersen_50 optimum 16537 but did not count its
maximisers, and bracketed petersen_39's count without closing it.
All arithmetic is exact integer arithmetic; all tooling was validated
on solved cases before any new number was trusted. Committed here on
the branch `muse/planning-extras-tie-count`, as new files under
`independent_checks/planning_extras/`, for review by pull request
against the repository's default branch; no existing repository file
is changed.

## PROVED

**The petersen_50 optimum 16537 is attained by exactly ONE feasible
point.** The counter (`tie_count.py`) reuses wave one's exact bound
machinery unchanged (same efficiency order, per-resource
fractional-knapsack tables, Lagrangian prices snapped to integers at
scale 4096 — validity by weak duality for any nonnegative prices),
re-aimed at the fixed proved target: prune iff `val > OPT` or
`val + bound < OPT`; a node at `val == OPT` contributes exactly one
optimal point (its all-exclude completion; all profits are positive,
so no other completion of that node can be optimal). Exhausted
search: **506,701 nodes, 3.4 s, tie count = 1**. Together with wave
one's proof, the petersen_50 maximiser is unique (it is the receipt
point, replayed as feasible in wave one).

**petersen_39's optimum is 10618 and its maximiser is also unique.**
Wave one's `prove_optimum`, run on petersen_39 here, exhausts
(234,141 nodes) at optimum 10618, independently confirming the
published value; the tie counter then exhausts (197,537 nodes) at
tie count 1, independently confirming the receipt's stated
`maximizer_count: 1`.

## Validation of the tooling (before any new number)

- Tie counter on petersen_15 / 20 / 28: tie count 1 in each case
  (145 / 123 / 328 nodes), matching the receipts' stated
  maximiser counts.
- Independent brute-force enumeration of petersen_15 and petersen_20
  (all 2^n subsets): tie counts 1 and 1, and feasible counts 22,158
  and 422,601 — matching both the receipts and wave one's recount.
- Frontier machinery: wave one's original `frontier_interval` closed
  petersen_28 exactly at 208,817,578 in 974,960 expansions (the same
  expansion count wave one reported), and the monitored copy used
  for the petersen_39 run reproduced the original's result
  field-for-field apart from timings. At 1,500,000 expansions the
  petersen_39 run reproduced wave one's bracket
  [367416693865, 368263629080] exactly, then continued past it.

## COMPUTED (petersen_39 count: narrowed, NOT closed)

The closure run (pair (0,3) by wave one's criterion; budget
30,000,000 expansions / 5400 s / RSS cap 2.6 GB) was stopped by the
**memory guard** at **6,145,000 expansions** (504 s; 5,117,375
frontier nodes still live; 341,450,493,494 portfolios already counted
exactly in collapsed subtrees; peak RSS 2,600,344 KB at the cap).
Final rigorous interval:

**[367,756,900,510, 368,192,477,002]**, width **435,576,492**
(≈ 0.118 % of the count).

That is ≈ 1.94× narrower than wave one's bracket
[367416693865, 368263629080] (width 846,935,215), and it still
**contains the stated count 368,072,359,571** — so the run is
consistent with the repository's number but does **not** confirm it;
agreement can only be claimed at width zero. The binding constraint
was memory, not the expansion budget: the best-first heap retains
≈ 0.83 nodes per expansion, and the width decay per expansion had
fallen by more than an order of magnitude between 0.75M and 6.1M
expansions (the tail is millions of small-width nodes), so simply
raising the cap on this 7 GB machine would have narrowed the
interval further without closing it — the same wall wave two met on
petersen_50, at smaller scale. Closing petersen_39 needs the
memory-bounded (DFS / disk-backed) frontier variant, not more heap.

## OPEN

- The exact petersen_39 feasible count: open, inside the rigorous
  interval above.
- The exact petersen_50 feasible count remains open in its wave-one /
  wave-two interval; it is being attacked separately and is not
  duplicated here.

## Files

- `tie_count.py`, `tie_count_results.json`, `tie50_run.log` —
  maximiser counting (petersen_15/20/28 validation, petersen_39,
  petersen_50).
- `optimum39_proof.json` — independent optimum proof record for
  petersen_39 from wave one's `prove_optimum`.
- `frontier39.py` (driver), `frontier39_core.py` (the monitored
  frontier copy, generated verbatim from `attempt_50.py` with three
  stated insertions), `frontier39_results.json`,
  `frontier39_run.log`.
