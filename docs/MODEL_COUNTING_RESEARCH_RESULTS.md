# Publication-driven exact counting: 0.10.1

The new counter improves on PerfectPower 0.10.0, but does not establish general
benchmark superiority. On the complete 200-instance MC2025 Track1 public draft,
at five seconds per solver, it produces 13 exact answers versus 11 for the prior
counter, 21 for deterministic Ganak 2.8.0 and 21 for the archived 2024 D4 entry.
There are no lost solves against our prior counter in this screen. A completed
answer is distinguished from an independently reference-confirmed answer.

## What research changed in the implementation

[The research protocol](MODEL_COUNTING_NEXT_PROTOCOL.md) links the primary
papers and identifies precisely which algorithms were implemented. The main
change inspired by Lagniez and Marquis's AAAI 2014 preprocessing paper is a
signed equivalence quotient derived from binary-clause implication SCCs. Its
counting justification uses unique extension, as discussed in Lagniez, Lonca
and Marquis's IJCAI 2016 definability paper. A removed equivalent variable has
one extension, so it must not receive a free-variable factor of two.

Dechter's bucket elimination framework motivates a bitset primal-graph planner
for the existing exact sum/product evaluator. Occurrence-queue unit propagation
and direct dense variable maps reduce repeated scanning. These are general
formula transformations and planning changes; there are no instance-name
special cases and reference answers are never used by the counter.

[The counting invariants](MODEL_COUNTING_INVARIANTS.md) formalize propagation,
the equivalence quotient, component products and elimination. The native engine
still uses arbitrary-size integer arithmetic and retains its explicit limits.
Original-variable conditioning, lexicographic ranks and seeded sampling remain
available. This release does not add Lean certificates for the native counter,
general definability elimination, symmetry-aware caching, or a full D4 compiler.

## Complete MC2025 primary screen

| Solver | Exact / 200 | Timeouts | Work limits | PAR-2 seconds |
|---|---:|---:|---:|---:|
| PerfectPower 0.10.1 | 13 | 177 | 10 | 1881.904 |
| PerfectPower 0.10.0 | 11 | 179 | 10 | 1899.986 |
| Ganak 2.8.0, `--prob 0` | 21 | 179 | 0 | 1816.734 |
| Archived D4 2024 | 21 | 179 | 0 | 1808.400 |

PAR-2 assigns actual elapsed wall time to exact answers and twice the five-second
deadline to every other outcome. PerfectPower saves 18.082 seconds, approximately
0.95%, against its prior aggregate PAR-2. Its solved fraction rises from 5.5% to
6.5%; both references reach 10.5%. A conditional speedup on jointly solved cases
does not erase the many timeouts. Full outcomes are retained in
[`next_mc2025.json`](../receipts/model_counting/next_mc2025.json).

| New solve | New wall seconds | Prior at five seconds | Ganak | Archived D4 |
|---|---:|---|---|---|
| `mc2025_track1_042.cnf` | 0.303 | Timeout | Exact, 0.282 s | Exact, 0.059 s |
| `mc2025_track1_076.cnf` | 4.167 | Timeout | Timeout | Timeout |

The second row's primary count is one. Its reference timeouts are retained;
longer independent validation is reported separately below and cannot replace
the primary ranking.

## Dataset overlap

All 200 MC2025 files were retained. Raw file hashes did not match MC2024, but a
normalized audit found **52 repeated formulas** after ignoring comments,
whitespace, clause/literal order, duplicate clauses/literals and tautologies.
It preserves the declared variable universe. This is a materially stronger
overlap check than byte hashes alone.

| Secondary stratum | Instances | New exact | Prior exact | Ganak exact | D4 exact |
|---|---:|---:|---:|---:|---:|
| Normalized MC2024 repeat | 52 | 3 | 3 | 3 | 4 |
| No normalized MC2024 match | 148 | 10 | 8 | 18 | 17 |

Both gained solves lie in the second stratum. **No normalized match does not
prove semantic independence, different generation families or absence of
variable-renamed repeats.** These strata are secondary analyses after an overlap
audit; the full 200-case ledger remains the primary evaluation. The audit and
analysis are in `next_overlap.json` and `next_overlap_analysis.json`.

## Regression, repeat trials and independent validation

The 11 cases previously solved at ten seconds were each compared three times
against the prior counter and both references. All 33 new-counter answers match
the references. Aggregate new wall time is 14.317 seconds versus 35.049 for the
prior counter. MC2024 case 057 has median 0.242 versus 6.707 seconds, a 27.75-fold
speedup over our prior implementation, not a speedup claim over every reference.

The initially proposed strict 10% per-case timing regression gate was **not
met**: case 083 measured 0.0635 versus 0.0555 seconds, about 14.4% slower. Case
118 was also approximately 9.6% slower. These small absolute differences are
retained as measured regressions; the aggregate improvement does not establish
absence of per-case overhead. The receipt is `next_regression.json`.

The complete MC2024 engineering comparison, with both PerfectPower versions at
five seconds, finishes with **12 versus 10 exact solves**, 181 versus 183
timeouts, and seven work limits each. No prior solve is lost. New solves are
020 and 057; the latter was already solvable by the prior counter at ten seconds,
so this is a latency gain rather than a new mathematical capability. PAR-2 is
1887.481 versus 1905.007 seconds, a 17.526-second saving (approximately 0.92%).
All 12 new exact answers agree with independently completed reference answers
from the historical ten-second ledger. Those historical outcomes validate
counts only; they do not enter the new five-second speed ranking. The complete
paired receipt is `next_mc2024.json`, with validation in
`next_historical_agreement.json`.

All 13 MC2025 solves reproduce in all three five-second repeat trials: **39 of
39 new-counter attempts finish exactly**. Both gains, 042 and 076, repeat in
every trial. On this selected 13-case scope, the prior counter has 33 exact
answers, Ganak 34 and D4 27. That subset was selected by our own completed
answers and is **not a fair replacement for the full-corpus ranking**. Ganak
case 027 finishes in one trial and times out in two; those timeouts remain.
See `next_mc2025_repeated.json`.

At a separate thirty-second validation budget, deterministic Ganak independently
confirms case 076's exact count of **one**, taking 20.243 seconds. The new counter
takes 4.114 seconds; the prior counter times out and D4 exits with an error after
16.529 seconds. This validation does not replace those references' five-second
timeouts. All 13 MC2025 new-counter answers now have independent reference count
confirmation, and no exact-count disagreement is observed. The receipt is
`next_reference_validation.json`. D4's error log reports `std::bad_alloc` under
the declared address-space cap; that error is not a valid D4 speed comparison.
All three thirty-second repeats independently agree on the count. Medians are
**4.551 seconds for the new counter and 20.149 seconds for deterministic Ganak**,
a **4.43-fold speedup on this one explicit instance**. The prior counter times
out in every trial; D4 has an allocation error in every trial. This is a stable
narrow advantage over the pinned Ganak version under this budget, not a
whole-corpus advantage. See `next_reference_repeated.json`.

The paired empirical bootstrap on the complete MC2025 screen gives the
two-solve gain over the prior counter a 95% interval of **[0, 5]**. The PAR-2
seconds saved interval is **[1.300, 41.804]**. These are descriptive intervals
over resampled corpus instances. Against Ganak, the observed coverage difference
is minus eight, with interval **[-14, -2]**. A 1.014-fold conditional geometric
speedup on jointly solved cases does not establish superiority over Ganak:
its greater full-corpus coverage and lower PAR-2 remain decisive here.

The extra twenty startup-sensitive trials retain 120 exact answers per version.
Case 083 medians are 0.0573 versus 0.0564 seconds, approximately 1.6% slower;
the largest median slowdown among these six cases is approximately 3.3% on
case 082. Thus the initial 14.4% estimate is not reproduced at that magnitude.
This post-hoc check does not retroactively pass the original strict gate or
establish zero overhead. Every initial and supplemental observation is retained
in `next_startup_repeated.json`.

## Which features account for the gain?

Five variants are measured on four explicitly selected solved cases, three
times each at ten seconds. Removing a feature keeps the other three new features.
All completed counts match the original full-counter count.

| MC2025 case | Full | Without equivalences | Without graph planner | Without occurrence queue | Without direct dense map |
|---|---:|---:|---:|---:|---:|
| 042 | 0.309 s | 1.348 s | 3.214 s | 0.318 s | 0.390 s |
| 044 | 0.069 s | 0.071 s | 0.200 s | 0.068 s | 0.069 s |
| 076 | 4.182 s | 3/3 timeouts | 4.071 s | 4.636 s | 5.953 s |
| 160 | 0.902 s | 0.873 s | 1.217 s | 0.860 s | 0.895 s |

Times are medians of three exact trials; the timeout cell has no completed
answer. Equivalence substitution is essential to the observed solve of case
076 under this budget. Graph planning is the main improvement on cases 042 and
044. Direct renumbering and the propagation queue also reduce time on case 076.
Features are not monotonically beneficial: removing the planner slightly
improves case 076, and removing some other features slightly improves case 160.
These observations motivate measuring routing overhead rather than assuming
every reduction helps every formula. They do not prove causal effects outside
these four selected formulas. See `next_ablation.json` and its source variants
in the detailed evidence. The ablation validator audits all 60 outcomes.

## Correctness and package validation

All 16 focused counting, comparison and harness tests pass, including large
analytic branching counts, signed equivalences emerging after a decision,
original-variable locks and fresh rank/select inverses. A portable native
exhaustive harness checks 1,000 seeded small formulas under AddressSanitizer and
UndefinedBehaviorSanitizer; it reports no count mismatch or sanitizer finding.
LeakSanitizer is disabled, so this is not a leak check. These checks exercise
the implementation; they are not a formal proof of all executable paths.

The 0.10.1 wheel installs outside the checkout and compiles its packaged native
source using a fresh temporary cache. It returns the independently known
17,528,422,464 count on MC2024 case 118. Seeded unconditional and conditional
samples pass fresh-counter rank inverses. Packaged native bytes match the
measured source. See `next_installation.json`; the wheel SHA256 is
`3e766b2fbcb2dc73ffc43e181fbe199f02eea70a78b1908f04f701502203725e`.

The release audit verifies **1,804 solver/variant outcome logs** across full
screens, regressions, repeats, validation and ablations. All completed answers
agree where comparable. No timeout, work limit or allocation failure is removed
from its declared scope. Validation summaries are in `next_validation.json`.

## Limits and the next acceptance criterion

These are practical latency experiments under six GiB virtual-address-space
limits, not official competition rankings. D4 is an archived 2024 submission,
not a current 2026 champion. Compilation is warmed outside timing; fresh Python
process startup, parsing, construction and counting are included. One shared
exclusive lock prevents overlapping benchmark invocations, and solver order is
rotated. The host is shared infrastructure, not an isolated dedicated machine.

Bootstrap intervals resample paired instances, keeping each instance's repeated
trials together. They describe this empirical corpus and do not certify
out-of-distribution dominance. Repeats select every case solved by the new
counter, including slower cases; ablations are post-selection mechanism tests,
not a second blind holdout. Native width, work, depth and input limits remain.

The next performance claim should require a source-frozen full declared corpus,
independent exact-count agreement, no hidden failures, repeatable coverage/PAR-2
gains against the prior version and relevant current reference implementations,
and disclosed per-case regressions. Separator selection and stronger SAT-based
decomposition from the Decision-DNNF literature are promising hypotheses, not
promised wins. None of the observed CNF gains establishes a DynaComp gain.

## Reproduction and evidence

The prior source is commit `478bca899da6b032eb486eaaa2704eef621ea303`.
MC2025 archive and every instance are pinned in
`data/model_counting/mc2025_manifest.json`; MC2024 and reference binaries retain
their existing manifests. Detailed logs are delivered separately from public
Git; public receipts contain counts, statuses, wall times and log hashes.
Historical 0.10.0 receipts still refer to their original sources: audit them
using `scripts/check_model_counting_receipts.py --source-root PRIOR_CHECKOUT`.

Use the CLI argument help in `compare_model_counting.py` to provide corpus,
reference binary and prior-checkout paths. Outputs must be fresh. The runner
hashes and checks sources and binaries before every measurement and refuses
concurrent runs. `scripts/check_model_counting_comparison.py` audits the complete
scope, source identity, count agreement and optional original logs.

For example, run from a clean checkout, with `PP_DATA` pointing to a writable
external directory and an available C++17 compiler and Boost headers:

```sh
git worktree add --detach "$PP_DATA/prior" 478bca899da6b032eb486eaaa2704eef621ea303
python scripts/fetch_model_counting.py "$PP_DATA/mc2025" --manifest data/model_counting/mc2025_manifest.json
python scripts/fetch_model_counting_references.py "$PP_DATA/references"
PYTHONPATH=python python python/compare_model_counting.py \
  --manifest data/model_counting/mc2025_manifest.json --corpus "$PP_DATA/mc2025" \
  --previous-root "$PP_DATA/prior" --ganak "$PP_DATA/references/ganak" \
  --d4 "$PP_DATA/references/d4" --timeout 5 \
  --output "$PP_DATA/reproduction.json" --log-directory "$PP_DATA/reproduction_logs"
PYTHONPATH=python python scripts/check_model_counting_comparison.py "$PP_DATA/reproduction.json" \
  --manifest data/model_counting/mc2025_manifest.json --previous-root "$PP_DATA/prior" \
  --logs "$PP_DATA/reproduction_logs"
PYTHONPATH=python make model-count-test
g++ -std=c++17 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer \
  -I "$PP_CNF_BOOST_INCLUDE" native/model_counting/test_exhaustive.cpp \
  -o "$PP_DATA/counter_sanitizer"
ASAN_OPTIONS=detect_leaks=0 "$PP_DATA/counter_sanitizer"
```

Receipts record source and binary hashes, not an assertion that another host
will produce identical elapsed times. Run this serially without other heavy
work. Use `--names` only for explicitly declared supplemental scopes, retaining
the full-corpus receipt as the primary result.
