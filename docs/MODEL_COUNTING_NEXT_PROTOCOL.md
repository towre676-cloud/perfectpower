# Research-driven counter comparison

## Research and implemented scope

The 0.10.0 baseline is commit `478bca899da6b032eb486eaaa2704eef621ea303`.
This effort implements three general changes: occurrence-queue unit propagation,
signed literal equivalence substitution through binary implication SCCs, and
bitset primal-graph planning for exact bucket elimination. Dense renumbering now
uses a direct map. The exact integer arithmetic, full-key caches, factor-width
and work budgets, and original-variable conditioning semantics remain enforced.
No reference solver supplies answers to PerfectPower's implementation.

Primary literature read for this effort:

* Lagniez and Marquis, **Preprocessing for Propositional Model Counting**,
  AAAI 2014, 2688–2694. [Paper](https://ojs.aaai.org/index.php/AAAI/article/download/9116/8975).
  It motivates count-preserving equivalence replacement. Our SCC detector only
  finds equivalences implied by binary clauses; it does not implement their full
  BCP-based detector, gate replacement, vivification, or SAT backbone computation.
* Lagniez, Lonca and Marquis, **Improving Model Counting by Leveraging
  Definability**, IJCAI 2016, 751–757.
  [Paper](https://www.ijcai.org/Proceedings/16/Papers/112.pdf).
  Its unique-extension criterion informs the counting invariant. We do not
  claim to implement its general definability partition or elimination system.
* Dechter, **Bucket elimination: A unifying framework for reasoning**,
  Artificial Intelligence 113 (1999), 41–85.
  [Author copy](https://ics.uci.edu/~dechter/publications/r76A.pdf).
  It informs the separation of induced-width planning and exact sum/product
  evaluation. The new bitset planner replaces expensive repeated factor scans;
  it uses greedy minimum degree, not an optimal treewidth algorithm.
* Lagniez and Marquis, **An Improved Decision-DNNF Compiler**, IJCAI 2017,
  667–673. [Paper](https://www.ijcai.org/proceedings/2017/0093.pdf).
  It explains the remaining importance of separator decisions, SAT reasoning,
  and dynamic decomposition. These are future implementation directions, not
  features added by this effort. Existing component products are retained.
* **Symmetric Component Caching for Model Counting on Combinatorial
  Instances**, AAAI 2021.
  [Author copy](https://www.cs.toronto.edu/~meel/Papers/aaai21-bdsrm.pdf).
  Symmetry-aware caching is a separate candidate requiring exact canonicalization
  and overhead measurements; it is not implemented or claimed here.

The previously supplied arXiv `2408.07499` is Tom Leinster's **Galois Theory**.
It provides mathematical background, not a demonstrated general #SAT speedup.
Wilf's generating functions remain relevant to structured counting; neither
publication implies superiority on arbitrary competition CNFs.

## Counting invariants

For declared universe V, free variables contribute `2^f`; forced variables
contribute one extension. Disjoint components multiply and decisions sum.
If the implication graph proves `y = x` or `y = not x`, removing y contributes
one extension, not two. SCCs containing a literal and its negation refute the
formula. Conditional queries apply original-variable assumptions before
substitution, preserving select/rank semantics without a public renumbering.

## Protocol fixed before evaluation

1. Freeze native source, Python counter, both runners, prior checkout sources,
   compiled native libraries, reference binaries and dataset manifest hashes.
   The runner rejects changes during measurement, takes a shared serial lock,
   refuses existing receipts, and checkpoints every completed instance.
2. Run the **11 previously solved MC2024 instances**, without omitting losses,
   three times each at ten seconds per solver, against the prior version,
   deterministic Ganak 2.8.0 and archived D4 2024. These are development
   regressions; their results do not count as unseen evaluation.
3. Run **all 200 MC2025 Track1 public-draft instances**, once each, with all four
   solvers at five seconds and 6 GiB virtual-address-space limits. Parsing,
   startup and construction count toward subprocess wall time; native
   compilation is warmed separately. The archive is fetched from the public
   link provided by [the organizers](https://mccompetition.org/past_iterations.html).
   Its SHA256 is `ee097e79d8b1c863f8e57a7db8433451201c47fce82f912e4a011351c8a537d2`.
   All 200 files are retained. None has a byte-identical SHA256 to MC2024;
   the subsequent normalized audit finds 52 repeats. The remaining 148 are not
   certified semantically or family independent. Dataset is explicitly a draft.
4. Run **all 200 MC2024 instances**, with new and prior counter, at five seconds.
   This is a paired engineering comparison on known data, not a blind holdout
   and not a comparison of five-second results to the old ten-second ranking.
5. Counts must agree wherever multiple solvers finish. Report solved totals,
   gains/losses and PAR-2 (actual wall time for exact answers, twice the deadline
   otherwise). All unsupported inputs, work limits, errors and timeouts remain
   in denominators. Repeat any apparent reference advantage on the new corpus
   before describing it as a stable speed advantage; label the selected repeats
   as descriptive, not a second independent holdout.

Supplemental validation rule added during the screen, after observing case 076:
every new 2025 answer lacking a completed Ganak or D4 reference answer receives
a separate thirty-second comparison for independent count validation. Selection
depends on reference completion, not favorable timing. This was not part of the
original premeasurement protocol. The longer measurements are validation only;
they do not replace failures or alter the five-second primary ledger.

Post-screen mechanism analysis removes one feature at a time on explicit cases
042, 044, 076 and 160, with three ten-second trials per variant. This selection
is descriptive and cannot establish an independent performance advantage.
After the initial three-trial regression check showed a 14.4% slowdown on case
083, all six original regression cases with sub-100-millisecond medians
(079–083 and 118) receive twenty one-second paired startup-sensitive trials.
This additional check is post hoc; the initial regression and unmet strict
per-case gate remain disclosed.
After Ganak confirmed case 076 at the thirty-second validation budget, the same
four-solver, thirty-second comparison is repeated three times for that explicit
case. This tests a narrow observed reference advantage; it does not modify the
full-corpus primary ranking or create an independent holdout.

Ganak runs with `--prob 0`. D4 is the pinned 2024 submission already used in the
baseline report, **not a current 2026 champion**. Global superiority requires
greater coverage and a speed advantage on a declared scope against appropriate
current references; that conclusion is not guaranteed by these changes.
Detailed local logs remain outside public Git; portable receipts include counts,
statuses, elapsed times and log hashes. Historical 0.10.0 receipts remain bound
to their original source and must be validated using that checkout.
