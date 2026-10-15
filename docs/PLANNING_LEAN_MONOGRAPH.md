# Lean foundations and original Petersen planning statements

The original October 12 extension adds **59 checked theorems** in `PerfectPower/PlanningDiagram.lean` and `PerfectPower/PetersenPlanning.lean`, compiled with the repository's pinned Lean 4.20.0. Every theorem's assumptions are inspected. There is no `sorryAx`, user-declared axiom, `native_decide`, or native-reflection axiom. Concrete arithmetic is accepted by ordinary kernel reduction. General proofs use only Lean's standard logical axioms where listed in the axiom receipt.

The new proof library establishes the decision-diagram counting mathematics, actual original-model conditional counts **16,777,216** and **512**, original feasibility and profit **16,537** of the retained optimizer witness, and disjoint coverage and aggregation for the literal retained 176-leaf partition. These are new formal statements, not reruns of the C++ population kernel. The full unrestricted population **702,508,860,122,761** remains independently reproduced computationally; its concrete C++ diagram-to-original-predicate correspondence is not yet a Lean theorem. The full-instance statement is deliberately not obtained by assuming its 176 feasible leaf counts.

## A finite population with exact original identity

For a Boolean predicate `f` on bit lists, `census n f` branches on the first coordinate and adds its zero and one populations. `assignments n` constructs the complete list of length-n bit strings. `census_enumerates` and `census_cardinality` identify the recursive count with the number of accepted strings in this literal list. `assignments_multiplicity` proves that a bit list of length n appears exactly once, and a bit list of any other length appears zero times. Thus the finite domain contains original assignments with their multiplicities, not distinct resource vectors, graph paths, or projected auxiliary choices.

`census_bound` proves the count is at most \(2^n\). `census_skip` proves that a predicate ignoring r coordinates contributes \(2^r\) copies of its n-coordinate population. This is the factor needed by a reduced diagram whenever an edge skips variables. `census_congr_length` permits replacement by a predicate proved equal only on the actual length-n domain.

## The diagram semantic kernel

The proof representation has false and true terminals, binary decisions, and explicit skip nodes. `Fits` records the number of Boolean coordinates represented by each node. The arithmetic evaluator returns zero for a false terminal, \(2^n\) for a true terminal, the sum of child weights for a decision, and \(2^r\) times the child's weight for an r-variable skip.

`weight_correct` proves that this arithmetic evaluator equals the finite accepted-assignment cardinality for every well-formed diagram. `weight_bound` inherits the \(2^n\) bound. `reduce_equal_branches` proves that replacing identical decision children by a one-variable skip preserves the represented predicate. The proof uses structural induction; no truth table for the 50-project model is assumed.

`threshold_correct` proves that a threshold diagram built from an arbitrary list of nonnegative integer resource costs accepts exactly the assignments whose weighted sum is within capacity. The selected branch is false if its project alone exceeds the remaining capacity; otherwise the capacity is reduced by that project's cost. `threshold_count` connects the diagram's weight to the original inequality's population.

`cofactor_correct` proves the semantics of fixing the next Boolean coordinate. `intersect_correct` proves the Boolean conjunction of two diagrams on the full finite domain, and `intersect_count` connects this construction to accepted-assignment cardinality. This proof representation is a pure structural reference. It does not implement the C++ unique-node hash tables or certify their pointer indices. Structural sharing and storage optimization do not enter these theorems' assumptions.

## Original Petersen source and conditional proofs

The literal 50-project cost rows, capacities and profits are present in the checked source file. `scripts/check_planning_lean.py` independently reads the original public OR-Library tokens and checks that all three literal tables match exactly. It also checks the retained partition addresses, free-variable counts and numerical count labels against the original receipt, then records their hashes. The theorem compiler checks the mathematics of those literals; the source-binding receipt documents their provenance.

`dot_prefix` proves exact separation of fixed prefix use from remaining use. `feasible_prefix` proves that subtracting a feasible original prefix gives the same original-model predicate on its remaining coordinates. `dot_bound` proves that selecting some nonnegative-cost projects cannot exceed the sum of all their costs.

For the zero 26-project prefix, the remaining resource totals are **449, 347, 252, 200, 192**, all within the original capacities. `zero_prefix_original_population` therefore proves that all \(2^{24}=16,777,216\) completions are feasible, using the literal original predicate.

For prefix `11111111111111101111010111`, the residual capacities are **327, 213, 91, 4, 181**. `forced_zero_implication` proves a general resource implication: if a project's cost in the guard resource exceeds its capacity, a feasible assignment must omit that project. Consequently another resource's use is bounded by the sum of its costs on the remaining permitted projects. The concrete `high_guard_bounds` proves that the fourth resource inequality implies all other residual inequalities. `high_guard_semantics` reduces the actual original problem to this single checked inequality. Its threshold diagram has kernel-evaluated weight **512**. `high_prefix_original_population` connects that weight back to the literal original 50-project predicate, rather than merely stating the weight of a supplied diagram.

`optimizer_original_feasibility` and `optimizer_original_profit` check the exact retained 50-bit witness against all five original inequalities and its original profit row. Both arithmetic facts require no axioms. They establish witness feasibility and profit; global optimality and uniqueness still have the separate exact C++ target-enumeration evidence, not a new Lean global optimization proof.

## Actual partition and aggregation

`retainedPartition` is the actual original-coordinate binary tree from the population receipt. Kernel checks prove that every split coordinate is within 0–49, no coordinate is fixed twice along a branch, it has 176 leaves, and its normalized root-to-leaf assignments agree exactly with the retained original fixed masks and values. The sorting used by this check is a transparent structural insertion sort, so ordinary kernel reduction suffices.

`partition_disjoint_cover` proves pointwise that every original assignment contributes exactly once through any such binary tree. Specializing to the concrete tree gives `original_disjoint_cover`. `partition_aggregation` proves that aggregating an arbitrary accepted-assignment indicator through the tree preserves its finite population. `original_partition_aggregation` specializes this law to all 50 coordinates and the literal original five-constraint predicate. This is an unconditional semantic aggregation theorem, not a theorem with native leaf populations as premises.

Separately, kernel arithmetic proves that the **supplied numerical leaf count labels** sum to 702,508,860,122,761 and their cube sizes sum to \(2^{50}\). These arithmetic statements are useful but deliberately distinct from a theorem identifying each numerical leaf label with the accepted cardinality of its cube. The latter identification for every root leaf is currently provided by the independent computational receipt.

## Reproduction and remaining precise boundary

Run `make planning-population-lean` with Lean 4.20.0 on PATH, or set `PLANNING_LEAN` to its executable. The checker builds both modules in a temporary directory using only the pinned standard library, then prints and inspects all 59 theorem axiom sets. It writes `receipts/planning/independent/lean.json`, including source hashes, input binding, compilation outcomes and explicit scope flags. The whole existing Mathlib-dependent repository was not rebuilt for this standalone check.

The managed build environment needed the optional `--namespace-path-shim` flag: its `getpid` uses a PID namespace while `/proc` exposes host process identifiers. The small published compatibility source changes only the current executable's location lookup from `/proc/<current-pid>/exe` to `/proc/self/exe`. The pinned Lean executable and kernel remain unchanged. Ordinary installations do not need this flag. This environment repair has no role in proof evaluation or accepted arithmetic.

What remains for a full unrestricted kernel theorem is a verified bridge from the concrete 9,190,151-node C++ DAG and its original five threshold constructions to the proved diagram semantics, followed by source-bound evaluation of its concrete weight. A checked DAG certificate should establish every child index, skipped level, canonical-node reuse and conjunction result against those original threshold functions. The current 59 proofs supply the finite semantics, threshold, cofactor, intersection, reduction, counting and partition identities needed by that bridge. They do not declare the bridge complete. A formal full optimizer theorem would similarly need to certify the target enumerator's pruning bounds and complete branch coverage.


## October 15 construction-certificate extension

The [source-bound certificate monograph](PLANNING_CERTIFICATE_MONOGRAPH.md) records the next completed bridge: external replay of the entire native construction trace, plus new kernel-checked node, threshold, conjunction and source-chain rules and a source-bound native five-variable fixture. The standalone audit now covers 99 theorems in four modules while preserving all original 59 declarations. The full external trace connects all five original inequalities to the unrestricted count; the packed checker-to-Lean bridge and the unrestricted kernel theorem remain open. See `receipts/planning/independent/certificate50.json` for full-instance replay evidence and `PerfectPower/PlanningCertificateExamples.lean` for the concrete small kernel proof.
