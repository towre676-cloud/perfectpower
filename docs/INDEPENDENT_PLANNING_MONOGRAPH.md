# Independent unrestricted verification of the Petersen population

The October 12, 2026 verification route computes the complete 50-project feasible population using a standalone reduced ordered Boolean decision diagram (ROBDD) implementation. Its answer is **702,508,860,122,761**, exactly the previously published result. A separately implemented exact target enumerator finds exactly one feasible selection with profit at least **16,537**. That selection has profit 16,537 and original mask 95,583,623,577,551. These computations establish independent implementation agreement for the unrestricted population and a separate check of the unique optimizer. They do not establish Lean verification of either C++ executable or confirmation by a second externally authored unrestricted solver.

The authoritative new receipts are in `receipts/planning/independent`. The original population, MITM, Ganak, optimization and timing receipts in `receipts/planning/population` remain untouched. The successful unrestricted count is computed before the retained partition is queried; none of its published leaf counts enters diagram construction, intersection, reduction or counting. The existing 176 terminal cubes supply an additional comparison bank, not the decomposition used to obtain the new root count.

## Original mathematical question

The standalone parser reads `data/planning/mknap1.txt`, the retained public OR-Library transcription. It consumes all seven cases, retains the published profit tokens without rounding fractional cases, and selects the integral-profit 50-project case. It does not import `CompletionPlanner`, `planning_native`, the old benchmark parser or `completion_planner.cpp`. For project costs \(c_{jk}\), capacities \(u_k\), and original bits \(x_j\), its accepted predicate is

\[
 F(x)=\bigwedge_{k=1}^{5}\left[\sum_{j=1}^{50}c_{jk}x_j\le u_k\right],
 \qquad (u_1,\ldots,u_5)=(800,650,550,550,650).
\]

There are no extra dependency, symmetry, projected-variable or objective constraints in this population. Distinct projects remain distinct Boolean coordinates, including projects with equal costs. The objective is checked in another executable. The parser consumes every token and rejects a trailing transcription remainder. Costs are not inferred from the prior count or partition.

## Threshold diagrams and Boolean intersection

Projects are ordered by decreasing sum of their five integer costs, breaking ties by their original index. This order is defined independently of the native residual-polynomial engine. Each resource separately produces a threshold Boolean function. At ordered level \(i\) and remaining capacity \(b\), let \(T_i\) be the sum of the remaining costs for that resource. Its threshold constructor returns false when \(b<0\), true when \(b\ge T_i\), and otherwise constructs a node whose zero child is the threshold for \((i+1,b)\) and whose one child is the threshold for \((i+1,b-c_i)\).

Induction on the number of remaining coordinates proves that this node accepts exactly the assignments satisfying the single resource inequality. Nonnegativity justifies the terminal cases. The memo table for this construction records threshold Boolean functions, not feasible-population coefficients or optimizing aggregates.

The node constructor eliminates a decision when both children coincide and merges nodes with the same level and ordered pair of children. Both reductions preserve the represented Boolean function. Boolean AND is then computed by descending to the earliest level appearing in either operand. An operand that skips that level supplies the same function to both branches. Terminals follow the ordinary identities \(0\wedge A=0\), \(1\wedge A=A\), and \(A\wedge A=A\). Induction on the combined remaining levels proves that the result represents the conjunction of its operands.

The five threshold diagrams are intersected in resource order. After each intersection a separate postorder traversal retains only reachable nodes, rebuilding the canonical node tables and releasing obsolete diagrams and intersection caches. No resource-implication test, multivariate residual state, univariate coefficient lookup, bivariate suffix table, native arena, old partition coordinator or old counting function is reused.

## Counting represented original assignments

A reduced diagram may skip Boolean coordinates. Counting graph paths without their multiplicity would therefore be incorrect. Set the level of each terminal to \(n\), its suffix count to \(C(0)=0\) or \(C(1)=1\), and for an internal node \(v\) at level \(i\) use

\[
 C(v)=2^{\operatorname{level}(v_0)-i-1}C(v_0)
      +2^{\operatorname{level}(v_1)-i-1}C(v_1).
\]

The unrestricted answer is \(2^{\operatorname{level}(r)}C(r)\) for root \(r\). Each skipped coordinate is a freely chosen original bit, so it contributes a factor of two. Induction through the postorder node numbering proves the formula counts assignments, rather than paths or distinct resource vectors. The two decision branches are disjoint because they differ at the node's coordinate.

Conditional counting replaces each skipped-coordinate exponent by the number of *unfixed* coordinates in that interval. At a fixed decision node, it follows only the specified child; at an unfixed decision it adds both child counts. Original-coordinate masks are transported through the explicit ordering permutation. This gives an independent check of every retained root leaf against the newly constructed unrestricted Boolean function. It also checks that summing those independently counted leaves gives the unrestricted answer.

The separate Python partition checker validates original-mask ranges, one-bit free-coordinate splits, both children, duplicate split and answer addresses, reachable split records and complete cube coverage. The structural partition statement remains distinct from a leaf arithmetic statement. Coverage by itself does not certify a count; the new diagram supplies those leaf counts. Extra saved conditional answers are permitted in the old receipt but are not substituted for root leaves.

## Exact optimizer check

`native/independent_planning_optimizer.cpp` enumerates all feasible assignments whose objective is at least the published target. Its search order is decreasing profit, independently of the diagram order. At every node, it computes five separate fractional-knapsack upper bounds on additional profit, one for each resource. Remaining projects are sorted by exact profit/cost ratio using integer cross multiplication; zero-cost projects precede positive-cost projects.

For each resource, take every affordable whole project until the first fractional item. Its remaining contribution is bounded above by \(p b/c\). Since the actual objective is integral, rounding this fractional upper bound down is sound. The minimum of the five upper bounds remains an upper bound on the simultaneous constrained optimum. Branches whose bound is below the target contain no qualifying assignment. Negative residual capacity also proves infeasibility. Every other branch is explored, and full assignments are counted without an incumbent-dependent cutoff.

The retained run visits 4,133 nodes and finds **one** candidate at or above 16,537. Checking its original project costs and profit directly establishes feasibility. Because no other candidate reaches that target, this proves both global optimality and uniqueness under the original integer inequalities. The target is supplied by the publication; the absence of any better candidate is independently established by the exhaustive bounded search. It is not inferred from a solver's incumbent or floating-point tolerance.

## Generating functions and alternatives

The decision-diagram answer has the same mathematical meaning as

\[
 \sum_{0\le a_k\le u_k}[z_1^{a_1}\cdots z_5^{a_5}]
 \prod_{j=1}^{50}(1+z_1^{c_{j1}}\cdots z_5^{c_{j5}}).
\]

Expanding the product chooses one factor term per original bit. Thus each monomial coefficient is exactly the number of original assignments realizing its exponent vector, and the coefficient sum is the accepted Boolean population. This identity explains equivalence; the verifier does not evaluate the polynomial recurrence used by the original implementation. A dense five-dimensional coefficient array would require the product of the five capacity lengths in cells, making it unattractive here. Meet-in-the-middle is independently useful on the retained 39-project case, but its large multidimensional join was the original performance obstacle. The new route instead shares equal Boolean suffix functions across the whole cube. Decision-diagram size can still grow exponentially and depends on variable order; success here is not a universal complexity claim.

## Formal mathematics boundary

The existing Lean module `PerfectPower/PopulationPartitions.lean` proves `left_card`, `four_card`, and address-transport identities. Taking a splitting predicate to be the chosen original bit gives a formally established finite-filter cardinality split; iterating that identity justifies partition aggregation when the cubes are correctly represented and their populations are supplied correctly. Its transport theorems are applicable to coordinate bijections. These generic theorems are reused as the mathematical foundation, not advertised as a kernel proof of the new diagram builder.

A subsequent [Lean extension](PLANNING_LEAN_MONOGRAPH.md) checks 59 theorems: finite population cardinality, threshold construction, Boolean intersection, equal-child reduction, skipped-variable counting, original-prefix conditional counts 16,777,216 and 512, the literal optimizer witness, and the actual partition coverage and aggregation identity. The remaining formal work is the concrete C++ DAG-to-original-predicate bridge and source-bound unrestricted weight evaluation; the native target-enumerator completeness proof also remains separate. The present result closes independent unrestricted *computational* confirmation. It leaves native-kernel formal verification and externally authored unrestricted solver confirmation open.

## Reproduction and evidence

Run `make planning-independent-test` for 80 seeded exhaustive small cases, 320 conditional queries, exact optimizer comparisons including zero-profit ties and infeasible capacities, and the \(2^{62}\) count boundary. Run `make planning-independent-benchmark` for 20, 39 and 50 projects, or `python python/verify_planning_independent.py --case 50` for the unrestricted population, every retained root-leaf count, selected original prefixes and a separate optimizer enumeration. Three selected prefix counts are also rebuilt from scratch using their original residual constraints, rather than merely restricting the unrestricted diagram.

Receipts bind the raw dataset, partition, standalone C++ sources, Python driver, exact serialized diagram input, compiler/version/flags, variable order, address-space ceiling, node cap, wall timeout, diagnostics and outcomes. A retained 12-million-node attempt stops without returning a population. The successful default uses a 40-million-node cap, 6 GiB process address-space ceiling and 600-second timeout per worker. Peak RSS and elapsed times describe execution in this shared environment; they do not establish superiority over the old kernel or a controlled solver comparison. Earlier benchmark measurements are preserved. The public research feed carries the new verification status without claiming that installed native executables have changed.

### Retained execution

The 50-project source-bound run built its unrestricted diagram in 68.4149 seconds and completed all 179 conditional queries in 98.4184 seconds total inside the worker (101.155 seconds including process overhead). Peak RSS was 2,040,124 KiB. All 176 root leaves agreed; their independently counted sum was 702,508,860,122,761. The selected conditional rebuilds returned 16,777,216, 512 and 16,095,745. The 20-project total was 422,601, and the 39-project total was 368,072,359,571, also agreeing with the preserved independent references. The failed 12-million-node attempt reached its node limit after 49.612 seconds without establishing the unrestricted total. A final graph smaller than the cap does not imply that construction fits that cap: temporary conjunction nodes and earlier diagrams coexist before compaction.
