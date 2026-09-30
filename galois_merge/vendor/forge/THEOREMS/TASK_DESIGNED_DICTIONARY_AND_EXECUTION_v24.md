# Task-designed dictionaries, execution-order Hankel compression, and the v41 species join (v0.24)

## 1. Scope

V0.24 keeps the four v0.23 characteristic-zero tasks fixed: the EQ-LAB two-route sensor `A_12+A_48` and Paley, each under degree-eight `(0,2)` and degree-nine `(1,0)` native masks. It does not enlarge the rational reconstruction problem. It replaces the breadth-first prefix dictionary by exact one-word basis exchanges, evaluates the resulting five-way Pareto front, and corrects the residual-Hankel execution semantics for column-vector programs.

## 2. Execution-order correction

A written algebra word `s_1...s_d` denotes the product `s_1 ... s_d`. On column vectors the corresponding operators act right-to-left. The physical residual-Hankel machine must therefore be built from the reversed letter string. The earlier EQ-LAB v0.18 audit is preserved byte-for-byte as an algebra-word-order audit; v0.24 adds the column-execution audit rather than rewriting the upstream archive.

For both original v0.23 degree-eight programs the exact execution-order state dimensions are
`1,2,4,8,16,15,7,3,1`, with transition ranks
`(1,1),(2,2),(4,4),(8,8),(15,14),(7,7),(3,3),(1,1)`.
Thus the exact machine uses 41 G transitions and 40 H transitions: 81 primitive calls and cost 138,572 under the frozen G/H primitive costs 1,732/1,689.

For both original degree-nine programs the state dimensions are
`1,2,4,8,16,19,9,4,2,1`, with transition ranks
`(1,1),(2,2),(4,4),(8,8),(16,16),(9,9),(4,4),(2,1),(1,0)`.
This gives 47 G and 45 H transitions: 92 primitive calls and cost 157,409.

These are characteristic-zero exact. For every displayed state and transition matrix the rank computed modulo each independent good prime reaches the trivial support-pattern upper bound. The nonzero modular minor proves the same lower bound over Q, while the support pattern supplies a field-independent upper bound.

## 3. Exact task-designed dictionary exchanges

A one-word basis exchange can improve arithmetic height without changing the task or native mask. Five exact rational alternatives are frozen.

* Sensor d8 balanced: replace `HHGHHHHG` by `HHHGHGHG`. Height 4652 -> 4644 bits, support 488, flat prefix cost unchanged 833035, physical machine unchanged at 81 calls / 138572.
* Sensor d8 height-local: replace `GHHHHHHH` by `HHHGHGHG`. Height 4652 -> 4641, support 488; flat prefix cost rises by 43, but the physical machine remains 81 / 138572.
* Paley d8 balanced: replace `GHHHHHHH` by `HHHHGGGH`. Height 4623 -> 4610 with unchanged flat prefix cost, but the exact physical machine rises 81 -> 82 calls (140261).
* Sensor d9 balanced: height 6007 -> 6005 at unchanged flat prefix cost, but the physical machine rises 92 -> 96 calls (164251).
* Paley d9 balanced: height 5979 -> 5976 at unchanged flat prefix cost, but the physical machine rises 92 -> 96 calls (164208).

Therefore task-designed dictionaries produce a genuine Pareto set. The sensor degree-eight balanced exchange is a strict arithmetic improvement with no loss in either flat-prefix or compressed execution cost; the other exchanges trade coefficient height against one of the execution metrics. V0.24 stores alternatives instead of overwriting the v0.23 baselines.

Across every possible single replacement of the breadth-first support by one outside word, the coefficient-independent physical support-shape upper bound never falls below the baseline 81 calls at degree eight or 92 calls at degree nine. This is only a one-exchange support-shape statement: coefficient cancellations could in principle lower an exact rank, and no global l0 or machine-minimality theorem is claimed.

## 4. Five-way compiler objective

The live compiler objective is now
`(degree, active rational words, physical residual-Hankel cost, native state, rational coefficient height)`.
Flat shared-prefix cost remains useful as a storage/evaluation statistic, but it is no longer treated as execution complexity. The rank-compressed residual machine is the appropriate linear execution object.

The direct EQ-LAB sensor and primitive Paley remain external Pareto endpoints. The purpose of these rational programs is to quantify the cost of forcing the targets through restricted synchronized native masks, not to replace a cheaper direct route backend when that backend is available.

## 5. Formation v41 cross-category join

Formation v41 supplies an engineered, not intrinsic, seven-species join surface: the canonical v40 species keys `A5,...,A11` are attached in order to Wilson routes `(49,12,125,48,116,59,95)`. Forgetting labels, every three-species subset has the same depth-one formation lock. Wilson transport retains the labels and splits the 35 triples at degree four into ranks 118 (2 triples), 120 (13), and 121 (20), while all reach 152 by degree five. Adding the EQ direct-bypass bit yields five operational classes with counts `(118,false):2`, `(120,false):12`, `(120,true):1`, `(121,false):16`, `(121,true):4`.

The seven Fano lines form one `GL(3,2)` orbit on the formation side but split into Wilson degree-four ranks 120 (three lines) and 121 (four lines), with pairwise distinct exact compiler fingerprints. The unique Fano line containing both direct sensor routes 12 and 48 is `12/48/59`; it is route-49-free and therefore generically worse under the earlier arithmetic compiler metric, yet task-optimal for the direct EQ bypass. This is a concrete Pareto reversal.

No intrinsic group-theoretic identification between `A5,...,A11` and the seven Wilson route labels is asserted. The v41 map is a deliberately engineered common keyspace used to ask which formation-equivalent labeled subsets remain distinguishable by Wilson/EQ invariants.

## 6. Boundary and next target

V0.24 does not claim global word-support minimality, global residual-state minimality, or a natural equivalence between formation species and Wilson routes. The next arithmetic target should optimize small multi-exchange dictionaries directly against the exact physical residual-Hankel machine, screening support and ranks over several primes before rational reconstruction. The v41 join additionally makes it possible to score the same labeled subset simultaneously by formation lock data, Wilson closure fingerprints, EQ bypass availability, and synchronized compiler cost.
