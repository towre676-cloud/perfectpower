# Global 81-call support theorem and exact two-exchange compiler (v0.25)

## 1. Scope

V0.25 keeps the v0.23/v0.24 degree-eight targets and the `(0,2)` native mask fixed. It does not enlarge the rational task space. It asks two exact questions: whether any 488-word degree-eight dictionary can have a smaller support-pattern residual machine than the 81-call v0.24 sensor machine, and whether a small simultaneous basis exchange can materially improve the exact rational heights while preserving that machine.

## 2. Complete-bipartite transition geometry

Let `W_{<=8}` be the 511 binary `G/H` words of lengths zero through eight. For a fixed execution depth `k=0,...,7` and next symbol `s in {G,H}`, the full transition support graph has left vertices the `2^k` prefixes and right vertices all suffixes of lengths `0,...,7-k`. Hence

`Gamma_{k,s} = K_{2^k, 2^(8-k)-1}`.

Its full transition rank is `min(2^k,2^(8-k)-1)`. Reducing the maximum matching rank of a complete bipartite graph `K_{m,n}` by one requires at least `max(m,n)` deleted edges. Therefore the degree-eight thresholds are

`255,127,63,31,16,32,64,128`.

A 488-word dictionary omits only 23 words. Thus every transition rank is forced to remain full except possibly `k=4`. The complete 511-word dictionary has 82 primitive transition calls, so every 488-word support satisfies

`boxed{calls_structural >= 81}`.

A loss in both `k=4` symbol graphs would require at least `16+16=32` omissions. A two-rank loss in one `K_{16,15}` graph also requires at least 32 deletions. Hence at most one primitive call can be removed structurally.

With at most 23 deletions, rank `15 -> 14` in `K_{16,15}` can occur only by isolating one right vertex: every one of its 16 incident edges must be deleted. Consequently the 81-call supports are exactly those whose omission set contains a complete 16-word `k=4` transition fiber. This is a global support-pattern theorem, not merely a one-exchange census.

## 3. Consequence for the v0.23 prefix support

The v0.23 488-word prefix dictionary omits indices `488,...,510`. Sixteen of these are precisely the execution-order `H / HHH` fiber, indices `495,...,510`; the remaining seven are extra omissions. A two-exchange support can stay on the 81-call structural stratum only if both inserted words come from those seven extras. No different fiber can be completed with only two new omissions because every other fiber meets the baseline omission set in at most seven words.

Therefore the complete two-exchange universe has

`C(488,2) C(23,2) = 30,063,484`

supports, but only

`C(488,2) C(7,2) = 2,495,388`

can preserve the 81-call structural minimum.

## 4. Exhaustive determinant-proxy screen

For the degree-eight constrained square system `A c=b`, let `N` be the 23 outside word columns. Replacing basic columns indexed by a two-set `I` with outside columns indexed by `J` changes the determinant by the exact low-rank identity

`det(A')/det(A) = det((A^{-1}N)_{I,J})`.

V0.25 evaluates the absolute value of this 2x2 determinant in double precision for all 2,495,388 structurally admissible two-exchange supports. This is used only as a conditioning/rational-height proxy; it is not promoted as an exact determinant ordering theorem.

The strongest proxy candidate removes written words

`HHHHHHG, GHHHHHHH`

and inserts

`HHHGHGHG, HHHGHHGG`.

Its proxy ratio is approximately `2.3719209309e-7`, or `2^-22.0074`; the runner-up is more than five times larger. The selected basis is independently nonsingular at the five good primes `1,000,003`, `1,000,033`, `1,000,037`, `1,000,039`, `1,000,081` before rational lifting.

## 5. Exact characteristic-zero programs

The selected support was lifted by p-adic reconstruction and checked directly against the integral native and Hecke word matrices.

For the two-route sensor `A_12+A_48`, the exact common-denominator program has coefficient height

`boxed{4630 bits}`,

versus 4652 bits for v0.23 and 4641 bits for the best v0.24 sensor alternative. The support remains 488 words, the native mask remains `(0,2)`, and the physical residual-Hankel machine remains exactly 81 primitive calls with cost 138,572.

For Paley, the same support gives

`boxed{4596 bits}`,

versus 4623 bits for v0.23 and 4610 bits for the best v0.24 Paley exchange. Unlike the v0.24 Paley alternative, which raised the exact physical machine to 82 calls, the v0.25 program retains the 81-call machine. Thus the new Paley program strictly improves both arithmetic height and execution state relative to every previously frozen constrained degree-eight Paley program.

At all five good primes both programs have state dimensions

`1,2,4,8,16,15,7,3,1`

and transition ranks

`(1,1),(2,2),(4,4),(8,8),(15,14),(7,7),(3,3),(1,1)`.

These attain the support-pattern bounds, so the 81-call machines are exact over characteristic zero.

The two-exchange dictionary has 487 flat prefix edges, split 245 `G` and 242 `H`, for naive prefix cost 833,078. V0.25 continues to treat that as a storage/evaluation statistic rather than physical linear execution complexity.

## 6. Joined Formation/Wilson/EQ Pareto calculus

The v41 species-route map remains explicitly engineered. Within that fixed join surface, v0.25 computes the first finite Pareto fronts instead of only class counts.

Across all 35 three-species supports, if one maximizes Wilson degree-four closure rank and the EQ direct-bypass bit, the coarse Pareto front consists exactly of the four triples containing routes 12 and 48 and one of 125, 116, 59, or 95. All four have degree-four rank 121 and direct bypass true.

Among the seven Fano lines, using the frozen objectives `maximize degree4 rank`, `maximize bypass`, and minimize one-pass degree, denominator bits, numerator bits, active word passes, and traffic, exactly four lines remain Pareto-undominated:

`49/12/125`, `49/48/116`, `12/48/59`, `12/116/95`.

The first two retain the cheap route-49 execution regime; `12/48/59` is the unique direct-bypass Fano line; `12/116/95` has the best arithmetic height among the non-bypass rank-121 Fano lines. This is a finite joined Pareto calculus, not an intrinsic equivalence between formation species and Wilson routes.

## 7. Evidence boundary and next problem

V0.25 proves a global 81-call support-pattern lower bound for 488-word degree-eight dictionaries and an exact fiber characterization of structural minimizers. It does not prove that every exact coefficient series on such a support needs 81 calls: special coefficient cancellations can in principle lower residual rank beneath structural rank. The selected programs attain the structural bound at five primes and therefore have exact characteristic-zero call count 81.

The exhaustive two-exchange search is exact in its support class but uses a floating determinant ratio only as a ranking proxy. The selected sensor and Paley programs are exact rational certificates; no global rational-height minimum is claimed.

The next useful move is therefore not a larger unrestricted exchange search. It is to attack coefficient-induced rank cancellation deliberately: search 81-structural supports whose modular residual ranks drop below their matching bounds at several independent primes, and only then attempt characteristic-zero lifting. If no such stable cancellation exists in a substantial multi-exchange neighborhood, the 81-call result can be promoted from support-pattern optimality toward a task-specific residual-machine minimum.
