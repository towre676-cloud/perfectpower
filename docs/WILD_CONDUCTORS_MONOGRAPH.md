# Wild conductor exponents from the Galois representation

This continues open item N41. Earlier work is in [DYADIC_REDUCTION_AND_STOKES_MONOGRAPH.md](DYADIC_REDUCTION_AND_STOKES_MONOGRAPH.md), which covers Tate's algorithm at 2 and 3, good-reduction certificates at 2 and tame extension clusters. That document listed wild ramification as not claimed. This document treats the wild case: Swan conductors and conductor exponents at p = 2, 3, 5.

- Module: `python/perfectpower/wild_conductors.py`
- Develop script: `python/develop_wild_conductors.py`
- Receipt: `receipts/curve_structure/wild_conductors.json`
- Tests: `python/tests/test_wild_conductors.py`

## The quantity

For an abelian variety A over Q_p and a prime l ≠ p, let V = V_l(A). The conductor exponent is

  a(A) = (dim V − dim V^I) + Sw(V).

Both terms are independent of l. The module computes each term from Galois data of torsion fields. It does not use a minimal regular model, and it does not use PARI's `elllocalred` or `genus2red`; those two serve as oracles only. Local fields are represented by number fields. For a global polynomial T, the étale algebra Q_p[x]/(T) is the product of the completions of Q[x]/(T) at the primes above p. Local values of e, f and the different are read from `nfinit([T,[p]])`. When the splitting field M is small enough for `galoisinit`, the full lower ramification filtration G_0 ⊃ G_1 ⊃ … at a prime of M is read from `idealramgroups`. The action on roots is computed with `nfgaloisapply`, and the tame character σ(π)/π mod P is a discrete logarithm in the residue field.

## 1. Elliptic curves at 2 and 3

**Swan conductor at p = 2, with l = 3.** Let W = F_3². For every 2-subgroup H of GL_2(F_3),

  2(2 − dim W^H) = (8 − #H-orbits on W−0) − (4 − #H-orbits on P(W)).

This identity was checked on all 33 two-subgroups (the Sylow subgroup has order 16). It reduces Sw(E) to two permutation conductors: Sw(E) = (Sw(points) − Sw(lines))/2. The points are the roots of the degree-8 resultant in t = y′ + λx, where y′ = 2y + a_1x + a_3. The lines are the roots of ψ_3. Each permutation Swan conductor is Σ_P f_P(v_P(𝔇) − e_P + 1).

**Swan conductor at p = 3, with l = 2.** As Brauer characters of 3-groups, E[2] ⊕ 1 = F_2[roots of the 2-division cubic], so Sw(E) is the Swan conductor of that cubic.

**Second Swan route.** On a subset of curves, the Swan conductor is recomputed as Sw = Σ_{i≥1} |G_i|/|G_0| (2 − dim E[l]^{G_i}). Here the fixed points of G_i are counted in the full torsion field, which has degree up to 48 (GL_2(F_3)). The count must be l^d − 1, which is asserted.

**Tame part without Tate's algorithm.**
- If v(j) < 0, E is the quadratic twist by −c_6 of a Tate curve. It has multiplicative reduction exactly when Q_p(√−c_6) is unramified (tame part 1). Otherwise the tame part is 2.
- If v(j) ≥ 0, the reduction is potentially good. By Serre–Tate, E has good reduction exactly when inertia fixes E[3] pointwise (p = 2) or E[4] pointwise (p = 3). That holds when every field of a torsion point is unramified.

**Ogg's formula.** f = v(Δ_min) − m + 1, where m is the number of components of the Kodaira fibre. It is evaluated twice, once from our Tate algorithm and once from PARI's Kodaira symbol with PARI's minimal discriminant.

## 2. Genus two (any genus) at odd p, wild included

The roots of f are taken in the splitting field M, and the depths are v_P(r_i − r_j)/e_P. These give the cluster picture (reusing `cluster_stable_reduction.cluster_picture`). The inertia image G_0 acts on the roots by permutations, and each element carries a tame exponent. A covering group of order 2|G_0| adds the action on √π, which carries the sheet signs. The invariant dimension dim V^I is a Lefschetz average over this group acting on the semistable fibre:

- The toric part is the trace on H_1 of the dual graph: 1 − #fixed vertices + #fixed edges.
- The abelian part is the trace on H^1 of the positive-genus components, averaged over the stabiliser of each orbit.

An element with nontrivial tame rotation on a component is handled as in `tame_cluster_frobenius`. On such a component the element acts tamely, because its p-part acts trivially there.

A wild element g that fixes a cluster s but moves its children acts on the component of s as a translation x ↦ x + b. Such an element moves every child, because a translation has no finite fixed point. Its fixed points lie over ∞ and have ℓ-adic Lefschetz multiplicities, which the trace must use:

| Points over ∞ (odd children of s) | γ = 1 (g acts trivially on the sheets) | γ = −1 (translation composed with the hyperelliptic involution) |
|---|---|---|
| one point, ramified (odd number) | multiplicity 3, since a tame base change of index 2 doubles the lower break 1 | multiplicity 1 (transversal) |
| two points (even number) | multiplicity 2 at each point | no fixed points (the two points are swapped) |

Sanity checks:
- y² = x³ − x in characteristic 3 with x ↦ x + 1 gives trace −1, the eigenvalues of an order-3 automorphism.
- y² = x⁵ − x in characteristic 5 gives trace −1 on H¹ of dimension 4.

The Swan conductor is that of J[2], which is the permutation representation on the roots. It is computed two ways, from the filtration and from local discriminants, and the code asserts that the two agree.

**Ablation.** Counting every wild fixed point once instead of with multiplicity changes the result. The invariant average becomes non-integral or the conductor becomes wrong on almost every wild curve in the sample.

## 3. Genus two at 2: split Jacobians

PARI 2.17 `genus2red` returns exponent −1 at 2 whenever the reduction at 2 is bad, so PARI gives no local answer at 2. For y² = g(x²), the Jacobian is isogenous to E1 × E2 with E1: Y² = g(X) and E2: Y² = X³g(1/X). The conductor exponent at 2 is the sum of the Galois-route exponents of E1 and E2. The same holds for every Möbius image of the curve.

**Oracle at 2.** The exponent is checked analytically by the functional equation of L(C, s). PARI's `lfungenus2` supplies the Dirichlet series and the odd bad Euler factors. The conductor is set to 2^k·N_odd, with N_odd from `genus2red`, and `lfuncheckfeq` is run at 38 digits.

`lfungenus2` takes the Euler factor at 2 to be 1. This is wrong when dim V^I > 0 at 2, for example when one elliptic factor has good or multiplicative reduction at 2. With factor 1, the functional equation then fails for every k, which was observed on 2 curves before the fix. The oracle therefore replaces the factor at 2 with the product of PARI's elliptic local factors (`ellap`). Acceptance requires error ≤ −30 at the predicted k. On every fifth curve, k ± 1 are also tested and must be worse than −20.

## Results (receipt `wild_conductors.json`)

| Section | Compared | Disagreements | Notes |
|---|---|---|---|
| GL_2(F_3) identity | 33 two-subgroups | 0 | |
| Elliptic, p=2 and 3: Galois route vs PARI `elllocalred`, Ogg (our Tate), Ogg (PARI Kodaira data), Swan from Tate | 1,591 local reductions from 1,600 curves | 0 | 952 at p=2 (587 wild, Swan 1–6, all Kodaira types incl. II*, III*, In*); 639 at p=3 (169 wild, Swan 1–3). 199 filtration replays of the Swan conductor, all equal |
| Genus 2 at p=3, 5 (tame controls at 3, 5, 7) vs `genus2red` | 622 curves | 0 | 266 wild (211 at 3, Swan 1–6, exponents up to 10; 55 at 5, Swan 1, 3, 5, exponents up to 9). 254 involve wild translations of positive-genus components. 40 curves skipped (splitting degree > 72), 0 failures |
| Ablation: fixed points counted once | 622 | 254 wrong (245 non-integral) | Multiplicities are necessary |
| Genus 2 at p=2, split Jacobians: Galois route vs Tate route (E1, E2) | 300 curves | 0 | Exponents at 2 from 2 to 16; Swan 0–12 |
| Same 300 curves vs the functional equation | 300 (+60 neighbour scans, +75 Möbius images) | 0 | 33 curves needed the corrected Euler factor at 2. Worst accepted error −53; the best wrong k reached −8. `genus2red` returned −1 at 2 on all 300. 672 sampled curves were skipped (2^(k+1)·N_odd > 8·10^6) |
| Survey of generic genus 2 at 2 (oracle only) | 30 curves | — | 7 have a unique hit (exponents 6–10); 23 have none within the scan range or with the factor-1 Euler factor. Not a result of this module |


All sampling is seeded and no timings are written, so each section replays byte-identically. That was checked by rerunning a section and comparing SHA-256 hashes.

## Not claimed

- **General genus two at p = 2.** Only split Jacobians y² = g(x²) and their Möbius images are handled, plus the good-reduction certificates of the earlier monograph. A general curve needs the l = 3 local Galois module J[3] (80 points), as in Doris's algorithm. That is not implemented. The survey section records analytic-oracle values for generic curves as oracle data only, not as results of this module.
- **The functional-equation check is not a proof.** It is numerical, and it relies on the analytic continuation of L(C, s). It is used as an oracle only.
- **Minimal regular models.** None are computed. The component count m in Ogg's formula comes from Kodaira symbols, for elliptic curves only. There is no Ogg–Saito check for genus two.
- **Odd p, larger fields.** The Galois route needs a splitting field of degree ≤ 72 on which `galoisinit` works. Larger or non-solvable cases are skipped and counted.
- **Proofs of the multiplicity table.** The table rests on the ℓ-adic Lefschetz formula with intersection multiplicities and on the lower-break computation above. The cross-checks against PARI support it but do not prove it. The trust base is Python plus PARI (number fields, `galoisinit`, `idealramgroups`, `lfun`). There is no Lean.
- **Tamagawa numbers in the wild case.** Not computed.
