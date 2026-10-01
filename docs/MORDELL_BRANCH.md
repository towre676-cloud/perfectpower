# Closing unresolved Mordell curves: the branch compiler for `y² = x³ − D`

**Headline.** A finite, exhaustive branch compiler gives Lean-certified complete lists of integral
points for **36 of the 59** curves `y² = x³ − D` (`1 ≤ D ≤ 100`) that the repository could not
enumerate before, including `y² = x³ − 1`:
- 26 close by field cubes and local obstructions (§3);
- the other 33 curves reduce to explicit Thue equations. 10 of them close by transporting their Thue
  branches to 15 proved obligations (§5–6), and **23 remain open** (§7). PARI solves all 33
  unconditionally, and the resulting lists agree with Sage on all 33. For the 23 open curves that
  is external evidence, not a Lean theorem.

## 1. The method (`PerfectPower/DescentBranch.lean`, `python/perfectpower/branch_descent.py`)

**Every solution enters a branch.** `ClassTwo.short_relation` is Thue's lemma on the lattice
`{(a, b) : x ∣ a − y b}`. For every solution it gives `a, b` and an entry `(k, p, q)` of a finite
table (`1 ≤ k ≤ K` from the Thue box, `|q| ≤ Q`, `p² + D q² = k³`) with

$$k^3\,(y+s) = (p+q s)\,(a+b s)^3,\qquad s=\sqrt{-D}.$$

The argument assumes nothing beyond this:
- **coprimality:** it does not assume `y + s` and `y − s` are coprime;
- **ring:** it does not assume the ring is maximal;
- **units:** it does not assume the units are `±1`;
- **class number:** it assumes nothing about it.

Common factors (primes over 2 and over `D`), conductors and units all appear as table entries,
and each must be discharged.

**Each entry is closed in one of two ways**, or the curve stays open:

| verdict | condition (kernel-checked) | consequence |
|---|---|---|
| field cube | `g³(p + q s) = (c + d s)³`, `g ≥ 1` | with `A + B s = (c + d s)(a + b s)`: `B(3A² − D B²) = (gk)³`, a **reducible** cubic. `|B|` is a product of three divisors of `gk`, and `A` follows. Every `y` of the branch is in an explicit list (`divYs_complete`) |
| local | `q W₁(a,b) − p W₂(a,b) ≢ k³ (mod m)` for all residues | the branch is empty (`mod_sound`) |
| neither | — | an **irreducible Thue equation** `q a³ + 3p a²b − 3Dq ab² − pD b³ = k³`; the certificate fails and **nothing is claimed** |

Field cubes include:
- the Gaussian units (`i = (−i)³`);
- element cubes (`2 + 2i = (i − 1)³`);
- cubes of non-integral elements such as `(−1 + √−19)/2` (for `D = 76`, `g = 4`).

No residue check, class number or maximal-order argument is needed for them: the divisor
enumeration replaces all of it.

**Every candidate returns to the curve.** The final list keeps `(x, y)` only when
`y² + D = x³` exactly, with the cube root verified by its bracket (`pointsB`). The theorem is
`complete_of_branch: y² = x³ − D ↔ (x, y) ∈ P`.

**Checked soundness.** In development, a weaker Python test (the four branch relations jointly
mod `m`) once accepted `D = 83`. The Lean checker verifies only the Thue-form test, and it
rejected that certificate. The Python side now uses exactly the test Lean checks.

## 2. The Gaussian pilot (`PerfectPower/MordellMinus1.lean`)

`y² = x³ − 1` was refused by the old certificate, which assumed the units are `±1`. Its table has
eight entries:
- `k = 1`: `±1` and the Gaussian units `±i`, all cubes (`units_are_cubes`);
- `k = 2`: `±2 ± 2i`, the common-factor case at the ramified prime `1 + i`, all cubes of `∓1 ± i`
  (`common_factor_cubes`).

Every branch is reducible, and `complete` proves the only point is `(1, 0)`. An odd `y` would
have to enter through a `k = 2` branch; those are closed like the rest, so no parity or
coprimality argument is needed.

## 3. Results on the 59 negative-`k` curves (`receipts/mordell_branch.json`)

| | curves |
|---|---|
| **complete, Lean-certified** (`Generated/MordellBranch.lean`) | **26**: `D` = 1, 8, 11, 16, 19, 20, 24, 27, 31, 35, 40, 44, 50, 51, 54, 59, 64, 67, 68, 75, 76, 81, 83, 84, 88, 96 |
| of which Sage rank 0 / 1 / 2 | 10 / 12 / 4 |
| agree with the Sage census / published counts | 26/26 / 26/26 |
| open: some branch is an irreducible Thue equation | 33 |

**The diagnostic prediction, tested.** The earlier classification predicted that a maximal-order
descent with a gcd case split would address every recorded failure of 46 curves.
- **22** of those 46 are now closed.
- **24** are not: their Thue branches carry genuine solutions (e.g. `D = 7`: `(2, ±1)`,
  `(32, ±181)`) or resist every modulus tried.
- **4 closed curves were not predicted**: `D = 31, 59, 83`, classed `CLASS_3`, whose non-cube
  branches are impossible mod 9 or 64, and `D = 1`.

The diagnostic identified failures of the *old certificate*, not all the mathematics needed for
completeness. That is why it over-predicted, missing the irreducible Thue branches, and
under-predicted, missing the local obstructions. A refusal disappearing was never counted as a
closure: every closed curve has a compiled completeness theorem.

`receipts/oeis_sqrt2_atlas.json` now checks **67** certified lists against A081119/A081120, with
**0 disagreements**, and the leads fall from 155 to 129.

## 4. The open branches, externally (`crosscheck/branch_thue_pari.py`, `receipts/mordell_branch_thue.json`)

For each of the 33 curves with Thue branches (10 since closed in Lean, 23 still open), every open branch was solved as a Thue equation by PARI's `thue`
with `thueinit(P, 1)`: flag 1 certifies without GRH. Each branch ran as an isolated job with a
600 s timeout.
- **All 316 branches finished** (each in under 0.1 s of PARI time).
- The branch-assembled lists (78 points, largest `|y| = 13537`) **agree with the Sage census
  (`mordell_census.csv`) on 33/33** curves.

This is a complete external computation under PARI's correctness. It is not a Lean theorem:
completeness of a Thue equation rests on Baker-type bounds inside PARI.

It also names the exact **proof targets**: for each open curve, a short list of binary cubic
Thue equations `F(a, b) = k³` with their solutions. A formal Thue solver, or certificates of Baker
bounds plus a reduced search, would close these branch by branch.

## 5. The Thue workload as a transformation graph (`thue_graph.py`, `make_lean_thue_branch.py`, `receipts/thue_graph.json`)

**Nodes.** Every open branch is an equation `F_{p,q}(a, b) = k³` with a readout
`y = (p W₁ + D q W₂)/k³`. It is kept as a whole: form, right-hand side, curve and entry.

**Edges.** A matrix `T ∈ GL₂(ℤ)` with `F ∘ T = G` maps the solutions of `G = M` bijectively onto
those of `F = M`. The inverse is integral because `det T = ±1` (`ThueLocal.sols_transport`,
`empty_transport`), and the certificate is the matrix plus a coefficient identity checked by
evaluation.

**Computed classes, and what is proved about them.** All 316 forms have positive discriminant,
so their Hessians are positive definite. Reducing the Hessian gives a normal form
(`thue_graph.canonical`), and it sorts the 316 nodes into **79 computed classes**. Three
statements need keeping apart:
- **Transport inside each class is certified.** Every node carries a matrix `T` with
  `F ∘ T = (representative)`, and Lean checks each one by evaluation. This is all the
  certificates use.
- **Inequivalence between classes is not proved here.** That no two of the 79 classes are
  GL₂(ℤ)-equivalent follows from the classical uniqueness of reduced binary cubic forms (reduction
  of the Hessian). Neither that theorem nor its application is formalized. The Python tests
  (300 random transformations mapped back to the same normal form) are evidence of invariance,
  not a proof of it.
- **A bounded independent cross-check agrees.** The `galois_merge` package's `branch_adapter`
  searches all matrices with entries of size at most 2, and checks each edge it finds exactly. It
  finds 474 edges, none between two different classes, and they connect the nodes into exactly
  the same 79 components (`galois_merge/run_repo_adapters.py`, `receipts/galois_adapters.json`).

So "79 obligations" means that the certificates needed 79 and no more. It does not rule out
further savings: a proved equivalence between two classes, or reuse of shared field data, could
lower the count. The established equivalences give no additional savings.

| | count |
|---|---|
| branch equations (nodes) | 316 |
| GL₂(ℤ) classes (distinct obligations) | **79** |
| class size | 4 in every class: `(p, q) ↦ (±p, ±q)`, realized by `−I` (`F ↦ −F`) and `diag(−1, 1)` (complex conjugation of the branch) |
| classes shared between curves | 0 (via the established equivalences) |
| forms with a nontrivial automorphism `F ∘ T = F` | 0 |

**Cubic fields** (`crosscheck/thue_fields_pari.py`, `receipts/thue_fields.json`; external, PARI
`bnfinit` + `bnfcertify`). `F(a, b) = c₀ N(a − bθ)` puts each class in the cubic field `ℚ(θ)`.
- The 79 classes lie in **26** fields, all totally real, all certified.
- **6 fields span several curves**: `D = 7, 28, 63` share discriminant 756, and `D = 18, 32, 72`
  share 1944. These are the curves `D` and `D m²`, with the same quadratic field `ℚ(√−D)`.
- **Sharing a field is not equivalence**: the order containing `a − bθ`, the leading coefficient
  and the right-hand side still differ, so no proof is transported along a field.
- `D = 48` lives in the cyclic field of discriminant 81. Its field automorphisms do not act on the
  equation's lattice, which is why no form has a GL₂(ℤ) automorphism.

## 6. A new certificate: p-adic descent on forms (`ThueLocal.lean`, `DescentThue.lean`)

**Which classes can be closed.** A class whose Thue equation has integer solutions that return to
curve points cannot be closed by any local argument. PARI labels 62 of the 79 classes that way.
The other **17 classes have no Thue solutions at all**; the certificates below do not depend on
that label.

**The certificate** (`ThueLocal.descB`, sound by `descB_sound`) is a list of nodes. For
`F(a, b) = M`, it splits every integer pair:
- **both divisible by `p`:** `F(a/p, b/p) = M/p³`, or no solution when `p³ ∤ M`;
- **primitive, with `p ∣ M`:** `(a : b)` is a root of `F` mod `p`, so `(a, b)` lies on a line
  `a = λb + pc` or `b = pv`. There `F ∘ T = pˢ H`, and the child is `H = M/pˢ`.

The recursion ends at leaves with `p ∤ M`, closed by a residue-lifting tree (`lvl`). The checker
verifies, residue by residue, that every nonzero root of `F` mod `p` lies on a listed line, so no
primality or inverse mod `p` is used.

**Why not plain residue lifting.** Lifting all residue pairs mod `pᵉ` is complete but wide. For
the obligations here it needs up to 2,193,840 lifts per class (depth `3⁸`), and the kernel ran out
of memory (15 GB) on such a tree, in both a breadth-first and a depth-first form. The descent
follows the `p`-adic root lines instead:
- **15 of the 17 point-free classes** close with at most 20 nodes each: **178 nodes and 2,008
  leaf lifts in total**, against 7,974,209 lifts for plain trees (one per class) or 31,896,836
  (one per branch);
- **exact repeated suffixes are interned**: a subproblem `(F, M)` reached along two paths is
  checked once, and both parents point at it. The checker only needs children after parents, so
  the certificate is a DAG. Unfolded as trees, the same certificates have 220 nodes and 2,487 leaf
  lifts. Only identical `(F, M)` are shared: the 205 non-root nodes are 163 distinct exactly but
  108 up to GL₂(ℤ), and sharing those would need a transport step inside the checker;
- the whole file of 15 obligations and 10 curves checks in about 80 s.

**Transport composes with the branch theorem.** `DescentThue.complete_of_thue` extends
`complete_of_branch` with a third verdict. An entry is closed when `F_{p,q} ∘ T` is an obligation
`(G, k³)`, and each obligation's proof is supplied once, as a hypothesis, to every curve and
branch that uses it.

**New complete lists (Lean)**: **10 curves**.

| D | 29 | 32 | 36 | 38 | 52 | 56 | 77 | 80 | 86 | 92 |
|---|---|---|---|---|---|---|---|---|---|---|
| points | – | – | – | – | – | (18, ±76) | – | – | – | – |
| obligations used | 2 | 1 | 1 | 2 | 1 | 1 | 1 | 1 | 1 | 2 |

All ten agree with the Sage census. Seven have Sage rank 0 and three rank 1; the Lean lists do not
use ranks. With the 26 from §3, **36 of the 59 negative-`k` curves** with
`D ≤ 100` now have Lean-certified complete lists. The atlas checks 77 certified lists against
A081119/A081120 with 0 disagreements, and 119 leads remain.

**Three kinds of evidence, kept apart:**

| | what it says | where |
|---|---|---|
| PARI Thue solutions | a complete external computation of each branch, under PARI's correctness | `mordell_branch_thue.json` |
| Lean membership | each listed point is on the curve | `pointsB`, inside every certificate |
| Lean completeness | no other integral point exists | `complete_of_branch`, `complete_of_thue` |

## 7. What remains, and why

**Accounting.** 23 of the 59 negative-`k` curves remain open. For each of them, completeness is
blocked by at least one class that carries points (62 such classes in all). That count includes
`D = 72`. On `D = 72` there are two separate issues:
- classes 55 and 58 carry points and need a bound, like every other open curve;
- classes 56 and 57 are point-free, according to PARI, but no local certificate closes them.

So closing the two point-free classes would not close `D = 72`. Lists: "open with a
point-carrying branch" = 23 curves; "point-free class not closed by descent" = 2 classes, both on
`D = 72`.

Completeness at a point-carrying class needs a bound on the solutions of an irreducible Thue
equation (Baker-type bounds with reduction, or Skolem's `p`-adic method). A local certificate
cannot do it, because a solution survives at every place.

### 7.1 D = 72: the local–global diagnosis (`python/d72_local.py`, `receipts/d72_local.json`)

The question is whether classes 56 and 57 are locally soluble everywhere, **including the branch
restrictions**. The restrictions are the readout conditions `k³ ∣ p W₁ + D q W₂` and
`k ∣ a² + D b²`, with `k = 9`, so they live only at 3. The curve equation then follows from the
norm identity. Every place is covered:
- **Real place.** `F(t, 1)` is a real cubic, and an odd-degree real polynomial takes every value.
- **Exceptional primes** `2, 3, 5, 7` (all primes of `3 · M · disc F`). The script gives an explicit
  Hensel witness `(a, b)` with `v_p(F − M) ≥ 2 v_p(∂F) + 1`, so `a` lifts to a `p`-adic root.
  - At `3`, the witness also satisfies both restrictions, and the lift agrees with it modulo
    `3^(e−v)` with `e − v ≥ 6`, so the restrictions persist in the limit.
  - The witnesses are `(1977, −40)` with `e = 17, v = 7` for class 56, and `(−3894, −40)` with
    `e = 11, v = 5` for class 57.
- **All other primes `p ≥ 11`, uniformly.** Two steps are needed, because smoothness alone gives
  no point:
  - *Existence.* The projective plane cubic `F(a, b) = M z³` is smooth over `𝔽_p` when
    `p ∤ 3 M disc F`, so it is a genus-1 curve. Hasse–Weil gives at least `p + 1 − 2√p` points
    over `𝔽_p`. At most 3 lie at infinity (`z = 0`), and `p + 1 − 2√p − 3 > 0` for `p ≥ 11`.
  - *Lifting.* An affine point is smooth, so it lifts by Hensel. At `p ≠ 3` there are no
    restrictions.

**Conclusion.** Both classes are everywhere locally soluble with their restrictions, so **no local
certificate (descent or lifting, at any prime) can close them**. The obstruction is global.

**Solution-preserving descent sharpens this** (§7.2). Full descent over the primes of `M`
reduces class 56 and class 57 to the **same** unit equation
`G(u, v) = −3u³ + 9uv² − 2v³ = ±1` (canonical form; field discriminant 1944). Its solutions map
onto the class's solutions through the descent matrices, so it has none. Class 55, which carries
points, also has this equation among its leaves; its points come through its other leaves.
- PARI's `thue` (external) finds no solution of `G = ±1`.
- `G = ±1` is not locally obstructed at 2, 3, 5, 7, 11 or 13.

**The norm interface, in Lean** (`PerfectPower/NormForm.lean`). For any binary cubic `F` with
`c₀ ≠ 0`, put `β = c₀θ`, a root of the monic `X³ + c₁X² + c₀c₂X + c₀²c₃`.
- `mulMat_spec`: `mulMat` is the matrix of multiplication by `γ = c₀a − βb` on `(1, β, β²)`, in
  any commutative ring.
- `det_mulMat`: `det = c₀² F(a, b)`.

So `F(a, b) = M` iff `N(γ) = c₀² M` with `γ ∈ c₀ℤ + βℤ`: a nonmonic Thue equation is a scaled
norm equation **plus** a lattice condition. For the `D = 72` residual this gives:
- `d72_det`: `β³ − 27β − 18 = 0`, `γ = −3u − βv`, and `det = 9 H(u, v)`;
- `d72_no_int_root`: `X³ − 27X − 18` has no integer root (none mod 5);
- `d72_disc`: the polynomial discriminant is `69984`.

**Unit pilot** (`crosscheck/d72_unit_pilot.py`, `receipts/d72_unit_pilot.json`; external, PARI).
The field has discriminant 1944, class number 1 (certified) and two fundamental units. There are
two norm-±9 representatives up to units.
- Every `γ = ±α ε₁^{e₁} ε₂^{e₂}` with `|eᵢ| ≤ 40`, 26,244 elements in all, was reconstructed
  exactly and tested for the lattice `C = 0`, `3 ∣ A`. **None lies in the lattice.**
- A positive control runs the same pipeline at norm ±36 (`H = ±4`) and recovers `(1, 1)`,
  `(−1, −1)`, `(2, −1)` and `(−2, 1)`. So the empty result is a real search result.
- **The box is not a bound.** Completeness needs a proved `B` covering every solution in the
  lattice (Baker–Matveev on the unit equation, then reduction), and none is claimed.

The whole remaining `D = 72` point-free problem is therefore **one unit Thue equation**.

**Exponent bound and Lean** ([UNIT_PREMISES.md](UNIT_PREMISES.md)).
- Siegel's identity and Matveev's theorem give a first bound `H ≤ 2.6·10¹⁸`, with `H = max |eᵢ|`.
  The direct maximum-exponent reduction (`DirectReduction.lean`), applied exactly, brings this to
  **`H ≤ 4`** once `|v| > 1` (it was 35).
- `Generated/D72Unit.lean` and `D72Residual.residual_empty` prove `H(u, v) ≠ ±1` for all
  integers. The kernel checks the reduction chains, the box of `9²` elements of either sign, and
  the search `|v| ≤ 1`.
- Unit generation is **proved** (`Order1944.unitGen_proved`, [UNIT_PREMISES.md](UNIT_PREMISES.md)).
  So are the norm representatives (`D72Unit.normRep_pos_proved`: `9 ∣ N(g)` forces `3 ∣ A, B`,
  and `g/α` is integral). So is the analytic inequality (`D72Unit.analytic_pos_proved`,
  `AnalyticBridge.analytic_of_cert`). The proof rests on **one** named premise, `matveev_pos`:
  Matveev's lower bound for the three linear forms. The target `H = −1` needs no premise of its
  own: the form, `enc` and the norm are odd, so `UnitPremises.normRep_neg_of` and
  `analytic_neg_of` transport the `H = 1` facts.

So the residual is **closed conditionally**, and its external part is now three separate,
reusable statements instead of one opaque bound.

### 7.2 Solution-preserving descent on the nonempty classes (`python/descent_residual.py`, `receipts/descent_residual.json`)

Descent as in §6, but applied to all 64 classes without a descent certificate (the 62 point-carrying classes and `D = 72`'s two). It runs over **all** primes of
`M` (not just one), prunes children that are locally impossible at 2, 3, 5 and 7, and stops at
right side `±1`. Each child is `F ∘ T` with `det T = ±pˢ`. So the parent's solutions are exactly
the images of the children's solutions, and every solution reaches a leaf. Measured:
- the 64 classes end in **189 unit leaves**, which are **109 distinct** unit equations
  `G(u, v) = 1` up to GL₂(ℤ);
- 24 of these unit equations are shared by several classes;
- 28 have no solution with `|u|, |v| ≤ 60`.
- **Correction.** An earlier version of this section said multi-prime descent newly empties
  classes 42 (`D = 55`) and 51 (`D = 71`). It does not. Both already have §6 certificates and
  are among the 15 obligations. The measurement had counted as open every class on an open
  curve, and both curves are open because of their other, point-carrying classes. The only
  point-free classes without a certificate are `D = 72`'s classes 56 and 57, and §7.1 shows
  that no local certificate exists for them.
- **Multi-prime certificates** are now available in Lean anyway: `ThueLocal.descM` carries a
  prime per node, and `descM_sound` / `no_solution_of_descM` prove them sound.
  - Both soundness theorems reduce to one per-node lemma, `nodeB_step`, plus a generic induction,
    `sound_of_step`.
  - The generator tries a multi-prime certificate whenever single-prime descent fails. On the
    current workload it finds none, as it must: the two remaining classes are locally soluble.

No leaf here is "explicitly solved". A certificate that closes a nonempty class this way needs,
for each surviving unit equation, a proved complete solution list. That is the same global
problem, but now on 109 unit equations instead of 64 classes with large right sides. This
measurement itself promotes nothing.

**Worked instance: `D = 23`** (`python/make_lean_curves.py`, `Generated/Minus23.lean`,
`receipts/minus23_certificate.json`). The three open classes of `D = 23` need only two of the 109
unit equations.

| class | `M` | descent prime | nodes | leaves carried | complete list |
|---|---|---|---|---|---|
| 8 | `729 = 3⁶` | 3 | 7 | `F₁` | `(2, 1)` |
| 9 | `512 = 2⁹` | 2 | 48 | `F₁` | `(1, 1)` |
| 10 | `27 = 3³` | 3 | 3 | `F₁`, `F₂` | `(−3, 0)` |

The two unit equations are `F₁ = −u³ − 3u²v + 6uv² + 4v³ = 1` and
`F₂ = −u³ − 6u²v + 69uv² + 46v³ = 1`.
- **The field.** `ℤ[x]` with `x³ = 6x + 3`, discriminant 621. The embeddings are
  `φ₁ = 5 + x − x²` and `φ₂ = 14 + 3x − 3x²`. The norm identity `N(c₀a − bφ) = c₀²F(a, b)` is
  proved by `ring`, so the field correspondence is explicit, not read off a field label.
- **The unit equations, under Matveev only.**
  - Unit generation is proved: `ε₁ = −2 − x`, `ε₂ = −1 − 2x`, with a box of 8 units.
  - Norm `1` needs no representative search (`NormRepProof.normRep_one`: the adjugate is the
    inverse).
  - The analytic certificates have precision margins of 41–47 bits, and the reductions end at
    `H ≤ 6`.
  - The box and the small-`b` search give `F₁ = 1 ⇔ (u, v) = (−1, 0)`, and the same for `F₂`
    (`class_u1`, `class_u2`).
- **The descent.**
  - Each node carries its prime.
  - Pruned children are lifting leaves at their own prime (2, 3, 5 or 7).
  - A unit leaf `G = ±1` cites `F₁` or `F₂` through a checked unimodular map `F_c ∘ T = s·G`,
    `Tinv · T = I`.
  - `DescentLists.root_iff` gives each class's exact solution set as a `Finset`.
- **The curve.** `minus23`: the integral points are exactly `(3, ±2)`, under `matveev_u1` and
  `matveev_u2`. This agrees with the Sage census.

**Second instance: `D = 45`, one nonmonic source equation for three classes**
(`Generated/Minus45.lean`, `receipts/minus45_certificate.json`). Classes 30, 31 and 32 all descend
to `G = −2u³ − 6u²v + 3uv² + 4v³ = 1`.

| class | `M` | descent primes | nodes | complete list |
|---|---|---|---|---|
| 30 | `729 = 3⁶` | 3 | 7 | `(12, −1)` |
| 31 | `729 = 3⁶` | 3 | 27 | `(−3, 2)` |
| 32 | `216 = 2³3³` | 2, 3 | 11 | `(−9, −1)` |

- **The order.** `G` is not monic (`c₀ = −2`). The encoding `N(c₀u − vφ) = c₀²G(u, v)` gives
  norm `4`. `φ = −2θ = 2 + x` lives in `ℤ[x]`, `x³ = 18x + 12` (discriminant 19440, not maximal
  at 2). The proofs work in this order, which contains every encoded element.
- **Norm representatives without class numbers** (`NormRepProof.normRep_of_res`).
  - Every residue class modulo `8` with norm `≡ 4` is divisible by `γ = 4 + x`
    (`N(γ) = 4`; 512 residues decided by the kernel).
  - So `N(g) = 4` gives `g = γ u` with `u = g γ#/4` integral and `N(u) = 1`.
  - Modulo `4` the check fails, so the certificate needs `m = 8`.
  - One representative suffices, and no ideal theory or bounded search is used.
- **The units.** `ε₁ = −7 − 3x + x²`, `ε₂ = −41 − 51x + 13x²` (regulator about 30). The unit box
  has 117,215 triples, so `UnitGenProof.unitGen_of_slices` checks it in 33 slices, one kernel
  evaluation each. `set_option Elab.async false` keeps the peak memory near 4 GB.
- **The source theorem.** The analytic certificate reduces to `H ≤ 3`, and
  `G = 1 ⇔ (u, v) = (−1, −1)` (`class_w1`, under `matveev_w1`).
- **The curve.** `minus45`: the integral points are exactly `(21, ±96)`, under `matveev_w1`
  alone. This agrees with the Sage census.

**Third instance: `D = 18`, a shared order** (`Generated/Minus18.lean`,
`receipts/minus18_certificate.json`). Classes 6 and 7 descend to two monic unit equations in
`ℤ[θ]`, `θ³ = 9θ + 6` (discriminant 1944), the order of the `D = 72` residual.

| class | `M` | descent primes | nodes | sources | complete list |
|---|---|---|---|---|---|
| 6 | `216 = 2³3³` | 2, 3 | 11 | `v1` | `(0, 1)` |
| 7 | `27 = 3³` | 3 | 3 | `v1`, `v2` | `(−3, 0)` |

- **The sources.** `F₁ = −u³ − 3u²v + 6uv² + 2v³` and `F₂ = −u³ − 9u²v + 54uv² + 54v³`, with
  `φ₁ = 1 + θ`, `φ₂ = 3 + 3θ` and `N(−u − vφᵢ) = Fᵢ(u, v)` (by `ring`). With the opposite sign,
  `φ = −1 − θ`, the identity reads `Fᵢ(u, −v)`. Both have norm `1` (`normRep_one`), reduce to
  `H ≤ 3`, and have the single solution `(−1, 0)`.
- **The shared order.** Unit generation for `ℤ[θ]` is proved once, in `Generated/Order1944.lean`
  (`ε₁ = θ² − 3θ − 1`, `ε₂ = 2θ² − 1`, a 7,425-triple box). `D72Unit` and `Minus18` both import
  it, so neither re-checks the box.
- **The curve.** `minus18`: the integral points are exactly `(3, ±3)`, under `matveev_v1` and
  `matveev_v2`. This agrees with the Sage census.

**Fourth instance: `D = 89`, two sources in one order** (`Generated/Minus89.lean`,
`receipts/minus89_certificate.json`). Classes 68 and 69 descend to `F₁ = (−1, −3, 12, 2)` and
`F₂ = (−1, −18, 267, 534)`.

| class | `M` | descent primes | nodes | sources | complete list |
|---|---|---|---|---|---|
| 68 | `5832 = 2³3⁶` | 2, 3 | 13 | `t1` | `(−1, 1)` |
| 69 | `125 = 5³` | 5 | 3 | `t1`, `t2` | `(−5, 0)` |

- **One order.** `F₁` gives `x³ = 15x + 12` (discriminant 9612). `F₂` gives `x³ = 375x + 1500`,
  and `375 = 5²·15`, `1500 = 5³·12`, so its `x` is `5θ`. Both encode in `ℤ[θ]`, with `φ₁ = 1 + θ`
  and `φ₂ = 6 + 5θ`. Each reduces to `H ≤ 1` and has the single solution `(−1, 0)`.
- **The slab.** The units `ε₁ = 37 + 55θ + 13θ²` and `ε₂ = −131 − 125θ + 37θ²` (regulator about 41)
  give a coordinate box of 2,548,975 triples. For fixed `(B, C)`, the bounds `|σᵢ(w)| ≤ Uᵢ` confine
  `A` to an interval of length at most `2 min Uᵢ`. `UnitGenProof.unitGen_of_slab` enumerates only
  those intervals: 33,217 lattice points in 3,575 rows, in 13 kernel slices.
- **The curve.** `minus89`: the integral points are exactly `(5, ±6)`, under `matveev_t1` and
  `matveev_t2`. This agrees with the Sage census.

**Three curves through order maps: `D = 39, 47, 60`** (`Generated/Minus39.lean`, `Minus47.lean`,
`Minus60.lean`; the maps are in `Generated/OrderMaps.lean`). The census of maps between the orders
of the workload comes from the order-transport review of `fb30592` (`python/order_transport.py`).
- A map `R(p, q) → R(P, Q)` is fixed by the image `g` of the generator.
- `OrderEmbedding.lean` proves that such a map moves a source equation forward:
  `N_S(c₀u − vΨ(φ)) = N_R(c₀u − vφ)` (`nrm_enc_of_map`).
- When the map is an isomorphism (`OrderIso`), it also moves unit generation back
  (`unitGen_transport`).
- All 22 maps of the census are Lean-checked: `map_mul` and `map_nrm` by `ring`, the determinant by
  `decide`. Two pairs are isomorphisms: `iso_4_14` gives `(12, 10) ≅ (30, 62)`, and `iso_8_15` gives
  `(18, 26) ≅ (36, 82)`.

| curve | target order | maps used | unit generation | sources | points |
|---|---|---|---|---|---|
| `D = 39` (classes 27–29) | `t³ = 12t + 10` | 3 of 6 sources moved from `(30, 62)` by the isomorphism | box of 195 triples | `r1`–`r6` | `(4, ±5)`, `(10, ±31)`, `(22, ±103)` |
| `D = 47` (classes 33–35) | `t³ = 36t + 82` | 4 of 9 sources moved from `(18, 26)` by the isomorphism | slab of 153 points | `p1`–`p9` | `(6, ±13)`, `(12, ±41)`, `(63, ±500)` |
| `D = 60` (class 46) | `t³ = 12t + 14` | all 3 sources moved from `(12, 4)` by an embedding of index 2 | slab of 1,051 points | `q1`–`q3` | `(4, ±2)`, `(136, ±1586)` |

- For `D = 60`, the larger order's unit generation covers the encoded solutions. The source
  equation and the readout filter whatever the larger order adds. No maximal order is used.
- The class certificates check their own norm identities by `ring` in the target order. The
  theorems `phi_*_via` and `nrm_*_via` record where each `φ` comes from, but soundness does not
  depend on them.
- Every curve agrees with the Sage census.
- In `receipts/order_cost.json`, the unit-generation estimates were 733 (`D = 39`), 4,165
  (`D = 47`) and 3,870 (`D = 60`). The orders used cost 195, 720 and 1,942.

**`D = 72` in the order of its own residual** (`Generated/Minus72.lean`). The four monic sources
of classes 55 and 58 live in `t³ = 18t + 24`, which maps into Order1944 (`t³ = 9t + 6`) with index 2
(`OrderMaps.map_22`, `t ↦ 6 + θ − θ²`). Classes 55, 56 and 57 also reach the residual
`H = (−3, 0, 9, −2) = 1`, which `D72Unit.class_pos` proves has no solution. The curve module cites
that theorem as an external source under its own premise, `D72Unit.matveev_pos`.

| class | `M` | descent primes | nodes | sources | complete list |
|---|---|---|---|---|---|
| 55 | `1728 = 2⁶3³` | 2, 3 | 25 | `s4`, residual | `(0, 1)` |
| 56 | `729 = 3⁶` | 3 | 27 | residual | — |
| 57 | `729 = 3⁶` | 3 | 7 | residual | — |
| 58 | `216 = 2³3³` | 2, 3 | 7 | `s1`–`s4` | `(−6, 0)` |

- No new unit-generation proof: unit generation is imported from `Order1944`.
- `minus72`: the integral points are exactly `(6, ±12)`, under `matveev_pos` and `matveev_s1`–`s4`.
  This agrees with the Sage census.
- The census of order maps now also offers the orders already proved in Lean as targets. Of these,
  only `(18, 24) → (9, 6)` was new; it is appended as `map_22`, so the earlier indices are unchanged.
- **Found by review:** a traversal bug in `descent_tree`. The loop could re-expand a node that already
  carried a lifting certificate when that node followed a carried leaf. This made the descent of
  classes 36, 43, 55 and 74 fail, so the assembly of `D = 48, 55, 72, 100` could not be priced. The
  loop now skips every assigned node. Every complete list is unchanged; two existing trees shrink
  from 11 nodes to 9 (`D = 18` class 6, `D = 45` class 32).

**Nonmonic sources: residue representatives, monic representatives, larger orders**
(`python/norm_rep_search.py`, `receipts/norm_rep_search.json`). After the order maps, most of the
remaining curves were blocked by sources with leading coefficient `|c₀| > 1`. Three tools now handle
many of them.
- **Monic representatives.** If a class takes the value `±1` at a primitive point `(x, y)`, then
  `F ∘ T` is monic for a unimodular `T` with first column `(x, y)`. That representative needs only
  `normRep_one`. The descent matches sources by their GL₂ class, so it can use any representative.
  6 of the 28 remaining nonmonic classes are of this kind.
- **Residue representatives** (`NormRepProof.normRep_of_res`). The search proposes representatives
  `γ` of norm `±c₀²` and a modulus `m`. `res_ok` is an exact mirror of the kernel's `resRepB`.
- **Larger orders.** A source moved into a larger order often needs a much smaller modulus:
  - `D = 15`: modulus 9 with one representative in `t³ = 12t + 14`, against 81 in its own order;
  - `D = 48`: modulus 9 in `t³ = 3t + 1` (discriminant 81);
  - `D = 71`: its three nonmonic sources each certify with one representative modulo 9 in
    `t³ = 24t + 42`, and fail in their own order.
- **Several representatives.** `UnitPremises.analytic_cons` combines one analytic certificate per
  representative. The source premise is then the conjunction of their Matveev instances. `D = 26`
  and `D = 55` use three representatives each (moduli 36 and 25).
- **Shared order.** Unit generation for `t³ = 12t + 14` now lives in `Generated/Order1620.lean`,
  which `D = 15` and `D = 60` both import.
- **Limit.** A residue certificate is local. When an ideal of norm `c₀²` is not principal, no
  modulus covers its residue classes, and the statement needs class-group information. 18 nonmonic
  classes remain open in `receipts/norm_rep_search.json`.

| curve | order | sources | integral points |
|---|---|---|---|
| `D = 15` | `t³ = 12t + 14` (`Order1620`) | 1 residue (`m = 9`), 1 monic representative, 2 monic | `(4, ±7)` |
| `D = 26` | `t³ = 9t + 2` | 1 residue (3 representatives, `m = 36`), 2 monic | `(3, ±1)`, `(35, ±207)` |
| `D = 48` | `t³ = 3t + 1` | 1 residue (`m = 9`), 1 monic representative, 3 monic | `(4, ±4)`, `(28, ±148)` |
| `D = 55` | `t³ = 12t + 6` | 1 residue (3 representatives, `m = 25`), 3 monic | `(4, ±3)`, `(56, ±419)` |
| `D = 71` | `t³ = 24t + 42` | 3 residue (`m = 9` each), 4 monic | `(8, ±21)` |

All agree with the Sage census. Each holds under its own Matveev premises.

**Choosing a unit basis by its proved cost.** `ε'₁ = ε₁^{U₁₁} ε₂^{U₂₁}`,
`ε'₂ = ε₁^{U₁₂} ε₂^{U₂₂}` with `det U = ±1` generates the same group. `best_basis` searches
`|Uᵢⱼ| ≤ 2` and minimizes the enumeration Lean actually runs.

| order | box, given basis | best box (`U`) | slab, given basis | slab, box-optimal basis |
|---|---|---|---|---|
| 9612 (`D = 89`) | 2,548,975 | 1,042,671 (`[[−1, −1], [0, 1]]`) | 33,217 points | 123,553 points |
| 19440 (`D = 45`) | 117,215 | 117,215 | 7,629 points | — |

- Minimizing the box alone would choose a basis whose slab is 3.7 times larger. With the slab,
  the given basis is already optimal in this range. The cost function prices the check Lean runs,
  not the bounding box.
- When a different basis wins, the generator adopts it and emits the identities `basis_e1`,
  `basis_e2` (`ε'ᵢ` as products of powers of the units found), checked by the kernel.
- The slab also replaced the box for `D = 45`: the module checks in 75 s instead of 229 s.

**The layers** (`python/make_lean_curves.py`). A curve is assembled from three separately checked
layers:

| layer | content | reused by |
|---|---|---|
| 1. field certificate | `unitGen_proved` (in the curve module, or a shared order module such as `Order1944`) | every source equation of the order, across curves |
| 2. source equation `j` | `normRep_j_proved`, `analytic_j_proved` (under `matveev_j`), reduction, box: `class_j` | every class whose descent reaches `j` |
| 3. curve assembly | `desc_*`, `root_*`, `class_*` (`DescentLists`), `minus D` (`complete_of_lists`) | — |

The curve theorem is `(⋀_{j ∈ J_D} matveev_j) → (y² = x³ − D ↔ (x, y) ∈ P_D)`. Here `J_D` is
exactly the set of sources that its classes' descents reach.

**Coverage** (`python/descent_coverage.py`, `receipts/descent_coverage.json`). This receipt is
derived from the registered Lean theorems. The raw workload receipts are unchanged.
- Classes: 15 locally discharged, 28 conditionally complete, 36 unresolved, out of 79.
- Unit equations: 30 of 109 registered. These are the 29 curve sources and the `D = 72`
  residual `H = ±1` (`D72Unit.class_pos`, `class_neg`).
- 79 are unregistered. That count includes leaves of classes already complete by another route
  (field 756, `D = 72`).
- The workload that still blocks a class is
  `U_needed = ⋃_{C unresolved} (U(C) ∖ U_registered)`: **66** unit equations. Of these, 52 block
  one class, 4 block two, 8 block three and 2 block four (`needed_by_class_count`).
- Curves conditionally complete: `D = 7, 18, 23, 28, 39, 45, 47, 60, 63, 72, 89`.
- `curves_unresolved_workload` orders the 12 unresolved curves by the number of unit equations
  they still need.

**Cost before proof** (`python/order_cost.py`, `receipts/order_cost.json`). The number of
equations is a poor proxy, because one order with a large unit box can outweigh several cheap
ones. For each unresolved curve the receipt estimates

`C(D) = Σ_{new orders R} C_UnitGen(R) + Σ_{j ∈ J_D} C_source(j) + C_assembly(D)`:

- **Orders.** Each needed equation's order is computed and reduced by scaling (`x = kθ`). Equations
  in the same order share one unit proof: 88 equations need 32 orders.
- **C_UnitGen.** Units come from quotients of small elements of equal norm (no PARI). The basis is
  chosen by `best_basis`, and the cost is that of the cheaper of the box and the slab.
- **C_source.** For monic sources, the reduced bound `(2B + 1)²` plus the reduction steps.
  Nonmonic sources need a residue norm-representative certificate first, and are left unpriced.
- **C_assembly.** The descent nodes.
- **Results.** 27 orders are priced. Five are unpriced because their units were not found:
  discriminants of `x³ − 30x − 16`, `x³ − 39x − 2`, `x³ − 42x − 74`, `x³ − 48x − 30` and
  `x³ − 195x − 830`.
- **Ranking (before this round).** Fully priced curves, cheapest first: `D = 39` (about 1,900, two
  new orders), `D = 60` (about 4,000), `D = 47` (about 5,700) and `D = 95` (about 24,000). The first
  three are now proved through order maps (above).
- **With the order maps** (`C_unitgen_transported`), an order is charged at the cheapest proved or
  priced target it maps into, and each target is charged once per curve.
  - `D = 15` needs no new unit proof: both of its orders map into `t³ = 12t + 14`, which was proved
    for `D = 60`. What blocks it is two nonmonic sources.
  - `D = 53` drops from about 14 million to 43,000.
  - `D = 71` drops from 1.1 million to 2,600.
  - `D = 25`, `D = 100` drop from 419,000 to 7,100.
  - `D = 87` drops from 1.3 million to 51,000.
  - Before the traversal fix, `D = 72` looked unpriceable. Afterwards its assembly priced at 32
    nodes, giving an estimate of 3,424, so it went before `D = 95`. It is now proved (above).
  - `D = 95` (about 24,000) is the only remaining curve whose sources are all monic and priced. The
    other eleven have a nonmonic source, which needs a residue norm-representative certificate
    before it can be priced.
  - The total `C`, which sorts the curves, uses the original orders. `C_transported_proxy` and
    `ranking_transported_proxy` mix transported unit costs with source costs estimated in the
    original orders, so they are labeled as proxies.
- These are estimates of kernel work, not proofs.

### 7.3 A shared cubic-field pilot (`crosscheck/field756_pilot.py`, `receipts/field756_pilot.json`; external, PARI)

**One field serving several open obligations.** `K = ℚ(x)`, `x³ − 6x − 2 = 0`, has
discriminant 756, is totally real, has class number 1 and unit rank 2, and is certified with
`bnfcertify`. It carries 7 classes from three open curves: `D = 7` (0, 1, 2), `D = 28`
(18, 19, 20) and `D = 63` (50). For a class `(c₀, c₁, c₂, c₃)` with right side `M`, put
`φ = c₀θ`. Then `F(a, b) = M ⇔ N_K(c₀a − bφ) = c₀²M`, so every solution is
`γ · ε₁^{n₁} ε₂^{n₂} · (±1)`, with `γ` taken from the finite list `bnfisintnorm(K, c₀²M)`.

- **Shared:** one `bnfinit` + `bnfcertify` (units, regulator 5.692, class group), and each class's
  `φ` embedded in `K` (`nfisisom`).
- **Per class:** only the norm list and the solutions' exponents. Every class has **one** norm
  representative and **2** solutions. Every solution has unit exponents with `|nᵢ| ≤ 1`, or
  `≤ 2` for class 50.
- **The bound** (`crosscheck/thue_bound_field756.py`, `receipts/field756_bound.json`). It uses
  the general pipeline `crosscheck/thue_bound.py`, also used for `D = 72`, with the direct
  maximum-exponent reduction recorded exactly ([UNIT_PREMISES.md](UNIT_PREMISES.md)):

  | class | D | M | `V` | `H` (was) | `H` (direct) |
  |---|---|---|---|---|---|
  | 0 | 7 | 64 | 1 | 11 | 5 |
  | 1 | 7 | 64 | 1 | 13 | 7 |
  | 2 | 7 | 8 | 1 | 10 | 5 |
  | 18 | 28 | 512 | 1 | 12 | 6 |
  | 19 | 28 | 512 | 1 | 13 | 6 |
  | 20 | 28 | 64 | 1 | 12 | 6 |
  | 50 | 63 | 64 | 0 | 10 | 5 |

- **Lean**:
  - `UnitBox.thue_list`: a complete list from the box and the small-`b` search (`UnitBox.cauchy`).
  - `UnitPremises.extBound_of`: the box bound **derived** from the premises plus kernel-checked
    reduction chains and norm identities.
  - `DescentThueList.complete_of_lists`: branch transport to classes with complete lists.
  - `Generated/Field756.lean`: `class_i` and `minus7`, `minus28`, `minus63`. The box hits are
    exactly PARI's solutions (positive control), and the points equal the Sage census.
- **Unit generation is proved** (`Field756.unitGen_proved`, `UnitGen.lean`): real embeddings,
  log enclosures, rounding into a box of 425 triples, and an explicit `±ε₁^x ε₂^y` for each of the
  6 units there.
- **The norm representatives are proved** (`Field756.normRep_N_proved`, `NormRepProof.lean`):
  every target is `±2^r 3^s`, and division by `x` and `1 + x` is exact when `2` or `3` divides
  the norm.
- **The analytic inequality is proved** (`Field756.analytic_i_proved`, `AnalyticBridge.lean`):
  Siegel's identity, the conjugate estimates, the inverse log matrix and the Matveev cutoff, with a
  kernel-checked rational interval certificate.
- **The remaining premise** is `matveev_i`, one per class: Matveev's lower bound for the three
  linear forms, with explicit constants ([UNIT_PREMISES.md](UNIT_PREMISES.md)).
- A field match is still not an equivalence: the 7 classes remain 7 obligations, sharing one unit
  group and one proof of unit generation.

### 7.4 Positive `k`

This is a separate development. The negative-`k` derivation uses `D > 0` in exactly four places,
in `ClassTwo.short_relation` and `DescentBranch.y_mem`:
1. `a² + D b² > 0`, which gives `k ≥ 1`;
2. `r² + D t² < (K + 1) r t`, which gives `k ≤ K`;
3. `D q² ≤ k³`, which gives the finite table `|q| ≤ Q`;
4. `y² + D = x³`, which gives `x > 0`.

For `D < 0`:
- (1) and (2) survive as `1 ≤ |k| ≤ K`: the lattice step never used definiteness beyond that bound.
- (4) fails: `y² = x³ + 8` has `x = −2`.
- (3) is the real change. `p² − |D| q² = k³` has infinitely many solutions, because the unit group
  of `ℤ[√|D|]` is infinite.

**Units modulo cubes is not a finite enumeration by itself.** `Interfaces.orbit_mod_three`
proves only the exponent normalization: `ε^n ρ = (ε³)^{⌊n/3⌋}(ε^{n mod 3} ρ)`. It leaves open
four separate obligations, and each must be discharged before any positive-`k` list is complete:
- **Seed coverage:** every solution of `p² − |D|q² = k³` lies in the orbit of a listed seed.
  This is the `QuadOrbit` certificate, and it must enter through a proved interface, not by
  matching data.
- **Ideal classes:** the element-versus-ideal gap when the class number of the real quadratic
  order is not coprime to 3.
- **Exceptional primes:** 2, 3 and the primes of `D`.
- **Integral readout of each reduced branch:** square `k` needs separate treatment.

Nothing is claimed for positive `k` yet.

## 8. Not covered

- **Positive `k`** (96 curves): `y² − k = x³` factors in a real quadratic field. This lattice
  argument is for imaginary `√−D`.
- **Irreducible Thue branches with solutions:** no Lean method here. Point-free branches close by
  the descent certificates of §6.
- **The Sage census:** external (mwrank ranks, elliptic logarithms), as before. Four of the 26
  closed curves have rank 2 in Sage. Their Lean lists do not use the rank at all.
