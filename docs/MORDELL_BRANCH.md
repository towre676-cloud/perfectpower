# Closing unresolved Mordell curves: the branch compiler for `y² = x³ − D`

**Headline.** A finite, exhaustive branch compiler gives Lean-certified complete lists of integral
points for **36 of the 59** curves `y² = x³ − D` (`1 ≤ D ≤ 100`) that the repository could not
enumerate before, including `y² = x³ − 1`:
- 26 close by field cubes and local obstructions (§3);
- 10 more close by transporting their Thue branches to 15 proved obligations (§5–6). The other 33 curves are reduced to explicit Thue
equations. PARI solves those unconditionally, and the resulting lists agree with Sage on all 33.
That is external evidence, not a Lean theorem.

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

For each of the 33 open curves, every open branch was solved as a Thue equation by PARI's `thue`
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

**Exact classes.** All 316 forms have positive discriminant, so their Hessians are positive
definite. Reducing the Hessian gives a canonical form (`thue_graph.canonical`, tested for
invariance), and the classes are exact rather than the output of a bounded search.

| | count |
|---|---|
| branch equations (nodes) | 316 |
| GL₂(ℤ) classes (distinct obligations) | **79** |
| class size | 4 in every class: `(p, q) ↦ (±p, ±q)`, realized by `−I` (`F ↦ −F`) and `diag(−1, 1)` (complex conjugation of the branch) |
| classes shared between curves | 0 |
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
- **15 of the 17 point-free classes** close with at most 28 nodes each: **220 nodes and 2,487
  leaf lifts in total**, against 7,974,209 lifts for plain trees (one per class) or 31,896,836
  (one per branch);
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

- **23 negative-`k` curves** have at least one class that carries points (62 classes in total).
  Completeness there needs an argument that bounds the solutions of an irreducible Thue
  equation (Baker-type bounds with reduction, or Skolem's `p`-adic method): not a local
  certificate.
- **D = 72** has two point-free classes that no descent up to `p = 43` closes. Its other classes
  carry points anyway.
- **Positive `k`**, as a separate development. The negative-`k` derivation uses `D > 0` in exactly
  four places in `ClassTwo.short_relation` and `DescentBranch.y_mem`:
  1. `a² + D b² > 0`, which gives `k ≥ 1`;
  2. `r² + D t² < (K + 1) r t`, which gives `k ≤ K`;
  3. `D q² ≤ k³`, which gives the finite table `|q| ≤ Q`;
  4. `y² + D = x³`, which gives `x > 0`.

  For `D < 0`, (1) and (2) survive as `1 ≤ |k| ≤ K` (the lattice step never used definiteness
  beyond that bound); (4) fails (`y² = x³ + 8` has `x = −2`). (3) is the real change: `p² − |D| q² = k³`
  has infinitely many solutions, because the unit group of `ℤ[√|D|]` is infinite. The repair is to
  take `β` modulo cubes of the fundamental unit. That is exactly what the `QuadOrbit` seed engine
  certifies (finitely many seed orbits of `x² − d y² = Δ` under a certified unit). The planned
  first family is one where those seeds and branches are uniform in a parameter. Nothing is
  claimed for positive `k` yet.

## 8. Not covered

- **Positive `k`** (96 curves): `y² − k = x³` factors in a real quadratic field. This lattice
  argument is for imaginary `√−D`.
- **Irreducible Thue branches with solutions:** no Lean method here. Point-free branches close by
  the descent certificates of §6.
- **The Sage census:** external (mwrank ranks, elliptic logarithms), as before. Four of the 26
  closed curves have rank 2 in Sage. Their Lean lists do not use the rank at all.
