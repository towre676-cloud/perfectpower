# Closing unresolved Mordell curves: the branch compiler for `y² = x³ − D`

**Headline.** A finite, exhaustive branch compiler gives Lean-certified complete lists of integral
points for **26 of the 59** curves `y² = x³ − D` (`1 ≤ D ≤ 100`) that the repository could not
enumerate before, including `y² = x³ − 1`. The other 33 curves are reduced to explicit Thue
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

A refusal disappearing was never counted as a closure: every closed curve has a compiled
completeness theorem.

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

## 5. Not covered

- **Positive `k`** (96 curves): `y² − k = x³` factors in a real quadratic field. This lattice
  argument is for imaginary `√−D`.
- **Irreducible Thue branches:** no Lean method here.
- **The Sage census:** external (mwrank ranks, elliptic logarithms), as before. Four of the 26
  closed curves have rank 2 in Sage. Their Lean lists do not use the rank at all.
