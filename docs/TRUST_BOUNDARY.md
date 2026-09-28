# Trust boundary

This page states what each artifact in the repository establishes, what it takes on trust, and which statements depend on ineffective theorems. If a statement is not covered here, treat it as unverified.

## 1. What the Lean kernel proves

The Lean files are in `PerfectPower/`, including the machine-generated `PerfectPower/Generated/`. They are compiled against Lean `v4.20.0` and Mathlib `v4.20.0`, both pinned in `lean-toolchain` and `lake-manifest.json`. `audit/check_axioms.sh` checks every audited declaration: each may depend only on `propext`, `Classical.choice` and `Quot.sound`, so there is no `sorryAx`, no `Lean.ofReduceBool` and no custom axiom. The audited count is generated into the README by `make counts`.

Given that kernel, the following are theorems:

- **Definitions and elementary density facts.** The hit predicate, the count $A(N)$, the finite-support squeeze, exact finite surgery, and periodic rational density.
- **Rigid branch.** Either $F=G^d$ over $\mathbb Z$ or the hit set is finite; the density exists and is $0$ or $1$.
- **Explicit families.**
  - Twisted powers are finite.
  - For monomials $n^r$ the count is exact.
  - The hit indicator of $c\,a^n$ is $d$-periodic, so its density is $P/d$.
  - $2n^2+1$ has infinitely many square values and density zero.
  - Ljunggren's quartic has hit set exactly $\{3\}$.
- **Runge reduction in integer form** (`runge_pointwise`, `runge_finite`).
- **Generated hit sets.** Each statement of the form "for $n\ge1$, $F(n)=m^d$ is solvable iff $n\in H$", for the polynomials named in `PerfectPower/Generated/`. Python proposes the data, and Lean checks the proof. **A compiled generated theorem does not depend on the Python code being correct.**

**Unconditional function-field results.**
- Davenport's bound $2\deg(f^3-g^2)\ge\deg f+2$ (`davenport`), derived from Mathlib's Mason–Stothers (`Polynomial.abc`).
- Its sharpness (`davenport_sharp`).

**Conditional results (abc as a hypothesis).** The following are implications "`ABC ε C` ⇒ …":
- `hall_of_abc`, for coprime $x,y$;
- `pillai_bound_of_abc` and `pillai_finite_of_abc`, for coprime bases and $(a,b)\ne(2,2)$.

abc is an ordinary proposition passed as an argument, so the axiom audit is unaffected. These theorems say nothing about whether abc is true.

## 2. What the Lean kernel does not prove

- **The Python classifier's type assignments** (`atlas.py`): power, radical, Pell or finite. Nor does it prove the constants $\kappa$, the structural counts, or the shift spectrum. These are paper proofs, cross-checked against direct scans.
- **Siegel's theorem, and anything resting on it.** Through Theorem G of the research notes, it now replaces the secondary-source LeVeque statement. That covers the finite type of the atlas, the exponent spectrum $\{0,1\}\cup\{1/t\}$ as a complete list, and Corollary K. Siegel's and Boshernitzan's theorems are likewise outside the kernel.
- **That scan-only rows are complete.**
- **Hall's conjecture, Pillai's conjecture, or any uniform integral-point bound.** No part of the repository proves these, and none is claimed. See `FRONTIER_PLAN.md`.
- **Completeness of the Mordell census** (`data/mordell_census.csv`). That is Sage's claim: Mordell–Weil generators from mwrank, saturated, then elliptic-logarithm sieving. It is rigorous modulo the correctness of that software and of the proved rank. Lean checks no row of the census.
- **The Sage cross-validation.** That is an external computation: Mordell–Weil generators from mwrank, then elliptic-logarithm sieving. Lean never checks a Baker bound or a sieve.
- **The Python Runge enumerator and the v0.5 cutoff certificate as programs.** Their mathematics is Theorem R, whose reduction step is compiled. The Python code is tested, including planted-hit adversarial tests, but it is not verified.

## 3. Conditional and ineffective inputs

| Statement | Depends on | Effective? |
|---|---|---|
| Density zero outside the rigid branch (monograph §3) | Boshernitzan's equidistribution criterion | Qualitative only |
| Atlas finite type, exponent spectrum as a complete list, $O(N^{1/p})$ barrier, Corollary K | Siegel (standard form) via Theorem G; historically LeVeque (1964) | **No.** Siegel is ineffective. Brindza's effective version exists in principle, but its bounds are astronomical, and none is computed here. |
| Second proof of the 0–1 law (research notes §1) | Siegel, via Theorem G | **No.** It cannot replace the Boshernitzan argument where effectivity matters. |
| Shifted exponentials $c\,a^n+k$ finite | Thue, the S-unit theorem | Thue is effective via Baker; no bounds are computed |
| Each Mordell curve $y^2=x^3+k$ has finitely many integral points | Siegel; effective via Baker | Yes. The census lists come from Sage, not from explicit Baker bounds computed here. |
| Pillai: finiteness for fixed $(a,b)$ | Siegel, via Theorem G; effective via Baker | Not computed here |
| Pillai: finiteness uniform in the exponents; Hall's inequality | **abc (open)** | Formalised only as implications |
| Radical and Pell counts, Theorems P, B, C | Elementary; paper proofs | Yes, explicit |
| Rigid-branch complete hit lists | Theorem R; elementary | Yes, explicit |

**LeVeque is no longer a dependency.** Theorem G in the research notes derives the finite type directly from Siegel's theorem in its standard form. That form is stated in Hindry–Silverman (Theorem D.9.1) and Bombieri–Gubler (§7.3): an affine curve with $2g-2+n_\infty>0$ has finitely many $S$-integral points. The derivation is a Riemann–Hurwitz computation, $\chi=d'(1-S)$, carried out for each geometric component of $y^d=F(x)$. It treats common multiplicities, the normalisation of singular points, fields of definition, and integrality with bounded denominators after normalisation. Its status is `PAPER_PROOF`, not independently refereed. It is backed by randomized consistency checks: the genus comes out integral and non-negative, and $\chi<0$ exactly for the finite type. The LeVeque statement (Acta Arith. 9 (1964) 209–219) was only ever taken from secondary sources, because the primary paper could not be read in the build environment. It is now historical context and matches Theorem G's conclusion.

## 4. Epistemic label of every data row

Every data row carries one label: `receipts/atlas_benchmarks.json`, `data/families.csv`, `data/mordell_census.csv` (which also names the engine and version) and `data/pillai_gaps.csv`. The labels are:

| Label | Meaning |
|---|---|
| `LEAN_CERTIFIED` | A compiled Lean theorem states the complete hit set. |
| `PROVED_STRUCTURAL` | A paper proof of the structure (Theorems P, B, C), with counts cross-checked against scans. |
| `COMPLETE_HIT_LIST` | Theorem R plus exact arithmetic; not formalised for this instance. |
| `INDEPENDENT_COMPUTATION` | Our scan agrees with a certified external computation (Sage integral points; `receipts/cubic_crossval.json`). |
| `LEAN_REDUCTION_PLUS_INDEPENDENT_POINTS` | Lean proves the reduction to an elliptic curve, the congruence filtering, and that every surviving point is a hit (`PerfectPower/Binomial.lean`). Completeness of the curve's integral-point list is an explicit hypothesis, certified by Sage (`receipts/binomial_curves.json`: rank proved, basis saturated). |
| `CONDITIONAL_ON_UNPROVEN_RANK` | A Sage integral-point list computed from generators whose rank mwrank could not prove. Complete only if the rank is right. Used in `data/mordell_census.csv`. |
| `EXACT_WITHIN_BOUND` | An exhaustive enumeration, complete up to the stated bound and silent beyond it. Used in `data/pillai_gaps.csv`. |
| `SCAN_EVIDENCE_ONLY` | Finiteness is conditional on Siegel (Theorem G). The listed hits are those with $n\le10^5$. **No completeness claim is made.** |

The cubic cross-validation shows why the last label matters. Among the 622 curves $m^2=n^3+an+b$ with $|a|,|b|\le12$, a scan to $10^3$ would have missed hits on 18 curves, and a scan to $10^4$ on 4. The largest hit is $n=80327$, at $(a,b)=(-12,-10)$.
