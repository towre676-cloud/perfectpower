# Related work and positioning

For each strand of prior work this page says three things: what the repository **reproduces**, what it **formalises**, and what, if anything, it **adds**.

**Source audit (2026-09-29).** The full texts of Beukers–Tengely (2005), Bérczes–Bugeaud–Győry–Mello–Ostafe–Sha (2023, Theorems 2.1–2.2), and Baanen–Best–Coppola–Dahmen (CPP 2023, Theorem 5.1 and §5) have been checked against the linked primary texts below. This is a *partial* literature audit. Entries without a primary-text link, including LeVeque, Bilu–Tichy, Schinzel–Tijdeman, Walsh and the Hall/Pillai comparisons, remain to be checked before an announcement. Bibliographic references alone do not verify the assertions attached to them. No novelty claim depends on an unaudited comparison.

## Positioning

- **The atlas and the exponent spectrum are a synthesis.** They combine Siegel's theorem, through the Euler-characteristic computation of Theorem G, with classical Pell and valuation counting. They add explicit constants, a decidable implementation and a formal exact-count interface for the infinite types (`Atlas.lean`). LeVeque's theorem (1964) states the same exceptional patterns and is historical context, not an input. We make no priority claim for the classification.
- **The Schäffer reproduction confirms the machinery.** It does not extend Schäffer's result.
- **The second proof of the 0–1 law is conditional and ineffective.** It goes through Siegel's theorem, so it complements the Boshernitzan argument but cannot replace it.

The parts with a chance of being new are engineering and certification:

- the specialized dyadic root-isolation strategy and its completeness certificates, subject to a direct example-by-example comparison with Beukers–Tengely's existing general Runge algorithm;
- the pipeline that emits Lean certificates, including the interval-sandwich certificates;
- the Lean formalisations themselves, most of which are new as formal statements whatever the novelty of the mathematics.

## By strand

**LeVeque, *On the equation $y^m=f(x)$*, Acta Arith. 9 (1964) 209–219.**
- Historical context only. The finite type is derived from Siegel's theorem by Theorem G, which recovers the same exceptional patterns. LeVeque is **not** an input.
- *Reproduced:* the list of exceptional patterns, through $\chi=d'(1-S)$.
- *Formalised:* the combinatorial half of that derivation (`chi_neg_iff`); the geometric half and Siegel remain external (`SuperellipticSiegel` in `Atlas.lean`).
- *Adds:* explicit constants for the two infinite nonpower patterns, with formal exact counts. This is almost certainly classical in substance.
- The exceptional multiplicity patterns are also stated in the introduction of [Bérczes et al. (2023)](https://arxiv.org/html/2310.09704v1), §2.2, as LeVeque's prior result. LeVeque's original paper has not been inspected [primary text pending].

**Brindza, Acta Math. Hungar. 44 (1984); and later effective work on superelliptic equations.**
- These make LeVeque's finiteness effective.
- Not used computationally here. Effective bounds are the open frontier (`OPEN_PROBLEMS.md`).

**Schinzel–Tijdeman, *On the equation $y^m=P(x)$*, Acta Arith. 31 (1976) 199–204.**
- If $P$ has at least two distinct roots, $m$ is effectively bounded.
- Cited only as a remark: counting all exponents at once. The resulting bound is too weak to compute with.

**Bilu–Tichy, *The Diophantine equation $f(x)=g(y)$*, Acta Arith. 95 (2000) 261–288 [primary text pending].**
- The standard-pair classification concerns infinitely many solutions with bounded denominator. The relationship between its cases and the atlas's fixed-power family $g=y^d$ has **not** been worked through here; in particular, the former assertion that the Dickson/Chebyshev types simply drop out is withdrawn.
- A sequel on general $g$ must first specialize each standard pair to $g=y^d$, impose integral and sign conditions, and separate an infinitude criterion from a counting theorem. No novelty claim is made here.

**Schäffer, *The equation $1^p+\cdots+n^p=m^q$*, Acta Math. 95 (1956) 155–189.**
- *Reproduced:* the list of infinite pairs $(1,2),(3,2),(3,4),(5,2)$ for $k\le10$, $d\le6$, with growth constants.
- *Formalised:* nothing.
- *Adds:* explicit counting constants, e.g. $\kappa=1/\log(5+2\sqrt6)$ for $(5,2)$, probably known to specialists.

**Runge (1887); Walsh, *A quantitative version of Runge's theorem on Diophantine equations*, Acta Arith. 62 (1992) 157–172 [primary texts pending]; [Beukers–Tengely, *An implementation of Runge's method for Diophantine equations*](https://arxiv.org/html/math/0512418v1) (2005).**
- **Prior art:** Beukers–Tengely §1 states a Runge–Schinzel Newton-polygon criterion, constructs an implementable algorithm over $\mathbb Q$ without Puiseux series or algebraic coefficients, and uses discriminants and resultants to isolate a finite search region (especially §2). Its examples are complete integral-point computations for nontrivial curves. Thus neither an effective Runge search nor use of rational polynomial operations can be claimed as new here.
- A defensible possible difference is a specialized algorithm for $y^d=F(x)$ using exact dyadic isolation of $D^dF-(P+t)^d$ and compact Lean-checkable completeness certificates. This remains a **candidate contribution**, pending benchmark cases and a comparison of hypothesis, cutoff size and certificate size. Beukers–Tengely treats more general bivariate curves; `runge.py` must not be described as a general improvement.
- *Formalised here:* the integer-form reduction (`runge_finite`) and generated instance certificates. The paper's general algorithm and completeness proofs have not been formalised here.

**Ljunggren (1943): $(x^n-1)/(x-1)=y^q$, case $n=5$, $q=2$.**
- *Reproduced and formalised:* the hit set $\{3\}$ (`ljunggren_hitSet`; also a generated certificate).
- *Adds:* a machine-checked statement only.

**Erdős–Selfridge, *The product of consecutive integers is never a power*, Illinois J. Math. 19 (1975) 292–301.**
- *Formalised:* the fixed instances $(k,d)$ with $d\mid k\le12$ as generated Lean theorems.
- *Adds:* machine-checked instances of a known theorem. These are engineering, not mathematics, and certificates beyond $k=12$ are not worth pursuing for their own sake.

**Stroeker–Tzanakis (1994); Gebel–Pethő–Zimmer (1994): elliptic logarithms for integral points.**
- This is the method behind Sage's `integral_points`, which provides the independent certificates in `receipts/cubic_crossval.json`.
- Not reimplemented, and not formalised.

**Siegel (1929), Baker (1966–), Thue (1909).**
- Background finiteness and effectivity. They are used only through the theorems above.

**Boshernitzan, *Uniform distribution and Hardy fields*, J. Anal. Math. 62 (1994).**
- The monograph's nonrigid density-zero argument. Qualitative.

**Nagell; Matthews; Robertson.**
- Nagell's bounds for generalized Pell equations, and the LMM algorithm of Matthews and Robertson.
- These are the standard algorithms behind `arith.py`.

**Grunwald–Wang (Wang 1948).**
- Used as a remark showing that prime-by-prime local sieving fails.

**Formal libraries.**
- Mathlib contains Pell-equation theory (`Mathlib.NumberTheory.Pell`), which our Pell example does not use.
- We have not yet searched Mathlib, the Mathlib Archive or the formal-conjectures collection for existing formalisations of Ljunggren or Erdős–Selfridge instances. That search is part of the upstreaming plan.

## Frontier push: Hall, Pillai and uniform bounds

**Hall (1971); Danilov (1982); Elkies (2000); Jiménez Calvo–Herranz–Sáez (2009); Aanderaa–Kristensen–Ruud (2017).**
- Hall conjectured $|x^3-y^2|\gg x^{1/2}$. Danilov showed that the exponent $\tfrac12$ cannot be improved and that the constant in the original conjecture fails. The modern form is $|x^3-y^2|\gg_\varepsilon x^{1/2-\varepsilon}$, which is open.
- Record ratios come from lattice-reduction searches. For example, Elkies' $x=5853886516781223$ gives $x^3-y^2=1641843$ and $r=\sqrt x/|k|\approx46.60$; this repository verifies the arithmetic only (`receipts/hall_literature_check.json`).
- *Reproduced:* nothing new. The census (`data/mordell_census.csv`) validates the pipeline for $|k|\le10^4$ and does not approach record territory.
- *Formalised:* the abc ⇒ Hall implication in the coprime case (`hall_of_abc`).

**Mason (1984), Stothers (1981); Davenport (1965); Birch–Chowla–Hall–Schinzel (1965).**
- The polynomial abc theorem is in Mathlib (`Polynomial.abc`, by Baek and Lee).
- *Formalised here:* Davenport's bound as a corollary (`davenport`), and sharpness via the Birch–Chowla–Hall–Schinzel example $f=X^2+2$, $g=X^3+3X$ (`davenport_sharp`).
- This is a candidate for Mathlib or the Mathlib Archive; first check that it does not already exist.

**Pillai (1936); Mihăilescu (2004).**
- Pillai conjectured that each $k$ is a difference of perfect powers only finitely often; this is open. Mihăilescu settled $k=1$ (Catalan).
- *Reproduced:* the empirical gap set up to $10^{18}$ (`data/pillai_gaps.csv`), exact within that bound. The list of $k\le100$ with no representation (6, 14, 34, 42, …) agrees with the conjectural list in the literature.
- *Formalised:* abc ⇒ Pillai, uniformly in the exponents, for coprime bases (`pillai_finite_of_abc`).

**Lang's conjecture; Hindry–Silverman (1988).**
- Lang conjectured that the number of integral points on a quasi-minimal model is at most $C^{1+\mathrm{rank}}$.
- Hindry–Silverman bound the number of ($S$-)integral points in terms of the rank, the number of bad primes and the Szpiro ratio of the curve. Uniformity in the curve therefore rests on Szpiro's conjecture. This is from memory; check the precise statement against the paper.
- The census supplies counts, ranks and discriminants. The uniformity plots are **numerical evidence** only.

**[Bérczes, Bugeaud, Győry, Mello, Ostafe and Sha, *Explicit bounds for the solutions of superelliptic equations over number fields*](https://arxiv.org/html/2310.09704v1) (2023).**
- **Correction:** Bérczes–Evertse–Győry is an *earlier* work cited by this paper, not its author list. §2.2 defines $m_i=m/\gcd(m,e_i)$ from the root multiplicities $e_i$. Theorem 2.1 gives explicit height bounds outside LeVeque's exceptional tuples $(a,1,\ldots,1)$ and $(2,2,1,\ldots,1)$; it includes multiple-root cases. Theorem 2.2 also bounds the varying exponent under its stated nonunit hypothesis on $y$.
- This is strong prior art for **effective** finite-type bounds. The repository's Siegel-premise route is ineffective, while `runge.py` handles an algorithmic subcase. Importing Theorem 2.1 into Lean would require formalizing its full hypotheses and a bound usable by the enumeration algorithm; a citation is not an executable cutoff.
- *Formalised here:* nothing from this paper.

**Mordell, *Diophantine Equations* (Academic Press, 1969), ch. 26 [primary text pending].**
- The elementary argument that $y^2=x^3+k$ has no integral points when $k=(4m-1)^3-4n^2$ and $n$ has no prime factor $\equiv3\pmod4$, and variants. This is classical; the case $k=7$ is a textbook exercise.
- *Formalised here:* a parametrised version (`MordellDescent.no_points`, $D\in\{1,2,-2\}$, congruence mod $M$ checked by the kernel) and 1163 generated instances for $0<|k|\le10^4$.
- *Adds:* no new mathematics. The contribution is a kernel-checked, hypothesis-free completeness statement plugged into the hit-list interface, and an independent confirmation of 1163 empty rows of the Sage census, 28 of them rows where Sage's rank was unproved.

**Euler; the Fermat cubic $a^3+b^3=c^3$ and $y^2=x^3-432$ [classical].**
- The birational map between the Fermat cubic and $y^2=x^3-432$ is classical. `MordellFLT3.lean` uses only the polynomial identity $(36u^3+y)^3+(36u^3-y)^3=(6ux)^3$ and Mathlib's `fermatLastTheoremThree` (Mathlib contributors, 2024).
- *Adds:* a kernel-checked complete, nonempty hit list for an infinite family ($n^3-432u^6$), plugged into the hit-list interface. No new mathematics.

**[Baanen, Best, Coppola and Dahmen, *Formalized Class Group Computations and Integral Points on Mordell Elliptic Curves*](https://arxiv.org/html/2209.15492v2) (CPP 2023).**
- Theorem 5.1 and §5 give a Lean 3 class-group descent for $y^2=x^3+c$ under explicit negative-squarefree, congruence and class-number hypotheses. §4 computes class numbers for $c=-1,-2,-5,-6,-13$; §5 describes complete integral-point results for selected instances. **Kernel-checked genus-one completeness therefore predates this repository.**
- `Genus1.lean` currently derives lists only under a named Sage point-list hypothesis, so its 399 instances are *conditional reductions*, not a replacement for those completeness proofs. A concrete next step is to choose a compatible $c$, translate its signed integral-point statement to positive $n$ and $m^2=F(n)$, and port or reprove the descent under this repository's Lean 4/Mathlib version. Verify the resulting theorem with the standard-axiom audit before advertising a new complete instance.
- Any claim of novelty should concern the integration of a completed proof into the hit-count and certificate interface, not the first formal Mordell solution.
- Their method (class groups, negative $c$) and the elementary descent in `MordellDescent.lean` (quadratic-residue obstructions, both signs of $k$, empty lists only) cover different curves; neither subsumes the other. Overlap of individual $k$ values has not been checked against their tables.

**Flajolet, Gourdon, Dumas, *Mellin transforms and asymptotics: harmonic sums*, TCS 144 (1995) 3–58.**
- The general machinery behind Theorem T2's log-periodic term. T2's novelty, if any, is limited to its arithmetic input: the Pell orbit and class decomposition, the shift $-B/(2A)$ and the exact correction $\delta_j$.

**Proof by reflection and verified numerical certificates (e.g. LeanCert) [unverified].**
- `pp-cert/1` (`docs/CERTIFICATE_FORMAT.md`) follows the standard search/check/interpret separation. A comparison of formats and checking times is future work.

**Bilu–Tichy and counting [primary text pending].** Its standard-pair framework for bounded-denominator solutions does not by itself count positive integral $x$: integrality, sign, local conditions and parametrisation multiplicity require separate arguments. The Pell and radical modules provide counts for particular fixed-power families. A sequel should specialize the standard pairs rigorously and first prove a complete integer count for one non-power $g$ family.


## Audit boundary and immediate comparison experiment

The three full-text links above support only the statements attributed to those papers. The remaining references on this page retain their pre-audit status; in particular the historical priority of individual counting constants, Walsh's exact bounds, and the Hall/Pillai record comparisons have not been certified by this pass.

For a reproducible Runge comparison, select one $y^d=F(x)$ example within both algorithms' hypotheses. Record the same input polynomial, the actual infinity-branch condition, each cutoff, the finite candidates, and the independent completeness argument. Time and certificate size can then be reported with versioned inputs. The comparison must distinguish an exact enumerator from a Lean proof of its finite result.
