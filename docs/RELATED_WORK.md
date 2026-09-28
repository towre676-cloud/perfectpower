# Related work and positioning

For each strand of prior work this page says three things: what the repository **reproduces**, what it **formalises**, and what, if anything, it **adds**.

**Status of this page.** It was written without library access. Bibliographic details come from memory, from search snippets and from an external reviewer's notes. The build environment's network policy blocks arXiv and the journal hosts, so **no entry below has yet been checked against its primary text.** Entries marked [unverified] carry claims about the content of a paper that we could not read. Before any announcement, a literature pass must check each entry against the primary source. That pass should cover especially Bilu–Tichy, Schinzel–Tijdeman, the implementations of Runge's method, the 2023 explicit superelliptic bounds and the formal Mordell work. The repository makes no novelty claim that depends on these comparisons.

## Positioning

- **The atlas and the exponent spectrum are a synthesis.** They combine Siegel's theorem, through the Euler-characteristic computation of Theorem G, with classical Pell and valuation counting. They add explicit constants, a decidable implementation and a formal exact-count interface for the infinite types (`Atlas.lean`). LeVeque's theorem (1964) states the same exceptional patterns and is historical context, not an input. We make no priority claim for the classification.
- **The Schäffer reproduction confirms the machinery.** It does not extend Schäffer's result.
- **The second proof of the 0–1 law is conditional and ineffective.** It goes through Siegel's theorem, so it complements the Boshernitzan argument but cannot replace it.

The parts with a chance of being new are engineering and certification:

- the complete rigid-branch enumerator, together with its dyadic root-isolation strategy, but *only after* comparison with the existing Runge implementations listed below;
- the pipeline that emits Lean certificates, including the interval-sandwich certificates;
- the Lean formalisations themselves, most of which are new as formal statements whatever the novelty of the mathematics.

## By strand

**LeVeque, *On the equation $y^m=f(x)$*, Acta Arith. 9 (1964) 209–219.**
- Historical context only. The finite type is derived from Siegel's theorem by Theorem G, which recovers the same exceptional patterns. LeVeque is **not** an input.
- *Reproduced:* the list of exceptional patterns, through $\chi=d'(1-S)$.
- *Formalised:* the combinatorial half of that derivation (`chi_neg_iff`); the geometric half and Siegel remain external (`SuperellipticSiegel` in `Atlas.lean`).
- *Adds:* explicit constants for the two infinite nonpower patterns, with formal exact counts. This is almost certainly classical in substance.
- The statement was only ever available to us from secondary sources [unverified].

**Brindza, Acta Math. Hungar. 44 (1984); and later effective work on superelliptic equations.**
- These make LeVeque's finiteness effective.
- Not used computationally here. Effective bounds are the open frontier (`OPEN_PROBLEMS.md`).

**Schinzel–Tijdeman, *On the equation $y^m=P(x)$*, Acta Arith. 31 (1976) 199–204.**
- If $P$ has at least two distinct roots, $m$ is effectively bounded.
- Cited only as a remark: counting all exponents at once. The resulting bound is too weak to compute with.

**Bilu–Tichy, *The Diophantine equation $f(x)=g(y)$*, Acta Arith. 95 (2000) 261–288.**
- An effective classification of when $f(x)=g(y)$ has infinitely many solutions with bounded denominator, in terms of standard pairs.
- The atlas is the specialisation $g=y^d$, where the Dickson/Chebyshev kinds drop out. Generalising the atlas to standard pairs is the proposed next monograph part (`OPEN_PROBLEMS.md`).
- *Adds today:* nothing.

**Schäffer, *The equation $1^p+\cdots+n^p=m^q$*, Acta Math. 95 (1956) 155–189.**
- *Reproduced:* the list of infinite pairs $(1,2),(3,2),(3,4),(5,2)$ for $k\le10$, $d\le6$, with growth constants.
- *Formalised:* nothing.
- *Adds:* explicit counting constants, e.g. $\kappa=1/\log(5+2\sqrt6)$ for $(5,2)$, probably known to specialists.

**Runge (1887); Walsh, *A quantitative version of Runge's theorem on Diophantine equations*, Acta Arith. 62 (1992) 157–172; Beukers–Tengely, *An implementation of Runge's method for Diophantine equations* (2005), and Tengely's thesis (Leiden, 2005).**
- This is **prior art for the rigid-branch enumeration.**
- Walsh gives explicit bounds. Tengely implements Runge's method for equations of the shape $y^2=F(x)$, among others.
- `runge.py` must be compared against these before any claim. Plausible differences to check are:
  - exact dyadic root isolation of $D^dF-(P+t)^d$ instead of bounding and searching;
  - general $d$;
  - the Lean certificate output.
- *Formalised:* the Runge reduction in integer form (`runge_finite`), plus generated certificates.

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

**Bérczes, Evertse, Győry et al., *Explicit bounds for the solutions of superelliptic equations over number fields* (arXiv:2310.09704) [unverified].**
- By the reviewer's account, this treats the multiple-root superelliptic regime with explicit bounds. That is the same regime as the atlas's finite type, which the repository handles only ineffectively (via Siegel) outside the Runge branch.
- It is the natural source for turning `SuperellipticSiegel` into an effective statement. It belongs in the introduction of any paper, not in a deferred roadmap.
- *Formalised:* nothing.

**Baanen, Best, Coppola, Dahmen, *Formalized class group computations and integral points on Mordell elliptic curves* (CPP 2023, arXiv:2209.15492) [unverified].**
- Formal complete solutions of selected Mordell equations. Any claim here about formal completeness of genus-one hit lists must be compared with it.
- The repository does **not** yet prove completeness of any genus-one list in Lean. `Genus1.lean` proves hit lists *from* a named Sage point hypothesis, so it is complementary.

**Flajolet, Gourdon, Dumas, *Mellin transforms and asymptotics: harmonic sums*, TCS 144 (1995) 3–58.**
- The general machinery behind Theorem T2's log-periodic term. T2's novelty, if any, is limited to its arithmetic input: the Pell orbit and class decomposition, the shift $-B/(2A)$ and the exact correction $\delta_j$.

**Proof by reflection and verified numerical certificates (e.g. LeanCert) [unverified].**
- `pp-cert/1` (`docs/CERTIFICATE_FORMAT.md`) follows the standard search/check/interpret separation. A comparison of formats and checking times is future work.

**Bilu–Tichy and counting.** Bilu–Tichy classify when $f(x)=g(y)$ has infinitely many rational solutions with bounded denominator. That does not by itself give the number of positive *integral* $x$: integrality, local congruences, compositions and parametrisation multiplicity can change or remove the family. The atlas's Pell and radical modules are the $g=y^d$ case of such a counting theory, and a sequel should first prove the complete integer count for one non-power $g$ family.

