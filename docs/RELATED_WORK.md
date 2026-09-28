# Related work and positioning

For each strand of prior work this page says three things: what the repository **reproduces**, what it **formalises**, and what, if anything, it **adds**.

**Status of this page.** It was written without library access. Bibliographic details come from memory and from search snippets. The primary texts of LeVeque, Brindza, Walsh and Tengely were not read in the build environment, because every host carrying them was blocked. Before any announcement, a literature pass must check each entry against the primary source, especially the Bilu–Tichy and Schinzel–Tijdeman lineage and all implementations of Runge's method.

## Positioning

- **The atlas and the exponent spectrum are a synthesis.** They combine LeVeque's finiteness theorem with classical Pell and valuation counting, and they add explicit constants and a decidable implementation. We make no priority claim for them.
- **The Schäffer reproduction confirms the machinery.** It does not extend Schäffer's result.
- **The second proof of the 0–1 law is conditional and ineffective.** It goes through Siegel's theorem, so it complements the Boshernitzan argument but cannot replace it.

The parts with a chance of being new are engineering and certification:

- the complete rigid-branch enumerator, together with its dyadic root-isolation strategy, but *only after* comparison with the existing Runge implementations listed below;
- the pipeline that emits Lean certificates, including the interval-sandwich certificates;
- the Lean formalisations themselves, most of which are new as formal statements whatever the novelty of the mathematics.

## By strand

**LeVeque, *On the equation $y^m=f(x)$*, Acta Arith. 9 (1964) 209–219.**
- The finiteness theorem is the input to the atlas's finite type; it is applied, not reproved.
- *Reproduced:* nothing.
- *Formalised:* nothing, and it is out of reach.
- *Adds:* the explicit description of the two exceptional patterns (Theorems B, C) with constants. This is almost certainly classical in substance.
- The statement is taken from secondary sources (see `TRUST_BOUNDARY.md` §3).

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
