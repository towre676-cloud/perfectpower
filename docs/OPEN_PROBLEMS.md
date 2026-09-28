# Open problems and good first issues

Each entry gives the precise problem, the current best approach, and the obstruction.

## Mathematics

1. **Effective finite type outside the Runge case.**
   - *Problem:* for non-rigid $F$ of finite type, turn "finite" into an explicit height bound and a certified hit list.
   - *Approach:*
     - Use Baker's method, with Brindza's refinements, for $y^d=F(x)$ with enough simple roots.
     - For $d=2$ and $\deg F\in\{3,4\}$, use Mordell–Weil generators with elliptic-logarithm sieving (Stroeker–Tzanakis, Gebel–Pethő–Zimmer). Sage implements the cubic Weierstrass case, and `crosscheck/cubics_sage.py` uses it.
   - *Obstruction:*
     - Quartic and non-monic models need a conversion to Weierstrass form that keeps track of integrality.
     - Lean can check only the final list against the sieve output, never the Baker step.
     - The binomial rows $\binom n2=m^3$ and $\binom n3=m^2$ are now `LEAN_REDUCTION_PLUS_INDEPENDENT_POINTS`: Lean proves the maps to $Y^2=X^3+1$ and $Y^2=X^3-36X$ and the hit lists given the curves' integral points, which remain a hypothesis certified by Sage.

2. **Bilu–Tichy atlas.**
   - *Problem:* extend the atlas from $F(x)=y^d$ to $F(x)=G(y)$ for $G$ triangular, binomial or Chebyshev. The atlas would be indexed by Bilu–Tichy standard pairs and would give explicit counting constants.
   - *Approach:* the first and second kinds reuse the radical and Pell machinery; the Dickson kinds need recurrence counting.
   - *Obstruction:* an algorithmic test for a standard-pair decomposition. Cross-check against Schäffer-type results.

3. **Referee Theorem G.** The finite type now follows from Siegel's theorem through $\chi=d'(1-S)$ (research notes §5), so LeVeque (1964) is context, not a dependency. The proof is a paper proof; an independent check of the normalisation and fields-of-definition steps is wanted. See [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) §3.

4. **Literature pass on Runge implementations.** Compare `runge.py` with Walsh (1992) and with Beukers–Tengely / Tengely (2005) before claiming anything about the enumerator.

## Formalisation

5. **Upstream candidates.** Each of these needs Mathlib naming, style and linter conformance, and a check that it does not already exist.
   - `isHit_exp_shift` / `exp_hasDensity`: $c\,a^n$ periodicity and rational density.
   - `monomial_isHit_iff` / `monomial_count`: $n^r$ is a $d$-th power iff $n$ is a $t$-th power.
   - `runge_pointwise`: the Runge reduction in integer form.
   - `ljunggren_hitSet` and the consecutive-product instances, as Archive or formal-conjectures-style entries.

6. **Theorem B in general.** The valuation core is done (`PerfectPower/RadicalValuation.lean`): sign, rational denominators, the congruence form and the parametrisation $z=z_0w^t$. The count is done up to the real power (`RadicalCount.lean`: $|vA(N)-RW|\le2Rv$). Still open: $W\sim(v/z_0)^{1/t}N^{1/t}$ in Lean, and the reduction from $c\,(n-\alpha)^rG^d$ with rational $\alpha$ and a nontrivial $G$.

7. **Coefficient-bound lemmas for Theorem R.** Derive the hypotheses of `runge_uniform` from the constants $a(x_0)$ and $C(x_0)$, so that one certificate format covers every rigid $F$.

8. **Pell count in Lean.** The interfaces and orbit exhaustion are done (`PellGeneral.lean`: norm equation, pure periodicity modulo $2A$, good classes, finitely many representatives in the box $DY_0^2\le|\Delta|x_1^2$, geometric counting). Missing: assembling $A(N)=\kappa\log N+O(1)$ from these pieces, which needs $X_j\asymp\varepsilon^j$ along each orbit. The log-periodic second term (Theorem T2) is numerical and paper-level only.

## Good first issues

- ~~Reduce the piece count of the sandwich certificates.~~ Measured: a Bernstein or Horner-interval test only takes $(10,2)$ from 283 to 279 pieces, because single points at small $n$ dominate, and the reflective format (`Reflect.lean`) already made piece count cheap (12 KB for both certificates).
- Port the Taylor-shift Runge certificates (`Generated/Runge.lean`, 136 KB) to the reflective checker as well.
- Add families to `python/make_atlas_receipts.py`, each with a certification label.
- Extend `crosscheck/` to quartic models $m^2=\text{quartic}$ with a rational point, keeping integrality through the conversion to Weierstrass form. Non-monic and shifted cubics and $m^3=$ quadratic are done in `crosscheck/genus1_sage.py`.
- Remove the unnecessary `have`s flagged by Batteries' `#lint` (see `FORMAL_AUDIT.md`).
