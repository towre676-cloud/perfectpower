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
     - The binomial rows $\binom n3=m^2$ and $\binom n2=m^3$ are still `SCAN_EVIDENCE_ONLY` for this reason.

2. **Bilu–Tichy atlas.**
   - *Problem:* extend the atlas from $F(x)=y^d$ to $F(x)=G(y)$ for $G$ triangular, binomial or Chebyshev. The atlas would be indexed by Bilu–Tichy standard pairs and would give explicit counting constants.
   - *Approach:* the first and second kinds reuse the radical and Pell machinery; the Dickson kinds need recurrence counting.
   - *Obstruction:* an algorithmic test for a standard-pair decomposition. Cross-check against Schäffer-type results.

3. **Read LeVeque (1964) in the primary source.** Confirm the exceptional patterns and the ring of solutions; see [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md) §3.

4. **Literature pass on Runge implementations.** Compare `runge.py` with Walsh (1992) and with Beukers–Tengely / Tengely (2005) before claiming anything about the enumerator.

## Formalisation

5. **Upstream candidates.** Each of these needs Mathlib naming, style and linter conformance, and a check that it does not already exist.
   - `isHit_exp_shift` / `exp_hasDensity`: $c\,a^n$ periodicity and rational density.
   - `monomial_isHit_iff` / `monomial_count`: $n^r$ is a $d$-th power iff $n$ is a $t$-th power.
   - `runge_pointwise`: the Runge reduction in integer form.
   - `ljunggren_hitSet` and the consecutive-product instances, as Archive or formal-conjectures-style entries.

6. **Theorem B in general.** Formalise the valuation characterisation for $c\,(n-\alpha)^r G^d$. Only the monomial case is done.

7. **Coefficient-bound lemmas for Theorem R.** Derive the hypotheses of `runge_uniform` from the constants $a(x_0)$ and $C(x_0)$, so that one certificate format covers every rigid $F$.

## Good first issues

- Reduce the piece count of the sandwich certificates. The $(10,2)$ certificate uses 283 pieces because the per-interval test $\mathrm{POS}(0)>\mathrm{NEG}(w)$ is crude. A midpoint shift or a Bernstein-basis test would merge intervals.
- Add families to `python/make_atlas_receipts.py`, each with a certification label.
- Extend `crosscheck/` to general Weierstrass models (e.g. $\binom n3$).
- Remove the unnecessary `have`s flagged by Batteries' `#lint` (see `FORMAL_AUDIT.md`).
