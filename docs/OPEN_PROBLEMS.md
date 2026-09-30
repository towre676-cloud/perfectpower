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

6. **Theorem B in general.** The valuation core is done (`PerfectPower/RadicalValuation.lean`): sign, rational denominators, the congruence form and the parametrisation $z=z_0w^t$. The count for $c(vn-u)^rG(n)^d$ is done, including the real power (`radical_asymptotic_int`). The pointwise reduction of a general $F$ is done (`PerfectPower/Continuation/`, `integer_radical_reduction`: rational Yun decomposition, exactly one bad layer, denominators cleared, all zeros $F(n)=0$ kept). *The count is done* (`Continuation/RadicalCountGeneral.lean`, `Decomposition.radical_count`): $|A(N)-\kappa N^{1/t}|\le K$, $\kappa\ge0$, $2\le t\mid d$. It covers the exceptional zeros ($\le\deg F$), both signs of the coefficient (flipped for odd $d$, a bounded count for even $d$), negative shifts (moved by at most $|u|$), and the solvability criterion `z0_dichotomy` (no $z\ge1$ works, so the count is bounded, or the least $z_0$ is minimal). *Positivity is decided* (`Continuation/KappaPositive.lean`): $\kappa>0$ iff there are infinitely many hits (`radical_count_pos`), iff a finite check succeeds (`radical_kappa_decide`). One hit with $z=Vn-U>0$ gives $z=z_0w^t$, and every $w'\equiv w\pmod V$ gives another. Taking $w'\le V$ and $z_0\mid |C|^{t-1}$ (`z0_dvd`) bounds the witness. *The error constant is explicit* (`Continuation/ExplicitK.lean`, `radical_count_explicit`): $|A(N)-\kappa N^{1/t}|\le 2V+2(U+V|U|)+|U|+2+\deg F$ for every $N$, with $(U,V)$ the numerator and denominator data of the bad rational root.

7. **Coefficient-bound lemmas for Theorem R.** Derive the hypotheses of `runge_uniform` from the constants $a(x_0)$ and $C(x_0)$, so that one certificate format covers every rigid $F$.

8. **Pell count in Lean.** *Done for the quadratic family (`pell_exact_count`).* The pointwise reduction of a general $F$ of Pell type (`integer_pell_reduction`) and its count (`Continuation/PellCountGeneral.lean`, `Decomposition.pell_count`: $|A(N)-\kappa\log N|\le K$) are done. The proof covers squarefree $Q$ hence nonzero discriminant, at most two branches $\pm\gamma_0$, cleared denominators, $A<0$ and $A=\square$ bounded, Mathlib's Pell unit for $A>0$ non-square, overlaps only at roots of $Q$, and the zeros of $F$. *Positivity is decided* (`Continuation/PellPositive.lean`). One point with $2An+B>0$ gives infinitely many (`branch_point_infinite`). A bounded search with explicit range, via the root box, a period $\le(2A)^2$ mod $2A$ and orbit growth, is `branch_infinite_iff_bounded`. For $F$: `pell_kappa_decide`. *The error constant is explicit* (`Continuation/PellExplicitK.lean`). One branch with any unit $(u,v)$ has $|A(N)-\kappa\log N|\le K$ for every $N>|B|$ (`pell_branch_explicit`), where $K=|B|+1+(2Z+3)^2(2A)^2K_c+(2Z+3)^2\log(2A+|B|)/\log\varepsilon$, with $Z=|\Delta|(1+u^2)$, $W=(2Z+2)(1+2\sqrt A)$ and $K_c=3+(2\log(W+|\Delta|)+\log(2+\sqrt{|\Delta|})+\log2)/\log\varepsilon$. The lower constant along each orbit is $X_j\ge\eta\varepsilon^j/(2+\sqrt{|\Delta|})$ (`orbit_lower`), which replaces the minimum over early terms. The roots lie in a box of $(2Z+3)^2$ points and each period is at most $(2A)^2$. For $F$: $|A(N)-\kappa\log N|\le\sum K_{\mathrm{branch}}+\deg F+2$ over at most two branches (`Decomposition.pell_count_explicit`), with $K_{\mathrm{branch}}=|B|+|C|$ for $A<0$ and $|\Delta|+|B|$ for $A$ a square. The fundamental unit is no longer a hypothesis, since Mathlib's `Pell.exists_of_not_isSquare` supplies one. The earlier text follows. The interfaces and orbit exhaustion are done (`PellGeneral.lean`: norm equation, pure periodicity modulo $2A$, good classes, finitely many representatives in the box $DY_0^2\le|\Delta|x_1^2$, geometric counting). The upper bound $A(N)=O(\log N)$ is compiled (`pell_count_log`). Missing: the exact asymptotic $A(N)=\kappa\log N+O(1)$, which needs the upper growth $X_j\le c\,\varepsilon^j$ and the per-class bookkeeping. The log-periodic second term (Theorem T2) is numerical and paper-level only.

## Good first issues

- ~~Reduce the piece count of the sandwich certificates.~~ Measured: a Bernstein or Horner-interval test only takes $(10,2)$ from 283 to 279 pieces, because single points at small $n$ dominate, and the reflective format (`Reflect.lean`) already made piece count cheap (12 KB for both certificates).
- ~~Port the Taylor-shift Runge certificates to the reflective checker.~~ Done (`Reflect.rungeCheck`; 136 KB → 31 KB).
- Add families to `python/make_atlas_receipts.py`, each with a certification label.
- Extend `crosscheck/` to quartic models $m^2=\text{quartic}$ with a rational point, keeping integrality through the conversion to Weierstrass form. Non-monic and shifted cubics and $m^3=$ quadratic are done in `crosscheck/genus1_sage.py`.
- Remove the unnecessary `have`s flagged by Batteries' `#lint` (see `FORMAL_AUDIT.md`).

## Added after the third review

9. **A kernel-checked completeness proof for one nonrigid genus-one family.**
   - *Done for empty lists (2026-09-29):* `MordellDescent.lean` proves, with no hypothesis, that $y^2=x^3+k$ has no integral points for 1163 values $0<|k|\le10^4$, including $k=7$ (so $n^3+7$ is never a square). This is Mordell's classical elementary descent ($k=c^3-Db^2$, $D\in\{1,2,-2\}$), with congruences checked by the kernel. 28 of these curves rest in the Sage census on an unproved rank.
   - *Done for one nonempty family:* `MordellFLT3.lean` proves that the integral points of $y^2=x^3-432u^6$ are exactly $(12u^2,\pm36u^3)$, for every $u\ne0$, by reduction to Mathlib's `fermatLastTheoremThree` (the curve is the Fermat cubic). So $n^3-432u^6=m^2$ iff $n=12u^2$.
   - *Done for two rank-one curves:* $y^2=x^3-2$ (`MordellMinus2.lean`, descent in ℤ[√−2]) and $y^2=x^3-4$ (`MordellMinus4.lean`, descent in ℤ[i]), unconditionally. `Transport.lean` carries complete lists through $n\mapsto rn+s$ with exact counts, and replaces the genus-one premise by one restricted to the image of the change of variables (`cubic_sound_image`).
   - *Current state for other nonempty lists:* apart from these, $y^2=x^3-13$, the FLT3 family and the Runge certificates, every nonempty genus-one list rests on Sage (`Genus1.lean` takes its point list as a hypothesis).
   - *Done for class number 2, as a template:* `ClassTwo.lean` proves the ideal-free class-group argument for every $D>0$, leaving a kernel-checked norm table per instance. Instances: $y^2=x^3-13$ (points $(17,\pm70)$), $y^2=x^3-5$ and $y^2=x^3-6$ (no points).
   - *Next:* generate `ClassTwo` instances from a Python search over $D$ (box ratio, $K$, table and Thue step), recording where the table fails. A failure means either a class group with 3-torsion or a Minkowski bound too weak for $K<8$; the fix is to extend `cube_of_table` to more $(k,\beta)$ cases. Then curves of rank at least 2 ($k=-11,-26$), where a descent must bound rather than solve. The empty-list descent's congruence mechanism cannot handle $D=3$: $q\equiv(x+c)^2\pmod3$ is never $\equiv2$, so no bad prime $\equiv2\pmod3$ can be forced. $D=-3$ (bad primes $\equiv\pm5\pmod{12}$) is open and would need a mod-12 variant. This corrects an earlier blanket claim about $D=\pm3$.
   - *Two routes:* (i) an independently checked height bound followed by an exact kernel-checked sieve up to it; or (ii) a formal descent for one well-chosen curve.
   - *Obstruction:* both are research projects. Any claim must be compared with Baanen–Best–Coppola–Dahmen (CPP 2023).
10. **Quartic genus-one models $m^2=$ quartic** with non-square leading coefficient, e.g. Ljunggren's $2n^4-1=m^2$ (hits $1,13$; a theorem of Ljunggren, 1942).
    - *Obstruction:* Sage has no integral-points routine for quartic models. Integral points of the quartic do not map to integral points of its Weierstrass model, so the cubic pipeline does not apply. What is needed is elliptic-logarithm bounds relative to a non-origin point (Tzanakis's method, or Magma's `IntegralQuarticPoints`). Until then these rows are evidence to $10^8$.
11. **Bilu–Tichy counting sequel.** Prove the complete integer counting theorem for one non-power $g$ in $f(x)=g(y)$, with integrality, congruence and multiplicity accounting, before any general atlas.
12. **Primary-source comparison.** Read Beukers–Tengely, Baanen–Best–Coppola–Dahmen, Bérczes–Evertse–Győry et al. (2023) and Flajolet–Gourdon–Dumas, and turn the provisional notes in `RELATED_WORK.md` and `CERTIFICATE_FORMAT.md` into a verified comparison. The build environment could not reach these texts.
13. **Filtered Pell families and effective finite plans.** *(a) is done* (`FilteredPell.lean`): the filtered family is infinite iff a root cycle modulo $M=|4Aa|$ meets an admissible state (`quadRoot_infinite_iff`), with kernel-checked certificates both ways. *(c) is done for catalogued plans* (`PlanCerts.lean`, `Generated/Plans.lean`). *The filtered count is done* (`FilteredCount.lean`: `filtered_count`, certified constants via `CountCert`). *Compact certificates and least solutions are done* (`FilteredAuto.lean`: `buildCert`, `quadRoot_count_auto`, `quadRoot_isLeast`; example: least solution $n=655680$). *One genus-one family is done* (`MordellFamily.lean`, empty answers). *Nonempty complete answers for single curves $y^2=x^3-D$ are done when the descent certificate passes* (`Descent.lean`; discovered by the compiler, 81 values $D<330$). Remaining there: $3\mid h(-4D)$, primitive-representation arguments, prime-only residue checks for larger $j$, and positive $k$. Remaining: filters on higher-degree reduced forms; emitting a plan theorem for any plan on request; certificates for large units, since the root box grows with $u$ (for $263n^2+1$, $u\approx8.4\cdot10^{19}$) and needs a continued-fraction (Lagrange–Legendre) or LMM root characterization in Lean; a genus-one family whose complete answer is a nonempty list; (b) below. The earlier text follows. **Filtered Pell families and effective finite plans** (the compiler's boundary, `CONSTRAINT_COMPILER.md` §7). (a) Decide in Lean when a Pell family survives a divisibility filter on the recovered root, as in $ay^2+by+c=F(n)$ with $2a\mid m-b$. The filter is periodic along each unit orbit, so a period criterion extending `branch_infinite_iff` should decide it; the compiler would then turn `STRUCTURED_FILTERED` into `STRUCTURED_INFINITE` or `COMPLETE_FINITE`. (b) Make `NOT_ENUMERATED` plans effective for more families, for example by extending the solved Mordell registry (`ClassTwo` instances) or by a certified Baker-type bound. (c) Prove the compiler's recognisers sound. For example, emit the chain as a Lean term that `Reduction.Exact.comp` accepts, instead of only citing theorem names.

**OEIS as a discovery layer** (`OEIS.md`). *Done:* the counting law for observed coordinates of
filtered orbits (`Observation.observed_count`) and the six-sequence theorem for $(3+\sqrt8)^j$.
*Open:*
- a first atlas against a real OEIS snapshot (oeis.org was unreachable from the release
  environment);
- reviewed definitions for the entries it confirms;
- eventual rather than strict monotonicity in `observed_count`;
- a clustering pass that proposes coordinate maps between entries sharing a norm equation;
- reading the leads for the 155 unresolved Mordell curves.
