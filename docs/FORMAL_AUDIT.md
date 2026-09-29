# Formal boundary and audit

**Release 0.6.** The Lean library builds with Lean `v4.20.0` against Mathlib tag `v4.20.0`. The dependency is a git requirement, with its exact revision recorded in `lake-manifest.json`.

In the build environment of this release, the Mathlib cache and release servers were unreachable, so Mathlib was compiled from source (about 1900 modules). CI uses `leanprover/lean-action` and the ordinary cache.

`./audit/check_axioms.sh` runs `#print axioms` on every audited declaration; the current number is generated into the README by `make counts`, so it is never typed by hand. It fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`, which excludes both `sorryAx` and custom axioms. This check passed for release 0.6. `audit/Lint.lean` runs Batteries' `#lint` over the hand-written library and reports 0 errors; the generated certificates are excluded, since their redundant `have`s are harmless machine output. Both checks are part of `make verify`. The results below are therefore `LEAN_VERIFIED` in the sense of [the receipt policy](RECEIPTS.md).

## What changed from 0.5

The 0.5 sources had never been elaborated. On the first build `Basic.lean` and `Dichotomy.lean` compiled unchanged, and `Density.lean`, `Rigid.lean` and `Estimates.lean` failed. The failures and repairs were:

- **`Density.lean`, `limsup_le_of_tendsto_sub`:**
  - A coboundedness lemma received an `Eventually` where it expects a pointwise bound.
  - The final ε-step compared `u n` with `limsup v + ε/2` when only `limsup v + ε` is available. The mathematical statement was correct; the tactic proof was not.
- **`Rigid.lean`:**
  - `binom_remainder`: an `omega` goal needed a rewrite in the goal as well as the hypothesis.
  - `trunc_induction`: an `omega` goal mixed `e * Q.natDegree` with `e * q`, and needed a rewrite by `hQd`.
  - `trunc_induction`: a `field_simp` residue needed `rw [← hN1eq]; ring`.
- **`Estimates.lean`:**
  - A missing `ring` after `field_simp` in `abs_sub_ge_inv`.
  - `le_self_pow` no longer applies to `ℝ` in this Mathlib; replaced by `le_self_pow₀`.
- **Deprecation renames:** `pow_le_pow_left₀`, `div_lt_div_iff₀`, `Finset.card_insert_of_notMem`, and `∑ x ∈ s`.
- **Imports:** `import Mathlib` was replaced by the five modules actually needed.

No theorem statement of 0.5 was changed.

## What the build certifies

| File | Declarations (all compiled, standard axioms only) |
|---|---|
| `Basic.lean` | `IsHit`, `hitSet`, `A`, `ratio`, `HasDensity`, `H`; `H_eq_of_hasDensity` |
| `Density.lean` | `A_succ`, `A_le`, `hasDensity_zero_of_finite`, `A_sub_eq_const` (exact surgery identity), `H_surgery`, `hasDensity_of_periodic` |
| `Rigid.lean` | `exists_denominator`, `frac_periodic`, `integral_closure_step` (Gauss content), `binom_remainder`, `trunc_induction`, `exists_truncated_root` |
| `Estimates.lean` | `abs_sub_ge_inv`, `abs_sub_one_le_abs_pow_sub_one`, `analytic_eventually`, `pow_diff_bound`, `eventually_no_hit` |
| `Dichotomy.lean` | `rigid_dichotomy`: rigid $F\ne0$ is $G^d$ over $\mathbb Z$, or has finitely many hits |
| `ZeroOne.lean` (new) | `hasDensity_one_of_pow`, **`rigid_zero_one`** (density exists and is $1$ or $0$ on the rigid branch), `rigid_H_mem`, `pow_of_mul_pow_eq`, `twisted_hits_subset`, `twisted_finite`, `twisted_density_zero` |
| `Monomial.lean` (new) | `rat_pow_eq_nat`, **`monomial_isHit_iff`** ($n^r$ is a $d$-th power iff $n$ is a $t$-th power, $t=d/\gcd(r,d)$), `monomial_hitSet`, **`monomial_count`** ($A(N)=\#\{w\in[1,N]: w^t\le N\}=\lfloor N^{1/t}\rfloor$) |
| `Examples.lean` (new) | `consecutive_four_hitSet` ($n(n+1)(n+2)(n+3)$ is never a square), **`ljunggren_hitSet`** (the hit set of $1+n+n^2+n^3+n^4$, $d=2$, is exactly $\{3\}$); both by the Runge squeeze |
| `Pell.lean` (new) | `hasDensity_zero_of_count_le`, `pell_descent` (every solution of $m^2-2n^2=1$ lies on the orbit of $(1,0)$), `pell_hit_iff`, **`pell_hitSet_infinite`**, `pell_count_le` ($A(N)\le\lfloor\sqrt N\rfloor$), **`pell_hasDensity_zero`**: $2n^2+1$ has infinitely many square values and density zero. This is the first **nonrigid** density-zero theorem in the kernel, proved without Boshernitzan or LeVeque. |
| `Exponential.lean` (new) | `isHit_exp_shift`, **`exp_hasDensity`**: for $a\ne0$ the hit density of $c\,a^n$ exists and equals $P/d$, the periodic core of Theorem E. **`two_pow_hasDensity_half`**: $2^n$ is a square with density exactly $1/2$. |
| `RadicalValuation.lean` (new) | The valuation core of Theorem B for general $c$:
- `exists_pow_iff_factorization`: $n$ is a $d$-th power iff $d\mid v_p(n)$ for all $p$.
- `isHit_iff_natAbs`: the signed version.
- `isHit_iff_rat`: a rational $d$-th power that is an integer is an integer $d$-th power, i.e. the denominator step.
- **`mul_pow_isPow_iff_congr`**: if $cz_0^r$ is a $d$-th power, then $cz^r$ is one iff $v_p(z)\equiv v_p(z_0)\pmod t$ for all $p$.
- **`mul_pow_isPow_iff_param`**: if moreover $z_0$ is minimal, the solutions are exactly $z=z_0w^t$.

The count is in `RadicalCount.lean`. |
| `RadicalCount.lean` (new) | The count of Theorem B:
- `count_periodic_le` / `le_count_periodic`: a $q$-periodic predicate with $R$ solutions per period has $RW/q+O(R)$ solutions below $W$.
- **`radical_hits_card`**: the hits $n\in[1,N]$ of $c(vn-u)^r$ with $vn>u$ are in bijection with the $w\in[1,W]$ satisfying $v\mid z_0w^t+u$, where $W$ is the largest $w$ with $z_0w^t+u\le vN$.
- **`radical_count_bound`**: $|v\,A(N)-R\,W|\le 2Rv$, with $R$ the number of good residues of $w$ modulo $v$.

The final step $W=\lfloor((vN-u)/z_0)^{1/t}\rfloor=(v/z_0)^{1/t}N^{1/t}+O(1)$ is in `RadicalAsymp.lean`. A sanity instance (squares up to 10) checks that the hypotheses are satisfiable. |
| `PellGeneral.lean` (new) | Interfaces for Theorem Q, for general $An^2+Bn+C$:
- **`quadratic_isHit_iff_norm`**: $P(n)$ is a square iff $(2An+B)^2-4AY^2=B^2-4AC$.
- `unitAct_norm`, `unitOrbit_norm`: a norm-one unit preserves the norm form along the orbit.
- **`unitOrbit_periodic`**: the orbit is purely periodic modulo every $M>0$, via a permutation of $(\mathbb Z/M)^2$ of finite order.
- **`goodClass_hits`**: a good index $r$ ($X_r\equiv B \bmod 2A$) stays good at $r+kP$, and each of those orbit points gives a hit.
- `geometric_count_le` / `le_geometric_count`: a sequence between $c_1E^j$ and $c_2E^j$ has $\log N/\log E+O(1)$ terms $\le N$, the source of the factor $1/(P\log u)$.

- **`pell_descent_box`**, **`pell_box_finite`**, **`pell_orbits_exhaust`**: each solution of $X^2-DY^2=\Delta$ with $X>0$, $Y\ge0$ is a nonnegative power of the unit applied to a representative in the finite box $DY_0^2\le|\Delta|x_1^2$. The proof is an integer descent: the inverse unit keeps $X>0$ and $Y\ge0$ and strictly lowers $X$ outside the box. This is a weak form of Nagell's bound.

- **`unitOrbit_growth`**, **`pell_count_log`**: along a forward orbit $X_j\ge X_0x_1^j$ and $Y_j\ge0$. Hence the hits $n\le N$ of any quadratic $An^2+Bn+C$ with $A>0$, given a unit, number at most $K(\lfloor\log_{x_1}(2AN+|B|)\rfloor+1)+|B|$, with $K$ the number of orbit representatives: $A(N)=O(\log N)$.

**Not formalised:** the matching lower bound and the exact constant, $A(N)=\kappa\log N+O(1)$. That needs the upper growth $X_j\le c\,\varepsilon^j$ and the class bookkeeping. |
| `ProfileG.lean` (new) | The combinatorial half of Theorem G:
- **`S_le_one_iff`**: $S=\sum(1-1/t_i)\le1$ iff at most one $t_i>1$ or the $t_i>1$ are $\{2,2\}$.
- **`chi_eq`**, **`chi_neg_iff`**: for *every* $d>0$ and every multiplicity list, the integer $\chi=d'-\sum(d'-d'/t_i)$ equals $d'(1-S)$, and $\chi<0$ iff the profile is not of power, radical or Pell type. This is a universal theorem, not a table.
- **`profile_table_ok`**: for all $2\le d\le12$ and all 271 multiplicity profiles of degree $\le12$, the Riemann–Hurwitz genus $(2-n_\infty-\chi)/2$ is a nonnegative integer, $t_i\mid d'$, $\chi=d'(1-S)$ in exact arithmetic, and $\chi<0$ iff the profile is not exceptional. The kernel checks all of this by `decide +kernel`.

The geometric half (Kummer and Riemann–Hurwitz for the normalisation) remains a paper proof. It is tested against Singular's normalisation genus and Sage's places at infinity by `crosscheck/theorem_g_sage.py`. |
| `Reflect.lean` (new) | Verified certificate checkers (proof by reflection):
- Polynomial arithmetic on coefficient lists (`ev`, `padd`, `pmul`, `ppow`, `shift`), with evaluation lemmas (`ev_shift`: Taylor shift).
- The interval test $\mathrm{POS}(0)>\mathrm{NEG}(w)$ and the tail test, with soundness (`intervalPos_sound`, `tailPos_sound`).
- **`check_sound`**: a sandwich certificate (a segment cover of $[1,c)$ plus a tail) that passes `check` gives the complete hit set.
- `mordellOK_sound` for census points. |
| `RadicalAsymp.lean` (new) | `radW_spec`, `radW_approx` (the cutoff $W=\lfloor((vN-u)/z_0)^{1/t}\rfloor$ is $(v/z_0)^{1/t}N^{1/t}+O(1)$, by subadditivity of $x^{1/t}$). **`radical_asymptotic`**: $|A(N)-\kappa N^{1/t}|\le2R+(R/v)((u/z_0)^{1/t}+1)$ with $\kappa=(R/v)(v/z_0)^{1/t}$, which is $0$ when $R=0$. **`radical_asymptotic_int`**: the same over all $n\in[1,N]$ for $c(vn-u)^rG(n)^d$ as integer `IsHit` statements, with the zeros of $G$ and the $n$ with $vn\le u$ counted in the constant. `isHit_mul_pow_iff`. |
| `PellExact.lean` (new) | Canonical orbit roots (`IsRoot`, `exists_root`, `root_unique`, `roots_finite`); growth at the rate of $\varepsilon=u+v\sqrt D$ (`orbit_fst_bracket`); counting near a geometric sequence (`count_near_geometric`); per class and per orbit (`class_count`, `orbit_count`). **`pell_exact_count`**: $|A(N)-\kappa\log N|\le K$ for $N\ge N_0$, $\kappa=(\sum_\rho g_\rho/P_\rho)/\log\varepsilon$. |
| `Atlas.lean` (new) | The interface: `atlas_power`, `atlas_radical`, `atlas_pell` (exact constants), and **`atlas_finite`** under the named premise `SuperellipticSiegel`, with profiles given by a Yun decomposition. |
| `MordellDescent.lean`, `Generated/MordellDescent.lean` (new) | **Unconditional** genus-one completeness. For $k=c^3-Db^2$, $D\in\{1,2,-2\}$: `no_points` proves $y^2\ne x^3+k$ for all integers $x,y$ from (i) a congruence mod $M\in\{8,16,32\}$, checked by kernel evaluation (`CongOK`), forcing $q=x^2-cx+c^2$ odd with a residue mod 8 outside the residues of primes where $-D$ is a square; (ii) `exists_bad_prime`, a multiplicative-closure induction; (iii) `good_of_dvd`, from Mathlib's supplementary laws for $-1$, $-2$, $2$; (iv) a divisor certificate $b=2^jb_1$, $b_1\mid u^2+D$ (`goodDivisors_of_cert`). 1163 generated instances, e.g. `mordell_7`. No point list, rank or external computation is assumed. |
| `MordellMinus2.lean` (new) | **Positive rank, unconditional.** Euclidean structure on ℤ[√−2] by integer rounding (`rdiv`, `norm_mod_lt`: remainder norm ≤ ¾ of the divisor's); coprimality of $y\pm\sqrt{-2}$ by an explicit Bézout identity; cube extraction by Mathlib's `exists_associated_pow_of_mul_eq_pow'`; `points`: the integral points of $y^2=x^3-2$ are $(3,\pm5)$; `hitSet`. |
| `MordellMinus4.lean` (new) | **Positive rank, unconditional.** In Mathlib's Euclidean ℤ[i] (`unit_is_cube`): the odd case gives $(5,\pm11)$; the even case goes through $y_1^2+1=2x_1^3$ and the Thue equation $(a-b)(a^2+4ab+b^2)=1$ to $(2,\pm2)$. `points`, `hitSet`. |
| `Continuation/RationalYun.lean`, `PowerSplit.lean`, `RationalHit.lean`, `ProfileReduction.lean`, `DenominatorReduction.lean` (new; 31 theorems, 9 audited definitions) | **Generic input.** `Decomposition F` over ℚ[X] (monic squarefree pairwise-coprime layers, constant included) exists for every nonzero $F$ (`exists_decomposition`, `exists_integer_decomposition`, `decomposition_iff_nonzero`). The old ℤ[X]-coprime interface cannot have this: `not_isCoprime_integer_X_X_add_two` versus `isCoprime_rational_X_X_add_two`. `powerSplit` and `weighted_degree` extract the full $d$-th power; `badDegree`. **Pointwise Theorems B, C:** `integer_radical_reduction` (bad degree 1 ⟹ $F(n)\in\mathcal H_d\iff F(n)=0\lor \mathrm{lc}\,v^{d-r}(vn-u)^r\in\mathcal H_d$) and `integer_pell_reduction` (square branches of a monic quadratic); `opposite_squares_iff_zero`. Counts for general $F$ are not yet derived from them. |
| `ClassTwo.lean` (new) | **The class-group template, all $D>0$.** `exists_short` (Thue's pigeonhole lemma: a short nonzero vector in the lattice $x\mid a-tb$); `box` (the pigeonhole box $\lfloor\sqrt{rx/t}\rfloor\times\lfloor\sqrt{tx/r}\rfloor$); identities `Q2_eq`, `norm_id`, `idR`, `idI` encoding $\alpha\bar v^3\in x^3R$ and $N(\beta)=k^3$; `short_relation` (the Minkowski step); `TableOK`, `HalvesOK`, `halvesOK_of_mod8`; `cube_of_table`: $y+\sqrt{-D}$ is a cube. |
| `MordellMinus13.lean`, `MordellMinus5.lean`, `MordellMinus6.lean` (new) | Instances of `ClassTwo`. `table13`/`table5`/`table6` (kernel), the Thue step, and the results: $y^2=x^3-13$ has points $(17,\pm70)$ (`points`, `hitSet`); $y^2=x^3-5$ and $y^2=x^3-6$ have none (`no_points`, `not_isHit`). |
| `Transport.lean` (new) | `CompleteArgs`; `affine_count` (the exact count of $n\mapsto G(rn+s)$ from a complete integer list, by an explicit bijection); `IntegralPointsOnImage`, the genus-one premise restricted to the image of the change of variables, and `cubic_sound_image`; `n3m2_hits`, the generic checker made unconditional for $n^3-2$. |
| `MordellFLT3.lean` (new) | **Unconditional nonempty** genus-one list. The identity $(36u^3+y)^3+(36u^3-y)^3=(6ux)^3$ on $y^2=x^3-432u^6$ and Mathlib's `fermatLastTheoremThree` give `points`: the integral points are exactly $(12u^2,\pm36u^3)$; `isHit_iff`: $n^3-432u^6$ is a square iff $n=12u^2$; `hitSet_432`: the hit set of $n^3-432$ is $\{12\}$. |
| `Genus1.lean`, `Generated/Genus1.lean` (new) | Checked Weierstrass reductions of $m^2=$ cubic and $m^3=$ quadratic, and checkers `cubicOK`/`quadOK` with soundness `cubic_sound`/`quad_sound`. Every listed point is re-verified on the model, every point pulls back to a recorded hit or to nothing, and every hit has a witness. There are 399 generated hit-list theorems, **each from the named hypothesis that Sage's point list is complete**. |
| `Binomial.lean` (new) | Reductions of $\binom n2=m^3$ and $\binom n3=m^2$ to the curves $Y^2=X^3+1$ and $Y^2=X^3-36X$. The point lists are checked by `decide`. Hit sets $\{1,2\}$ and $\{1,2,3,4,50\}$, **conditional on the named hypotheses** `IntegralPointsCubePlusOne` and `IntegralPointsCongruent6`, which state that the integral-point lists are complete; these are certified by Sage, not by Lean. |
| `Davenport.lean`, `ABC.lean` (new) | `davenport`, `davenport_sharp`, **`pillai_polynomial`**, **`pillai_polynomial_balanced`**, `pillai_polynomial_sq_sharp` (all unconditional; function-field Pillai from Mason–Stothers). `hall_of_abc`, `pillai_bound_of_abc`, `pillai_finite_of_abc`, all with abc as an explicit hypothesis. |
| `Generated/MordellPoints.lean` (generated) | Census data grouped by curve, `(k, [(x, y), …])`, checked block by block with `Reflect.mordellOK` (`decide +kernel`). `census_points_valid` states that every listed point lies on its curve, and `census_size` fixes 5641 curves and 8600 points. **Completeness is not checked.** |
| `RungeReduction.lean` (new) | `pow_diff_bound'`; **`runge_pointwise`** (if $P(n)\ne0$, $|D^dF(n)-P(n)^d|<(T+1)|P(n)|^{d-1}$, and, for odd $d$, $<|P(n)|^d$, then a hit gives $D^dF(n)=(P(n)+t)^d$ with $|t|\le T$); `runge_uniform`; **`runge_finite`**. This is Theorem R in integer form. The same file contains **`power_type_finite`**, Theorem P over $\mathbb Q[x]$: if $F=cG^d$ with $G\in\mathbb Q[x]\setminus0$ and $c$ not an integer $d$-th power, then the hits are finite. Only the derivation of the uniform inequalities from the coefficient constants $a(x_0),C(x_0)$ remains informal. |

## Machine-generated certificates

`python/perfectpower/lean_emit.py` turns a Runge plan into a Lean theorem of the form

```lean
theorem ljunggren_quartic_hits (n : ℕ) (hn : 1 ≤ n) :
    IsHit 2 (let z : ℤ := n; 1 + z + z^2 + z^3 + z^4) ↔ n ∈ ({3} : Finset ℕ)
```

The Python side only *chooses* the data: a threshold $x_0$, a $t$-range $T$, the signs of the $G_t$, and a witness for each $n<x_0$.

*Reflective form (current).* `Generated/Runge.lean` stores each certificate as a `Reflect.RungeCert` literal. `Reflect.rungeCheck` recomputes everything by kernel evaluation (`decide +kernel`):
- every Taylor shift and power, and the sign conditions $P>0$ and $(T+1)P^{d-1}\mp R'>0$ (and $P^d\mp R'>0$ for odd $d$);
- the definite sign of each $G_t$, $|t|\le T$;
- every value below $x_0$ (hit witness, strict bracket, or negative value).

`Reflect.rungeCheck_sound`, proved once from `runge_pointwise`, `tailPos_sound` and `ev_shift`, turns acceptance into the hit-set theorem, whose statement is unchanged. The file fell from 136 KB to 31 KB and checks in about 13 s.

The CLI (`python -m perfectpower lean --method runge`) still emits the older tactic proofs. There `norm_num`, `ring`, `positivity` and `runge_pointwise` re-check each instance, which is convenient for reading one certificate.

So a compiled generated theorem trusts nothing in the Python code. `PerfectPower/Generated/Runge.lean` contains 17 such theorems, and `Generated/Sandwich.lean` two more (below); the README count block is generated from these files. Regenerate them with `python3 python/make_lean_certificates.py`; `make verify` checks that the files are reproducible. The theorems cover:

- Ljunggren's quartic;
- $n^4+1$ and $n^4+7$ as squares;
- $n^6+n+1$ and $n^6+6n^5+5n^4+4n^3+3n^2+2n+1$ as cubes;
- products of $k$ consecutive integers that are never $d$-th powers, for these pairs:

  | $k$ | $d$ |
  |---|---|
  | 4 | 2, 4 |
  | 6 | 2, 3, 6 |
  | 8 | 2, 4, 8 |
  | 10 | 5 |
  | 12 | 2, 3, 6 |

**Interval-sandwich certificates** (`python/perfectpower/lean_sandwich.py` → `PerfectPower/Generated/Sandwich.lean`) cover the two instances that the plan search could not reach: $(10,2)$ and $(12,4)$.

*Reflective form.* Each certificate is now a data literal of type `Reflect.Cert`: the polynomial, its truncated root $P/D$, the segments and the tail. It is accepted by `Reflect.check` under `decide +kernel`, and `Reflect.check_sound` (proved once) turns acceptance into the hit-set theorem, whose statement is unchanged. The generated file fell from 768 KB (4889 lines, one `norm_num`/`gcongr` lemma per piece) to 12 KB (391 lines). The checker recomputes every Taylor shift and power itself, so nothing in the data is trusted.

*Sharper interval tests measured, not adopted.* Replacing $\mathrm{POS}(0)>\mathrm{NEG}(w)$ by a Bernstein-basis or Horner-interval lower bound changes the piece count from 283 to 279 for $(10,2)$ and from 49 to 38 for $(12,4)$. The count is dominated by single points at small $n$, where the sandwich offset $t$ changes from one $n$ to the next, not by the interval test. With the reflective format the piece count affects only the data size. The extra soundness proof is therefore not worth it.

For those instances the obstruction was the scan range below the Runge threshold, not the tail argument. Pointwise checks there would need about $2\cdot10^4$ cases. Instead, $[1,\infty)$ is covered by pieces:

- **Intervals** $[a,a+w]$ on which one integer $t$ satisfies $(P+t)^d<D^dF<(P+t+1)^d$ and $P+t>0$. Each of the three polynomials, shifted to $a+k$, is split as $\mathrm{POS}(k)-\mathrm{NEG}(k)$ with nonnegative coefficients. Monotonicity of polynomials with nonnegative coefficients gives $\mathrm{NEG}(k)\le\mathrm{NEG}(w)$ and $\mathrm{POS}(k)\ge\mathrm{POS}(0)$ (`ev_nonneg_mono`), and the checker tests $\mathrm{POS}(0)>\mathrm{NEG}(w)$.
- **A tail** $[c,\infty)$, where $\mathrm{NEG}$ is empty.
- **Isolated points**, decided numerically.

The lemma `no_hit_of_sandwich` then shows $F(n)$ is not a $d$-th power.

| Instance | Pieces below the tail | Tail start |
|---|---|---|
| $(10,2)$ | 283 | 20277 |
| $(12,4)$ | 49 | 478 |

The two files compile in about 4.5 minutes, and both theorems depend only on the standard axioms (no `Lean.ofReduceBool`). Statistics are in `receipts/sandwich_certificates.json`.

*On recentring.* Recentring the variable, e.g. $u=2n+9$ for $k=10$, improves only crude global coefficient bounds. The sandwich takes a Taylor shift at every interval start, which is already a local recentring. So a global substitution was not needed.

## What it does not certify

- **The nonrigid density-zero branch in general.** This is Boshernitzan's criterion, or alternatively Siegel's theorem through Theorem G. Both remain named external theorems. Individual nonrigid examples are proved directly (`pell_hasDensity_zero`, `monomial_count`, `twisted_density_zero`).
- **The atlas (Theorems B, C), the explicit Runge thresholds of Theorem R, the shift spectrum, and the transform theorems.** These are paper proofs. The Python implementations are checked against direct scans, but a Python test is not a Lean proof, and the Lean kernel does not certify the Python code.
- **The Python certificate verifier.** It shares its mathematics with `eventually_no_hit` but is a separate artifact.

## Interface notes

`IsHit` accepts every natural $d$. Public theorems assume $2\le d$ where it matters; `hasDensity_one_of_pow` does not need it. Hits are indexed from $n=1$. The shift $k$ is a parameter of `hitSet`/`A`, and the polynomial theorems use $k=0$ with the shift absorbed into $F$.

The next formal targets, in order, are:

1. The valuation characterisation behind Theorem B for general $c$ and $\alpha$ (the monomial case $c=1$, $\alpha=0$ is done in `Monomial.lean`).
2. Coefficient-bound lemmas giving the hypotheses of `runge_uniform` from $a(x_0)>0$ and $C(x_0)$. A Python certificate could then be replayed in Lean.
