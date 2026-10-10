# Current edition: PerfectPower 0.9.4

The historical core and its proof-status table follow. This complete edition also includes the merged generating-function chapter and the exact-binary/analytic-tail chapter at the end. Each chapter states its own scope; new Python replay certificates do not inherit the historical Lean labels.

# Perfect-Power Hits Beyond Density

## Exact definitions, a polynomial dichotomy, finite-hit certificates, and the arithmetic of the zero branch

## 0. Status of historical results (edition 0.8)

The 4 October extension replaces coordinate scanning for square-plus-constant polynomial equations with proved divisor enumeration and complete integer fibres. It also adds exact quotient-algebra proposal arithmetic and kernel-checked primitive quartic residue exclusions. See [the extension monograph](DIVISOR_REUSE_MONOGRAPH.md) and its separate verification record for scope and actual checks.

This table is the single source of truth. The research notes, the paper, the README and the trust boundary state the same claims. Labels: **Lean** means compiled and axiom-audited (only `propext`, `Classical.choice`, `Quot.sound`). **Lean ⇐ H** means compiled, with a named hypothesis that is not proved. **Paper** means a written proof. **External** means a computation by third-party software (Sage, Singular). **Evidence** means exact within a stated bound and silent beyond it.

| Result | Status | Depends on | Where |
|---|---|---|---|
| Density 0–1 law, rigid branch | Lean (`rigid_zero_one`, `rigid_dichotomy`) | — | `ZeroOne.lean`, `Rigid.lean` |
| Density 0–1 law, nonrigid branch | Paper | Boshernitzan (external theorem) | §3 below |
| Power type: all hits, or finitely many | Lean (`atlas_power`, `power_type_finite`) | — | `Atlas.lean`, `RungeReduction.lean` |
| Radical type $A(N)=\kappa N^{1/t}+O(1)$, $\kappa=(R/v)(v/z_0)^{1/t}$ | Lean for $c(vn-u)^rG(n)^d$ (`radical_asymptotic_int`, `atlas_radical`); general $F$ (rational bad degree 1): **Lean**. The pointwise reduction is `integer_radical_reduction`. The count is `Decomposition.radical_count`: $\lvert A(N)-\kappa N^{1/t}\rvert \le K$ with $\kappa\ge0$ and $2\le t\mid d$, keeping the exceptional zeros, both signs of the coefficient, negative shifts, and the unsolvable case ($\kappa=0$). The error is explicit: $K=2V+2(U+V\lvert U\rvert )+\lvert U\rvert +2+\deg F$ (`radical_count_explicit`). Positivity of $\kappa$ is decided in Lean (`radical_kappa_decide`): $\kappa>0$ iff there are infinitely many hits, iff some integer $n$ in an explicit finite range ($n\le \lvert C\rvert ^{t-1}V^t+U+V\lvert U\rvert $) is a hit of the reduced form with $Vn>U$ | valuation core (Lean); rational Yun decomposition (Lean) | `RadicalAsymp.lean`; notes §3 |
| Pell type $A(N)=\kappa\log N+O(1)$, $\kappa=(\sum_\rho g_\rho/P_\rho)/\log\varepsilon$ | Lean for $An^2+Bn+C$ with a given unit (`pell_exact_count`, `atlas_pell`); general $F$ of Pell type (Theorem C): **Lean**. The pointwise reduction is `integer_pell_reduction`. The count is `Decomposition.pell_count`: $\lvert A(N)-\kappa\log N\rvert \le K$ for large $N$, $\kappa\ge0$. It uses a squarefree quadratic (nonzero discriminant), the branches $\pm\gamma_0$ of $\gamma^e=\mathrm{lc}(F)$, cleared denominators, the bounded cases $A<0$ and $A=\square$, Mathlib's Pell unit for $A>0$ non-square, the overlap at roots of $Q$, and the zeros of $F$. Positivity is decided in Lean (`pell_kappa_decide`): $\kappa>0$ iff some root $\gamma$ of $\gamma^e=\mathrm{lc}(F)$ is positive and not a rational square, and $\gamma Q(n)$ is a rational square at one integer $n$ past the vertex. Per branch, a bounded search with explicit range is `branch_infinite_iff_bounded`. The error is explicit (`pell_branch_explicit`, `pell_count_explicit`): $K=\lvert B\rvert +1+(2Z+3)^2(2A)^2K_c+(2Z+3)^2\log(2A+\lvert B\rvert )/\log\varepsilon$, with $Z=\lvert \Delta\rvert (1+u^2)$, $W=(2Z+2)(1+2\sqrt A)$ and $K_c=3+(2\log(W+\lvert \Delta\rvert )+\log(2+\sqrt{\lvert \Delta\rvert })+\log2)/\log\varepsilon$ per branch, and $\sum K_{\mathrm{branch}}+\deg F+2$ for $F$ | canonical orbit roots (Lean) | `PellExact.lean`; notes §4 |
| Finite type: finitely many hits | Lean ⇐ `SuperellipticSiegel` (`atlas_finite`) | Siegel (external) + geometric half of Theorem G (Paper) | `Atlas.lean`; notes §5 |
| Theorem G, combinatorial half ($\chi=d'(1-S)$; $\chi<0$ ⇔ non-exceptional) | Lean, all $d$ (`chi_eq`, `chi_neg_iff`); Riemann–Hurwitz integrality table for $d,\deg F\le12$ (`profile_table_ok`) | — | `ProfileG.lean` |
| Theorem G, geometric half (Kummer, Riemann–Hurwitz) | Paper; External check (Singular genus, Sage places at infinity) over the range stated in `receipts/theorem_g_check.json` | — | notes §5 |
| Runge enumeration, rigid branch | Paper (Theorem R); 19 instances Lean via pp-cert/1 (`check_sound`, `rungeCheck_sound`) | — | `Reflect.lean`, `CERTIFICATE_FORMAT.md` |
| Genus one: 399 non-monic/shifted families, 2 binomials | Lean ⇐ named Sage point lists (`Genus1.lean`, `Binomial.lean`) | Sage `integral_points` (External) | `Generated/Genus1.lean` |
| Genus one, unconditional: 1163 Mordell curves $y^2=x^3+k$, $0<\lvert k\rvert \le10^4$, with **no** integral points | **Lean** (elementary descent `MordellDescent.lean`; no hypothesis) | agrees with the Sage census, 0 conflicts | `Generated/MordellDescent.lean` |
| Genus one, unconditional and **nonempty**: $y^2=x^3-432u^6$ has exactly the integral points $(12u^2,\pm36u^3)$ for every $u\ne0$; so $n^3-432u^6=m^2$ iff $n=12u^2$ | **Lean** (`MordellFLT3.lean`, from Mathlib's `fermatLastTheoremThree`) | classical (the Fermat cubic) | `MordellFLT3.isHit_iff` |
| Genus one, unconditional, **positive rank**: $y^2=x^3-2$ (points $(3,\pm5)$), $y^2=x^3-4$ (points $(2,\pm2),(5,\pm11)$) | **Lean** (`MordellMinus2.lean`, `MordellMinus4.lean`; descent in ℤ[√−2], ℤ[i]) | Mathlib (Euclidean ℤ[i]; ours for ℤ[√−2]) | §5A |
| Genus one, unconditional, positive rank, **class number 2**: $y^2=x^3-13$ (points $(17,\pm70)$); with $y^2=x^3-5$, $y^2=x^3-6$ (no points) as further instances | **Lean** (`ClassTwo.lean` template: Thue lattice bound + kernel norm table; `MordellMinus13/5/6.lean`) | — | §5A.3′ |
| Transport of complete lists through $n\mapsto rn+s$ with exact counts; image-restricted genus-one premise | **Lean** (`affine_count`, `cubic_sound_image`, `n3m2_hits`) | — | `Transport.lean`, §5A |
| Exact constraint reductions (affine, quadratic discriminant, triangular), their composition, and transported completeness | **Lean** (`Reduction.Exact`, `Exact.comp`, `Exact.pull_complete`, `triangular_count`, `tri_cube_complete`) | — | `Reduction.lean`, §5B |
| Filtered Pell orbits: a divisibility filter from a reduction's way back leaves infinitely many solutions iff some root cycle mod $M$ meets an admissible state; otherwise a complete finite range | **Lean** (`FilteredPell.infinite_iff_root_state`, `quadRoot_infinite_iff`, `FinCert.sound`, `quadRoot_bound_of_cert`) | unit orbits (Lean) | `FilteredPell.lean`, §5B |
| Filtered Pell count $A(N)=\frac1{\log\varepsilon}\big(\sum_\rho g_\rho/P_\rho\big)\log N+O(1)$ over canonical roots, and a certificate for the constant | **Lean** (`FilteredPell.filtered_count`, `count_of_orbit_estimates`, `count_of_cert`, `quadRoot_count_of_cert`) | exact Pell count (Lean) | `FilteredCount.lean`, §5B |
| Compiler plans as theorems on the original constraint: 25 catalogued plans with 37 theorems (2 disguised Mordell curves with nonempty complete answers from a discovered descent; 9 transport chains, 2 of them through branch-compiler lists; 5 infinite filtered plans with kernel-computed count constants, 4 with least solutions; 5 finite; a late family whose least solution $n=655680$ is proved; 2 Mordell-family members; one solution near $7.8\cdot10^{15}$) | **Lean** (`Generated/Plans.lean`, via `PlanCerts.power_transport`, `root_transport`, `quadRoot_subset_of_cert`, `FilteredPell.quadRoot_count_auto`, `quadRoot_isLeast`, `MordellFamily.no_points_cert`) | the rows above | `PlanCerts.lean`, §5B |
| Mordell's family $k=(4t-1)^3-4m^2$, $m$ free of primes $\equiv3\pmod4$: no integral point, for every member and every affine substitution | **Lean** (`MordellFamily.no_points`, `family_not_isHit`) | Mordell descent lemmas (Lean) | `MordellFamily.lean`, §5B |
| Descent certificates: under a kernel-checked table, `y^2 = x^3 - D` has exactly the points `(p^2 + D, p^3 - 3Dp)` with `3p^2 - D = ± 1`, and the list discharges `IntegralPointsOnImage` for every `m^2 = (rn + s)^3 - D` | **Lean** (`Descent.complete_of_cert`, `image_of_complete`, `hits_of_cert`) | `ClassTwo.short_relation` (Lean) | `Descent.lean`, `CONSTRAINT_COMPILER.md` §3F |
| Observations of filtered orbits: `#{v ≤ N} = (∑ g_ρ/(P_ρ log E_ρ)) log N + O(1)`; one orbit of `3 + √8` gives six sequences (Pell indices and roots, square triangular roots, values and odd values, triangular indices) with constants `1, 1, 1, 1, 1/2, 1/4` over `log(3 + 2√2)` | **Lean** (`Observation.observed_count`, `SquareTriangular.*_iff`, `*_count`) | exact Pell growth (Lean) | `Observation.lean`, `SquareTriangular.lean`, `OEIS.md` |
| Thirteen OEIS entries (definitions read from the official export, with offsets) are exact coordinates of `(1 + √2)^k`; both norm equations `x^2 - 2y^2 = ±1` are exhausted by two orbits; Pell numbers count at `log N / log(1 + √2)` as two observed orbits | **Lean** (`SqrtTwoOrbit.*_eq`, `*_enumerates`, `even_sol_iff`, `odd_sol_iff`, `pell_count`) | Pell roots (Lean) | `SqrtTwoOrbit.lean`, `OEIS.md` |
| Quadratic-unit orbit engine: for positive nonsquare `D`, a certified unit and seeds, `seedCheck` proves the seed orbits exhaust `x^2 - D y^2 = Δ` (seed completeness), with uniqueness, recurrences, periodic residues, geometric growth and collision bounds; the `φ` orbit of `Z[φ]` is six `Z[√5]` seed orbits, Fibonacci collisions are repaired by index parity, and Fibonacci / even Fibonacci numbers count at `log N / log φ` and a third of it | **Lean** (`QuadOrbit.complete`, `unique`, `orbit_mod`, `residues_periodic`, `cross_collision`, `FibOrbit.pos_iff`, `neg_iff`, `fib_collision`, `fib_parity_inj`, `fib_count`, `even_fib_count`) | exact Pell growth (Lean) | `QuadOrbit.lean`, `FibOrbit.lean`, `OEIS.md` |
| 69 OEIS definitions translated from their names by the definition language (recurrences, generating functions, coordinates, `D k^2 + c` sets) and proved equal to orbit coordinates or enumerated by certified seed orbits, generated and compiled; 10 more `√2` entries by hand (Pythagorean parametrization, a matrix orbit, coprime splitting, an exceptional set, a residue filter) | **Lean** (`Generated/OEISAuto.lean`, `OEISLib.setsq_enumerates`, `gf2_eq`, `gf3_eq`, `SqrtTwoBatch.*`) | the rows above | `OEISLib.lean`, `SqrtTwoBatch.lean`, `OEIS.md` §5–7 |
| Branch compiler: 26 of the 59 curves `y^2 = x^3 - D` (`1 ≤ D ≤ 100`) left unresolved before get complete Lean lists, including `y^2 = x^3 - 1`; every solution enters a finite branch of Thue's lattice argument and each branch is a field cube (reducible, listed by divisors) or impossible mod `m`; the other 33 reduce to explicit Thue equations | **Lean** (`DescentBranch.complete_of_branch`, `MordellMinus1.complete`, `Generated/MordellBranch.lean`); the 33: **External** (PARI `thue`, unconditional flag, agrees with Sage 33/33) | `ClassTwo.short_relation` (Lean) | `MORDELL_BRANCH.md` |
| The 316 open Thue branches compressed to 79 exact GL₂(ℤ) classes; 15 point-free classes proved impossible by p-adic descent on forms and transported to their branches, closing 10 more curves (36 of 59 in all) | **Lean** (`ThueLocal.descB_sound`, `empty_transport`, `DescentThue.complete_of_thue`, `Generated/MordellThue.lean`); classes and cubic fields: exact canonical forms / **External** (PARI) | the branch compiler (Lean) | `MORDELL_BRANCH.md` §5–6 |
| Continued fraction of `√2` (A001333), Euclid's primitive triples with conventions, exact monomial and filtered counts | **Lean** (`SqrtTwoBridges.*`, `MonomialCount.*`) | Pell orbit (Lean) | `OEIS.md`, `MonomialCount.lean` |
| Constraint compiler: plans, generated programs, timings | Python (tested against brute force, not verified); each plan cites its justification | the rows above | `CONSTRAINT_COMPILER.md`, §5B |
| Genus one: 622 monic cubics, Mordell census $0<\\lvert k\\rvert \le10^4$ | External (Sage; 485 census rows rest on an unproven rank) | — | `receipts/` |
| Genus ≥ 2 and quartic genus one outside Runge | Evidence (exact sieve to $10^8$) | — | `data/families.csv` |
| Abelian theorems: $A(x)\sim cx^\alpha(\log x)^\beta$ ($\alpha>0$, $\beta\ge0$) gives $K_X(t)\sim c\Gamma(\alpha+1)t^{-\alpha}(\log(1/t))^\beta$ and $\epsilon^{\beta+1}Z_X(\alpha+\epsilon)\to c\alpha\Gamma(\beta+1)$; finite support gives the exact hit count and a Dirichlet polynomial | **Lean** (`AbelianTransforms.heat_abelian`, `dirichlet_abelian`, `heat_finite`) | Mathlib's Gamma integral, dominated convergence | `AbelianTransforms.lean` |
| Log-periodic heat term (Theorem T2); $\beta<0$, $\alpha=0$ and the Tauberian converses | Paper; T2's $O(\tau)$ coefficient checked numerically | Mellin analysis (classical) | notes §8 |
| Exponential sequences (Theorem E) | Paper; periodic density Lean (`exp_hasDensity`) | — | notes §9 |
| Function-field Hall (Davenport) and Pillai | Lean (`davenport`, `pillai_polynomial`) | Mason–Stothers (Mathlib) | `Davenport.lean` |
| Hall, Pillai over $\mathbb Z$ | Lean ⇐ abc (`hall_of_abc`, `pillai_finite_of_abc`); the conjectures themselves are open | abc (hypothesis) | `ABC.lean` |

**Dependency arrows.**
- Siegel + Theorem G (geometric) ⟶ `SuperellipticSiegel` ⟶ finite type.
- Valuation core ⟶ radical count ⟶ `radical_asymptotic_int`.
- Canonical Pell roots + ε-growth ⟶ `pell_exact_count`.
- Rational Yun decomposition (`exists_integer_decomposition`, Lean) ⟶ pointwise Theorems B, C (`integer_radical_reduction`, `integer_pell_reduction`, Lean) ⟶ Theorem B count for general $F$ (`Decomposition.radical_count`, Lean); Theorem C count for general $F$ (`Decomposition.pell_count`, Lean). Positivity of $\kappa$ (`radical_kappa_decide`, `pell_kappa_decide`) and explicit error constants (`radical_count_explicit`, `pell_count_explicit`): Lean.
- Atlas = power ∪ radical ∪ Pell ∪ finite.
- Exact reductions (`Reduction.lean`) + a complete list or a structural count for the reduced power constraint ⟶ a complete answer or an exact generator for the original constraint (§5B). Completeness is transported by `Exact.pull_complete`, not re-proved.
- Boshernitzan ⟶ nonrigid density zero. This is independent of the atlas; the atlas gives a second, ineffective proof through Siegel.

**One command.** `make verify` builds the Lean library, audits axioms, lints, runs the Python tests, regenerates every receipt, certificate and generated Lean file, and fails on any difference from the committed files. Its output for the release commit is archived in `docs/RELEASE_CHECK.md`. The Sage and Singular steps (`make crosscheck`) are optional, and their receipts are re-checked in plain Python by `make verify`.

The text from §1 on is the 0.5 edition, kept for its definitions and the density argument. Where it and this table disagree, the table is current.

**Research edition, 28 September 2026.** This manuscript consolidates the preceding chat monograph with the attached Lean draft and the exact computational implementation in this repository. The analytic polynomial dichotomy is a paper proof relying on an established uniform-distribution theorem. The finite-hit cutoff is constructed and independently checked by exact Python arithmetic. In the 0.5 edition the Lean files had not been compiled; since 0.6 they compile, and the table in §0 lists what is machine-checked. No novelty claim attaches to Boshernitzan's, Siegel's, or Bombieri–Pila's results.

### 1. The object of study

For an integer sequence S on the positive integers, an integer k, and d≥2, put X(n)=1 if there is m∈ℤ such that S(n)+k=m^d, and X(n)=0 otherwise. Write A(N)=Σ_{1≤n≤N}X(n), ρ(N)=A(N)/N, H=limsup ρ(N). We exclude d=0, which tests only S(n)+k=1, and d=1, for which every integer qualifies. Negative values are hits for odd d precisely when their absolute values are d-th powers, and never for even d. This definition is the only authority for computed hits. Precomputed Boolean fixtures test a count aggregator, not the definition. Exact integer roots are required; round-tripping large integers through floating point invalidates an arithmetic receipt.

H is an upper asymptotic frequency, not the maximum of a set of finite prefixes. A numerical maximum taken beginning at a fixed sample N₁ can remain controlled by N₁ even when the true H is zero. The dyadic statistic B_j=max{ρ(n):2^j≤n<2^(j+1)} has the exact mathematical property H=limsup_j B_j, but any finite list of windows remains observational evidence rather than a proof of the limit. Every computational receipt must identify its polynomial coefficients (low to high), d, k, index range, exact count, software revision, and process exit code.

### 2. The convergence bridge and finite surgery

Define HasDensity(S,d,k,L) by ρ(N)→L as N→∞. The foundational lemma is HasDensity⇒H=L. If the hit set is finite, A(N)≤B for some B, so 0≤ρ(N)≤B/N→0. If X has period T≥1 and P hits in one period, writing N=qT+r gives A(N)=qP+R_r, 0≤R_r≤T; dividing by qT+r yields ρ(N)→P/T. Consequently periodic rationality is an elementary count theorem. The periodic hypothesis should concern X directly; when the theorem mentions a source sequence S, that source matters only through X.

If S and S' agree for n≥N₀, their hit indicators agree there. For every N≥N₀−1, A_S(N)−A_S'(N)=D:=A_S(N₀−1)−A_S'(N₀−1). Thus ρ_S(N)−ρ_S'(N)=D/N. Both upper densities are equal because the difference of their bounded density sequences tends to zero. An epsilon proof of general limsup invariance uses eventual inequalities u≤v+ε and v≤u+ε, and then lets ε→0. The attached Lean draft correctly binds two sequences, but has not been compiled. A command that constructs S' by replacing only finitely many prefix values makes agreement beyond N₀ true by construction. A generic finite scan cannot prove two arbitrary functions agree forever.

### 3. The polynomial 0–1 theorem

**Theorem (density dichotomy).** Let F=S+k∈ℤ[x] and d≥2. The ordinary density of positive indices n for which F(n) is an integer d-th power exists. It equals one if F=G^d for G∈ℤ[x], and zero otherwise. In particular H∈{0,1}. The constant case is immediate. If d is even and F is eventually negative, the count eventually stops. In the remaining cases choose the real d-th-root branch f(x) of F(x) for sufficiently large x, using the signed root for odd d.

Suppose first that deg(F)/d is not an integer. The asymptotic expansion of f begins with c x^λ for a positive noninteger λ. For every p∈ℚ[x], f(x)−p(x) has an unmatched positive-power leading term, so |f(x)−p(x)|/log x→∞. Suppose instead that deg(F)=qd but the integer leading coefficient a of F is not an integer d-th power (on the relevant real branch). Then f begins with the irrational coefficient a^(1/d)x^q; again every rational polynomial differs by a positive-power term, and the same logarithmic separation follows. Algebraic root functions on an eventual interval belong to a Hardy field and have polynomial growth. Boshernitzan's criterion implies that f(n) is uniformly distributed modulo 1 in both cases. A hit requires its fractional part to be exactly zero. For every ε>0, the hit set is contained in an interval around zero of length at most 2ε modulo one; uniform distribution makes its upper density at most 2ε. Let ε→0. This derives zero density, without asserting that there are infinitely many hits or giving a power-saving count.

It remains to consider deg(F)=qd and leading coefficient b^d for b∈ℤ. Matching the leading q+1 coefficients of F recursively constructs Q∈ℚ[x] of degree q and leading coefficient b such that R=F−Q^d has deg(R)<(d−1)q (with the zero polynomial permitted). Analytically f(x)=Q(x)+O(x^−1), and if R≠0 the first nonzero term in f−Q has negative degree. Clearing denominators gives DQ∈ℤ[x] for some positive D. Every Q(n) lies in (1/D)ℤ; its distance to an unequal integer is at least 1/D. The root f(n) approaches Q(n) without equalling it when R(n)≠0, so f(n) eventually cannot be an integer. Thus the hit set is finite. If R=0, Q^d=F∈ℤ[x]. Since ℤ[x] is integrally closed inside ℚ[x], Q∈ℤ[x]; every n is a hit. The theorem follows.

**Stronger rigid-branch conclusion.** In the degree-divisible, perfect-leading-coefficient branch, either F is an exact polynomial d-th power or there are only finitely many hits. Uniform distribution is needed only outside this branch. For an odd exponent a negative leading coefficient can be an odd d-th power and supplies a signed Q; for an even exponent an eventually negative polynomial supplies no hits. The degree-zero F=0 case is the exact power 0^d.

This is a deduction from Boshernitzan's published uniform-distribution criterion, not a new theorem attributed to this repository. The cited paper's precise criterion asks for logarithmic separation from every rational polynomial, a stronger and more useful statement than a vague appeal to fractional-part equidistribution.

### 4. An explicit certificate for the rigid branch

The implementation stores coefficients in increasing degree. It computes b as an exact signed integer root of the leading coefficient; if d∤deg(F) or no b exists, it reports `nonrigid`, which is *not* a finite-hit certificate. Otherwise write M=dq and recursively choose Q(x)=b x^q+c_(q−1)x^(q−1)+⋯+c₀. At stage j, match the coefficient of x^(M−j) in F−Q^d: its dependence on the as-yet-unset c_(q−j) is d b^(d−1)c_(q−j), so exact rational division determines it. After q stages, R=F−Q^d has degree r<(d−1)q, unless R=0. The certificate carries integer coefficients of F, numerator coefficients of Q with a common denominator D, numerator coefficients of R with denominator D^d, and a cutoff B. The independent verifier recomputes every polynomial identity from those integers.

For the nonzero remainder, put L=Σ_{i<q}|c_i|, C=Σ_i|R_i|, and L_R=Σ_{i<r}|R_i|; let a=|b|/2. The certificate enforces B≥max(1,ceil(2L/|b|),ceil(2L_R/|R_r|)). For every n≥B, triangle inequalities give |Q(n)|≥a n^q, |R(n)|≤C n^r, and |R(n)|≥|R_r|n^r/2>0. The last inequality is the crucial nonvanishing check. It also checks at B the two exact rational inequalities C B^r≤a^d B^(dq)/2 and C B^r<a^(d−1)B^((d−1)q)/(2D). Because the exponents on the right exceed r, both remain true for every n≥B. If F(n)=m^d, the first inequality forces an appropriate integer root y, equal to m or −m for even d, to have the sign of Q(n). Write y=tQ(n) with t≥0. The elementary inequality |t−1|≤|t^d−1| gives |y−Q(n)|≤|R(n)|/|Q(n)|^(d−1)<1/(2D). Nonvanishing says y≠Q(n), while denominator clearing says every distinct integer y is at distance at least 1/D from Q(n). This contradiction proves **there are no hits at n≥B**. The verifier recomputes Q, R, their degrees, and all four rational inequalities from the serialized integers. It is intentionally independent of the constructor's search for B, though it shares the mathematical argument. A potentially large cutoff is an honest bound, not a promise that enumerating all indices below it will be cheap. The report must not claim an exhaustive hit list until that finite prefix has actually been checked.

### 5. What zero density contains

For F(n)=n³+an+b+k and d=2, each hit is an integral point on m²=n³+an+(b+k). If 4a³+27(b+k)²≠0, the cubic is nonsingular. Siegel's theorem makes its integral-point set finite, so A(N) is bounded and H=α=0. The shift k changes the elliptic curve, and BSD concerns rational points and L-functions rather than the density of these integral points. Siegel's theorem as used here is a finiteness theorem, not an automatic algorithmic enumeration of every point.

For F(n)=n³, a square hit occurs exactly when n is a square, so A(N)=⌊√N⌋. For F(n)=4n+1, integer roots are odd and the same square-root order follows; at N=10³,10⁴,10⁵ the counts are 31,99,315. For F(n)=2n²+1, Pell solutions of m²−2n²=1 yield infinitely many hits with A(N) of logarithmic order; the root function has an irrational leading coefficient, so its values are nevertheless uniformly distributed modulo one. This example separates finiteness from the growth exponent zero. The exact monomial family F(n)=n^r, g=gcd(r,d), has A(N)=⌊N^(g/d)⌋: prime valuations force n to be a (d/g)-th power. The arithmetic zero branch spans finite counts, logarithmic counts, and various powers below N.

Define α=limsup_N log(1+A(N))/log N. The regularization makes α=0 for empty and finite hit sets. The above cases have α=1/2, 1/2, 0, and 1 for a polynomial d-th power; Pell gives α=0 despite infinitely many hits. For F(n)=a n+c with a>0, the congruence m^d≡c mod a determines whether any sufficiently large hits exist. If it has R positive residue classes modulo a, A(N)∼R a^(1/d−1)N^(1/d); if it has none, A(N)=0. The exact count and leading constant should be preferred over an exponent whenever available.

An enriched profile can retain (H, α, finite/infinite support, a logarithmic correction when meaningful, and local congruence data). Finiteness may be known nonconstructively; distinguish that proof status from an enumerated finite set. Brocard-type factorial questions lie outside the polynomial theorem. A computation of finitely many factorial values cannot establish their density or the finiteness of their hit set. Conversely, periodic fixtures can have rational H strictly between zero and one, but such fixtures are not examples contradicting the polynomial theorem.

### 5A. Genus one without an external point list (edition 0.8)

Sections 4–5 establish that a nonsingular cubic $F$ has finitely many square hits, but finiteness is not a list. Until edition 0.7 every complete genus-one list in this repository rested on Sage's `integral_points`, an elliptic-logarithm computation that Lean never checks. This section describes the four ways the Lean library now closes such a list with no external hypothesis. It also describes the bridge that carries a closed list to an exact hit count.

**1. Arithmetic obstruction: curves with no integral points** (`MordellDescent.lean`). Let $k=c^3-Db^2$ with $D\in\lbrace 1,2,-2\rbrace$. An integral point of $y^2=x^3+k$ gives
$$y^2+Db^2=(x+c)\,q,\qquad q=x^2-cx+c^2=\tfrac14\big((2x-c)^2+3c^2\big)\ge0.$$
Let $G_D$ be the residues mod 8 of the odd primes $p$ for which $-D$ is a square mod $p$: $\lbrace 1,5\rbrace$, $\lbrace 1,3\rbrace$ and $\lbrace 1,7\rbrace$ respectively (Mathlib's supplementary laws). $G_D$ is closed under multiplication, so an odd $q$ with $q\bmod 8\notin G_D$ has a prime factor $p$ with $p\bmod 8\notin G_D$ (`exists_bad_prime`). The kernel evaluates every residue pair mod $M\in\lbrace 8,16,32\rbrace$ and checks that the equation forces exactly this (`CongOK`). Such a $p$ divides $y^2+Db^2$, and $-D$ is not a square mod $p$, so $p\mid b$ (`good_of_dvd`). This is excluded by a certificate $b=2^jb_1$ with $b_1\mid u^2+D$ (`goodDivisors_of_cert`). The obstruction is arithmetic, not local: the curves have points modulo every integer. For $0<|k|\le10^4$ the search finds 1163 such $k$, 28 of them census rows whose Sage rank was unproved. For $D=3$ the mod-8 mechanism cannot work. $-3$ is a square modulo $p$ exactly when $p\equiv1\pmod3$, while $q\equiv(x+c)^2\pmod 3$ lies in $\lbrace 0,1\rbrace$, so no congruence on $q$ can force a prime factor $\equiv2\pmod3$. (Such a prime may still divide $q$ when it divides $\gcd(x,c)$.) $D=-3$ is different and unexamined. The needed primes are $p\equiv\pm5\pmod{12}$, where $3$ is a non-residue, and a mod-12 version of the argument has not been attempted. An earlier edition wrongly stated that both signs fail.

**2. Reduction to a formalised theorem: a nonempty infinite family** (`MordellFLT3.lean`). On $y^2=x^3-432u^6$,
$$(36u^3+y)^3+(36u^3-y)^3=(6ux)^3,$$
so Mathlib's `fermatLastTheoremThree` forces a vanishing cube. This gives exactly the points $(12u^2,\pm36u^3)$.

**3. Positive rank: descent in a Euclidean quadratic ring** (`MordellMinus2.lean`, `MordellMinus4.lean`). $y^2=x^3-2$ and $y^2=x^3-4$ have rank one. There are infinitely many rational points, so no finite-group or congruence argument can close the list.
- *For $x^3-2$:* ℤ[√−2] is made Euclidean by integer rounding, and the remainder norm is at most $\tfrac34$ of the divisor's. By a congruence mod 4, $y$ is odd. The explicit Bézout identity $(-B-c\sqrt{-2})A+c\sqrt{-2}\,B=1$ with $A,B=y\pm\sqrt{-2}$ and $c=k^2+k+1$ proves coprimality. Mathlib's `exists_associated_pow_of_mul_eq_pow'` extracts a cube root, and the only units are $\pm1$. The $\sqrt{-2}$-coefficient gives $b(3a^2-2b^2)=1$, hence $(x,y)=(3,\pm5)$.
- *For $x^3-4$ in ℤ[i]:* every unit is a cube. When $y$ is odd, the argument gives $(5,\pm11)$. When $y$ is even, it passes through $y_1^2+1=2x_1^3$ and the factor $1+i$ to the Thue equation $(a-b)(a^2+4ab+b^2)=1$, giving $(2,\pm2)$.

These reprove in Lean 4 results that Baanen–Best–Coppola–Dahmen formalised in Lean 3 through class groups. For these two curves the route is elementary, because the rings are Euclidean.

**3′. Class number two, without ideals: a template** (`ClassTwo.lean`; instances `MordellMinus13.lean`, `MordellMinus5.lean`, `MordellMinus6.lean`). When ℤ[√−D] has class number 2, unique factorisation fails. The classical proof shows that the ideal $I$ with $I^3=(y+\sqrt{-D})$ is principal, because $3\nmid h$. `ClassTwo` makes each ingredient explicit *for every $D>0$*, in integer arithmetic. Write $\alpha=y+\sqrt{-D}$ and $x^3=y^2+D$.
- *The ideal $I$* is the lattice $\lbrace (a,b): x\mid a-yb\rbrace$ of index $x$.
- *Minkowski's bound* is Thue's pigeonhole lemma (`exists_short`, `box`, `short_relation`). Compare the pairs in $[0,A]\times[0,B]$ modulo $x$, with $A=\lfloor\sqrt{rx/t}\rfloor$ and $B=\lfloor\sqrt{tx/r}\rfloor$ for a rational box ratio $r/t\approx\sqrt D$. There are more than $x$ pairs, so two collide, and their difference is $v=(a,b)\ne0$ in the lattice. It satisfies $a^2+Db^2=kx$ with $1\le k\le K$ whenever $r^2+Dt^2<(K+1)rt$. No small-$x$ case remains.
- *$I^3=(\alpha)$* is the congruence $\psi(z^3)\equiv\psi(z)^3\pmod{y^2+D}$ for $\psi(z)=z_{\mathrm{re}}+y\,z_{\mathrm{im}}$. Since $x\mid\psi(\bar v)$, $x^3$ divides both coordinates of $\alpha\bar v^3$, so $\alpha\bar v^3=x^3\beta$ with $N(\beta)=k^3$ and $k^3\alpha=\beta v^3$.
- *"The class group has order 2"* is the only instance-specific input: a finite table `TableOK D K P Q`, decided by the kernel. For $k\le K$, $p^2+Dq^2=k^3$ forces $q=0$ and $(k,p)=(1,\pm1)$ or $(4,\pm8)$. The companion `HalvesOK D` is a residue check mod 8 that halves $v$ when $k=4$. Given both, `cube_of_table` concludes $\alpha=(p+q\sqrt{-D})^3$.

| $D$ | box $r/t$ | $K$ | cube-root step $q(3p^2-Dq^2)=1$ | integral points |
|---|---|---|---|---|
| 13 | 11/3 | 7 | $q=-1$, $p=\pm2$ | $(17,\pm70)$ |
| 5 | 3/2 | 4 | none | none |
| 6 | 5/2 | 4 | none | none |

For $D=5,6$ the table rules out the norms $8$ and $27$, which is exactly where the non-principal class would enter. The curves $y^2=x^3-5$ and $y^2=x^3-6$ have rank 0, and the elementary descent of item 1 also shows they have no points. The template gives a second, class-group proof.

This is the class-group argument of Baanen–Best–Coppola–Dahmen, reorganised so that no ideal or class group appears. It is *not* a line-by-line port of their Lean 3 code, which this environment could not fetch. A new $D$ needs only a box ratio and $K$ with $r^2+Dt^2<(K+1)rt$, the kernel's table and halving checks, and the Thue step. The table fails, as it should, when a norm $k^3$ with $k\le K$ is represented non-trivially. That happens when the class group has elements of order 3, or when the pigeonhole bound is too weak for $D$ to be reached with $K<8$.

**4. Transport with integrality** (`Transport.lean`). Suppose a complete list is $\mathrm{CompleteArgs}(G,d,T)$: $G(t)$ is a $d$-th power iff $t\in T$, for every *integer* $t$. For $r\ne0$, the family $n\mapsto G(rn+s)$ then has hits exactly at $rn+s\in T$. By `affine_count`, the count is
$$A(N)=\lvert\lbrace t\in T:\ r\mid t-s,\ 1\le (t-s)/r\le N\rbrace\rvert,$$
from the same hypothesis. For example, $(rn+s)^3-2$ is a square iff $rn+s=3$, so $A(N)\in\lbrace 0,1\rbrace$ is decided by $r\mid 3-s$ and $1\le(3-s)/r\le N$ (`affine_cube_sub_two`).

The Weierstrass normalisation of `Genus1.lean` needs the same care. The old premise `IntegralPointsOn` asks for *every* integral point of the scaled model. A theorem about $m^2=F(n)$ only classifies the points in the image of $(n,m)\mapsto(9an+3b,\,27am)$. `IntegralPointsOnImage` asks only for those points (those with $9a\mid U-3b$ and $27a\mid V$), and `cubic_sound_image` proves the hit list from it. For $n^3-2$ the model is $V^2=U^3-1458$: `n3m2_image` discharges the image premise from `MordellMinus2.points`, and `n3m2_hits` recovers the unconditional list $\lbrace 3\rbrace$ through the generic checker, without classifying the model's other integral points. The same distinction will be essential for quartic models, where the change of variables introduces denominators.

### 5B. From structure to execution (edition 0.9)

The atlas says, before any search, which of four shapes a hit set has. This section turns that into
programs. The guide with all details is `docs/CONSTRAINT_COMPILER.md`.

**1. Architecture.** A constraint on a positive integer $n$ goes through three stages:
1. an **exact reduction** to a power constraint $G(n)=m^d$;
2. a **structural solver** for $G$, chosen from the classification;
3. the **backward maps**, which recover the original witnesses and discard inadmissible ones.

The result is a *plan* with exactly one outcome:
- `COMPLETE_FINITE`: a complete finite list;
- `STRUCTURED_INFINITE`: infinitely many, generated exactly;
- `STRUCTURED_FILTERED`: an exact generator followed by a nontrivial exact filter;
- `CLASSIFIED_FINITE`: finite, exact to any $N$, no complete list;
- `NOT_ENUMERATED`: finite, no enumeration; only labelled bounded evidence.

Each plan carries the Lean theorems, certificates or Python algorithms that justify it, and states
that its own execution is not verified. The specializer writes the plan out as a standalone program,
replacing a brute-force loop.

**2. The reductions are theorems** (`Reduction.lean`). An exact reduction $P\rightsquigarrow Q$ is
a map $\mathrm{fwd}$ of solutions and a partial inverse $\mathrm{bwd}:\ Q\text{-solutions}\to P
\cup\lbrace\bot\rbrace$ with $\mathrm{bwd}(\mathrm{fwd}\,a)=a$. The general theorems are:
- `Exact.iff`: $P(a)\iff\exists b,\ Q(b)\wedge\mathrm{bwd}(b)=a$.
- `Exact.comp`: reductions compose, and their admissibility conditions compose.
- `Exact.pull_complete`: a complete finite list for $Q$ pulls back to a complete finite list for
  $P$. This is the unifying principle of the release: *a complete theorem about one equation
  becomes a complete answer about another through a checked chain of reductions, and every
  integrality condition along the chain is part of the chain.*

The instances are:
- **affine**: $t=rn+s$, back when $r\mid t-s$ and $(t-s)/r\ge1$;
- **quadratic**: $m=2ay+b$, $m^2=4aF(n)+b^2-4ac$, back when $2a\mid m-b$ for $m$ or $-m$ and
  $y$ lies in its domain;
- **triangular**: $m=2y+1$, $m^2=8F(n)+1$. Here $m$ is odd, so the way back never fails for
  $y\in\mathbb Z$ or $y\ge0$. Hence `triangular_count`: $\lvert\lbrace n\le N: F(n)\text{ triangular}\rbrace\rvert=A_{8F}(2,1,N)$.

A square discriminant is not enough in general: $2y^2+y=1$ has discriminant $9$ but no root
$y\ge0$.

**3. Worked example, fully in Lean** (`tri_cube_complete`). With $n\ge1$ and $y\in\mathbb Z$,
$$\frac{y(y+1)}2=64n^3-120n^2+75n-16\iff (n,y)\in\lbrace (1,2),(1,-3)\rbrace.$$
The chain is: triangular, giving $m^2=(8n-5)^3-2$; then affine, $t=8n-5$; then `MordellMinus2.points`.
The pull-back of $\lbrace (3,\pm5)\rbrace$ is computed by `decide`. The compiler finds the same plan
automatically and emits the test `8*n + (-5) == 3`.

**4. Worked examples, executed** (`receipts/constraint_demos.json`, regenerated by `make verify`).
- $(5n-7)^3-2=m^2$ becomes `5*n + (-7) == 3`.
- $2n^2+1=m^2$ becomes the orbit $(X,m)\mapsto(3X+8m,\,X+3m)$ with $X=4n$, that is
  $n'=3n+2m$, $m'=4n+3m$ from $(n,m)=(0,1)$.
- $y(y+1)/2=n^2$ becomes a Pell orbit on $8n^2+1$ with $y=(m-1)/2$.
- $2y^2+y=n$ with $y\ge0$ becomes the radical family $8n+1=w^2$ filtered by $4\mid w-1$.
- $991n^2+1=m^2$ has its first hit at $n=12055735790331359447442538767$. No scan reaches it, and
  the plan finds it in microseconds.
- $n^3+17=m^2$ is `NOT_ENUMERATED`. Siegel makes it finite, nothing here enumerates it, and its
  bounded evidence ($n=2,4,8,43,52,5234$ up to $10^4$) is labelled as evidence.

**5. Measurements** (`make bench`). Against the plain loop, structural plans win from
$N\approx10^3$ to $10^4$ in every specialized demo. Preprocessing costs 0.1–2 ms. A Pell or
finite plan then costs time proportional to its number of hits, while the loop is linear in $N$.
The crossover is real, not assumed: the square-triangular loop wins below $10^4$. Dense radical
families are output-bound, about 707,000 solutions at $N=10^{12}$. The receipt records the machine.

**6. Review correction.** Release `ddbdcb8` listed bounded Pell branches by scanning only
to $n\le10^6$. A `COMPLETE_FINITE` list could then miss a hit that `contains` recognized, for
example $((n-1000007)^2-2)^2=m^4$ at $n=1000008$. The limit is now the proved bound
(`hit_le_of_neg`, `hit_le_of_square`). Regression tests shift families past $10^6$ and fail on the
old code.

**7. The finite symmetry system behind a filter** (`FilteredPell.lean`). The way back of a
reduction is a filter on the reduced solutions, and for Pell families the filter is *stable*: past
a threshold it depends only on $(X,Y)\bmod M$. The unit permutes $(\mathbb Z/M)^2$, so each root
orbit is a cycle.

**Theorem (filtered Pell orbits).** Let $m^2=An^2+Bn+C$ with $A>0$ not a square, let
$\varepsilon=u+v\sqrt{4A}$ be a unit, and let the filter be stable modulo $M$ beyond $T$.
- The filtered family is infinite iff some root's cycle meets an admissible state within one
  period.
- Otherwise every solution satisfies $(2An+B)^2<\Delta+4AT^2$.

For $ay^2+by+c=F(n)$ with $M=|4Aa|$, the filter is $2A\mid X-B$ together with
$2a\mid sY-b$, where the admissible sign is $s=\mathrm{sign}a$ once the domain $y\ge L$
becomes a sign condition. The original solution set equals the filtered family past the vertex
(`quadHits_iff`).

Both outcomes have kernel-checked certificates: an admissible witness, or a `FinCert` giving the
roots in the box $4AY^2\le|\Delta|u^2$ and their cycle lengths. Counting orbit indices $(X,Y\ge0)$
counts each $n$ once, so $\kappa$ is the marked fraction of the cycles over $\log\varepsilon$. On
271 random plans this agrees with the count to within $2.03$ at $N=10^{40}$.

**7′. The filtered count.** With one root $\rho$ per orbit, a period $P_\rho$ of its residue
cycle and $g_\rho$ admissible states per period,
$$A(N)=\frac{1}{\log\varepsilon}\Big(\sum_\rho\frac{g_\rho}{P_\rho}\Big)\log N+O(1)$$
(`filtered_count`; for the original constraint, `quadRoot_count_of_cert`). The proof generalises
the exact Pell count: `orbit_count_pred` counts one orbit for any periodic predicate, the
assembly `count_of_orbit_estimates` works for any filter forcing $2A\mid X-B$, and the finitely
many indices with $Y<T$ go into the error. A `CountCert` names the constant exactly: it lists
the roots (each checked to be a root, complete through the root box) with their $(P,g)$, so a
generated theorem states $\kappa$ as an explicit rational over $\log\varepsilon$.

**8. The chosen path as a theorem** (`PlanCerts.lean`, `Generated/Plans.lean`). For catalogued
plans the compiler's path is emitted as a Lean term: an `Exact` chain composed by `Exact.comp` and
closed by `pull_complete`, or a filtered-orbit certificate. The kernel then checks the plan's
statement about the original constraint, and the plan cites that theorem.
Certificates are computed by the kernel rather than written out (`FilteredAuto.buildCert`,
checked by the proved `CountCert.check`), and `quadRoot_isLeast` certifies the first solution
from the orbit order. For example, $41y^2+y+3=n^2+3$ has least solution $n=655680$, with count
$\tfrac12\log N/\log\varepsilon+O(1)$.

**8A. Recurrence to geometry.** A genus-one plan returns one of three kinds of answer:
- a complete list with a proof;
- an infinite family with a counting law;
- the exact missing premise (`Transport.IntegralPointsOnImage` on the Weierstrass model, with
  its substitution).

The first family case is Mordell's $k=(4t-1)^3-4m^2$ (`MordellFamily.lean`): one theorem gives
the empty answer for every member, so the emitted answer is the solution set. Its limits:
- the family's answer is always empty;
- recognition is a bounded search;
- positive-rank families with points remain open.

**8B. A nonempty complete answer, discovered and proved** (`Descent.lean`, `descent.py`). For
$y^2=x^3-D$ the compiler finds a descent certificate in $\mathbb Z[\sqrt{-D}]$:
- a Thue box;
- a table of the norms $k^3$ with $k\le K$, where a class of order 3 would show;
- residue checks that $j^3\mid v^3$ forces $j\mid v$.

Lean turns the certificate into the complete point list $(p^2+D,\,p^3-3Dp)$, $3p^2-D=\pm1$
(`complete_of_cert`), and then into the compiler's premise `IntegralPointsOnImage`
(`image_of_complete`, `hits_of_cert`). For example, $8n^3+12n^2+6n-73$ is a square only at
$n=49$. The class number $h(-296)=10$ is prime to 3, and the table is where this is certified.
`make descent-gate` gives an unseen disguised cubic to the compiler and has Lean check the file
it emits. Its limits:
- $3\mid h$;
- positive $k$;
- other genus-one cubics;
- kernel cost ($j\le5$).

**9. Two symmetries** (`galois.py`, `factor.py`). *The root action.* Each squarefree layer is
factored over $\mathbb Q$ (Berlekamp–Zassenhaus), so each irreducible factor is a genuine Galois
orbit. Groups are named up to degree 4: $C_2$ with its root field, $A_3$/$S_3$, and
$S_4$/$A_4$/$D_4$/$C_4$/$V_4$ via the resolvent cubic. The atlas profile is a union of orbit
profiles:
- radical type: its one obstructed root is fixed, hence a rational parameter;
- Pell type: its two obstructed roots are one conjugate pair or two rational roots.

*The unit action.* The integer solutions of a Pell branch move under the units of the **real**
field $\mathbb Q(\sqrt A)$ of its norm form, not under the root Galois group. For $2n^2+1$ the
roots lie in $\mathbb Q(\sqrt{-2})$ and the unit $3+\sqrt8$ lies in $\mathbb Q(\sqrt2)$. The two
fields are reported separately; an earlier explanation conflated them. The root action explains
the shape, and the unit action with its finite quotient decides the solutions and their count.
Neither settles point lists in higher genus.

**10. The remaining effectiveness boundary.** Classification becomes a complete executable answer
exactly where the mathematics is effective:
- Runge rigidity;
- solved Mordell curves (the registry of §5A and `Generated/MordellDescent.lean`);
- Pell orbits and radical parametrizations.

Two gaps remain:
- The finite type outside these cases is `NOT_ENUMERATED`. Siegel's theorem gives no bound, and
  Baker-type bounds are not implemented.
- Filters on Pell quadratics are now decided (item 7). Filters on higher-degree reduced forms
  remain `STRUCTURED_FILTERED`, and only catalogued plans are emitted as Lean theorems.

### 6. Dirichlet and heat transforms

For the same nonnegative indicator, Z_X(s)=Σ_{n≥1}X(n)n^(−s) and K_X(t)=Σ_{n≥1}X(n)e^(−tn). Summation by parts ties both to A(N). If the hit set is infinite, the abscissa of convergence of Z_X equals α. For finite support, Z_X is a Dirichlet polynomial with abscissa −∞, whereas the regularized α is zero. For all hit sets, limsup_(t↓0) log(1+K_X(t))/log(1/t)=α. The logarithm can hide slowly varying factors, so a Mellin or heat-kernel analysis should follow the count asymptotics rather than replace them.

**Proved in Lean** (`AbelianTransforms.lean`), for any hit set with `A(x) = #{1 ≤ n ≤ x}`:
- `heat_eq_integral`: K_X(t) = ∫₀^∞ e^(−u) A₋(u/t) du (Tonelli, with A₋ the strict count);
- `heat_abelian`: if A(x) ~ c x^α (log x)^β with α > 0, β ≥ 0, then K_X(t) ~ c Γ(α+1) t^(−α) (log(1/t))^β as t ↓ 0;
- `dirichlet_summable`: the same hypothesis already gives convergence of Z_X(s) for every s > α;
- `dirichlet_eq_integral`, `dirichlet_abelian`: under the same hypothesis, ε^(β+1) Z_X(α+ε) → c α Γ(β+1) as ε ↓ 0;
- `heat_finite`: for finite support, K_X(t) tends to the exact number of hits and Z_X is the finite Dirichlet polynomial.

These are normalized limits. They read as asymptotic equivalences (`~`) only when c > 0; for c = 0 they
state that the transform is o(t^(−α)(log 1/t)^β), respectively o(ε^(−(β+1))).

Each proof is dominated convergence after a change of variables. A Potter-type bound
A(x) ≤ C x^α (log(e+x))^β supplies the domination. Still open in Lean: β < 0 (the domination needs
a separate small-u estimate), the slowly growing case α = 0, and every Tauberian converse. A
converse needs a nondecreasing count, regular variation and a stated Tauberian condition. A
real-axis asymptotic alone does not recover the count.

When ordinary density h exists, t K_X(t)→h. In general limsup_(t↓0)t K_X(t)≤H. Likewise (s−1)Z_X(s)→h along real s↓1 when density exists; this is an Abelian real-axis limit and does not assert meromorphic continuation. A T-periodic indicator admits the stronger residue-class expansion Z_X(s)=T^(−s)Σ_(r=1)^T X(r) ζ(s,r/T), and its meromorphic residue at s=1 equals P/T. The finite-window maximum sometimes called a tropical limit supplies none of these density claims. Cofinite-tail invariance is a basic property of limsup, not an independent Čech obstruction to arithmetic equality.

### 7. Formalization and research receipts

#### Positive-`k` irreducible workload and the rank-one boundary (October 2026)

The exact triage in `receipts/positive_k_next.json`, derived by
`python/positive_k_next.py` from the positive-`k` class receipt, leaves 104
locally admissible irreducible Thue equations across 61 curves. The absolute
leading coefficients are 1 in 68 equations, 2 in 25, 3 in 10, and 4 in one.
Eighty-seven equations have at least one known representation in the bounded
search, which is evidence of a hit and cannot establish a complete list.
The 39 curves whose classes are locally impossible or reducible are
complete in Lean with proved class lists (`Generated/ClassLists/K*.lean`);
this receipt does not certify them.

For $F(u,v)=au^3+B u^2v+Cuv^2+dv^3$ with $a=\pm1$ and $3\mid B$, set
$h=B/(3a)$, $p=C/a-3h^2$, and $q=d/a-(C/a)h+2h^3$. If
$z^3+pz+q=0$, direct multiplication gives
$$F(u,v)=aN_{\mathbb Q(z)/\mathbb Q}((u+hv)-vz).$$
The discriminant $-4p^3-27q^2=-108k$ is checked for each monic row. Thus
$F=1$ gives a unit of $\mathbb Z[z]$ immediately. This identity removes
the norm-representative question for 68 equations, but a complete unit
generator and a complete zero set for the associated exponent recurrence
are still required. See `docs/POSITIVE_K_NEXT.md` for the first pilot,
$k=2$, where $F=-u^3-3uv^2-2v^3=-N(u-vz)$ with $z^3+3z+2=0$.

If units are proved to be $\{\pm\varepsilon^n:n\in\mathbb Z\}$, writing
$\varepsilon^n=A_n+B_nz+C_nz^2$ reduces this monic source to the exact
zero problem $C_n=0$ together with the norm sign. A bounded scan of $n$
cannot close that recurrence. A complete certificate needs an effective
exponent bound with exhaustive reduction, or residue-class $p$-adic
analytic arguments that cover every integer exponent. This is the
mathematical boundary for the proposed rank-one source engine.

For $k=2$ both steps are now proved in Lean (`Plus2.lean`, `Skolem3.lean`).
The units of $\mathbb Z[z]$ are $\pm\eta^n$ with $\eta=17-3z+5z^2=\varepsilon^{-1}$,
$\varepsilon=1+z-z^2$. The proof uses a real-embedding reduction and a
kernel-checked box, and the norm is split as
$N(g)=\sigma(g)(\mathrm{re}^2+\kappa^2j^2)$ without complex numbers. The $z^2$
coordinate of $\eta^n$ vanishes only at $n=0$, for every integer $n$. This is a
3-adic argument by integer valuations: $\eta^3$ and $\eta^{-3}$ are
$\equiv 1 \pmod 3$ with a nonzero linear term, and the residues $n\not\equiv0$
are excluded modulo 3. Hence $-u^3-3uv^2-2v^3=1$ only at $(-1,0)$. With the
proved class list, `K2.plus2` states that the integral points of $y^2=x^3+2$ are
exactly $(-1,\pm1)$, with no premise.

**The integer Skolem lemma at an odd prime** (`SkolemP.corner_zero`). This
lemma was proposed in the second OEIS handoff and is now proved in Lean. Let
$A$ be an integer $3\times3$ matrix, $p$ an odd prime and $M\ge1$, and suppose
$$A^M=I+pD,\qquad p\nmid D_{20},\qquad p\nmid (A^r)_{20}\ \text{for}\ 0<r<M.$$
Then $(A^N)_{20}=0$ only for $N=0$.

For $N=Mm+r$ with $r\ne0$, reduction modulo $p$ leaves $(A^r)_{20}$. For
$N=Mm$ with $m>0$, expand
$(I+pD)^m=I+pmD+\sum_{j\ge2}\binom mj p^jD^j$. If $e=v_p(m)$, the linear
corner term has valuation exactly $e+1$. Every later term has valuation at
least $e+2$, because $\binom mj=(m/j)\binom{m-1}{j-1}$ and $j-v_p(j)\ge2$.
Applied to $\eta$ and to $\eta^{-1}$, the lemma covers every integer
exponent.

**Rank-one sources, generically** (`RankOne.lean`). For $z^3=Pz+Q$ with a
complex pair, the norm splits as $N(g)=\sigma(g)(\mathrm{re}^2+\kappa^2j^2)$
with $\kappa^2=3\rho^2/4-P$. A reduced unit has $|\mathrm{re}|\le1$ and
$|j|\le J$, where $\kappa^2J^2\ge1$. Since $b=j+c\rho$ and
$a=\mathrm{re}+b\rho/2-cP+c\rho^2/2$, each $c$ admits only one or two $b$,
and each $(b,c)$ about three $a$. The kernel checks these slabs (15–31
elements) instead of a box of up to $4\cdot10^5$ elements.

The second handoff's bounded scan found $p=3$ candidates for one-source
curves. In each case the candidate is $\varepsilon$, and $\eta=\varepsilon^{-1}$
is proved fundamental:

| $k$ | source | order | $\eta$ | points |
|---:|---|---|---|---|
| 4 | $-u^3-4v^3$ | $z^3=-4$ | $5-3z+2z^2$ | $(0,\pm2)$ |
| 33 | $-u^3-6uv^2-10v^3$ | $z^3=-6z-10$ | $77-13z+10z^2$ | $(-2,\pm5)$ |
| 49 | $-u^3-14v^3$ | $z^3=-14$ | $29-12z+5z^2$ | $(0,\pm7)$ |
| 81 | $-u^3-18v^3$ | $z^3=-18$ | $55-21z+8z^2$ | $(0,\pm9)$ |

With the proved class lists, `K4.plus4`, `K33.plus33`, `K49.plus49` and
`K81.plus81` hold with no premise. The same engine handles shifted sources
and curves with several sources, and closes eleven more curves
(`MORDELL_BRANCH.md` §7.4). Eighty-six irreducible equations remain.

**An exact bridge to OEIS** (`python/positive_k_oeis.py`). Write
$P_k=\lbrace(x,y)\in\mathbb Z^2:y^2=x^3+k\rbrace$, $T_k$ for its size,
$R_k$ for the number of its points with $y\ge0$, and $Z_k$ for the number with
$y=0$. Sign symmetry gives $T_k=2R_k-Z_k$, and $R_k$ is the number of distinct
$x$. For $1\le k\le100$:
- `A081119` states $T_k$, and `A134108` states $R_k$.
- `A054504` lists the $k$ with $T_k=0$.
- `A134220`–`A134223` list the $k$ with $R_k=1,2,3,4$.

All 100 point lists of `receipts/positive_k.json` agree with these seven
definitions (`receipts/positive_k_oeis.json`). Of these rows, 72 are
Lean-complete and 28 are census evidence. The agreement is an independent
regression of the hit semantics, including the single $y=0$ point. It is not
a completeness proof.

The Lean sources specify the hit predicate and elementary proofs. As of release 0.6 they compile against Lean and Mathlib `v4.20.0`: exact definitions, HasDensity⇒H, the bounded-count squeeze, the exact finite-surgery identity, periodic rationality, the rigid truncation, the integer-closure step, and the analytic finite-hit theorem are all `LEAN_VERIFIED`, and three files needed tactic repairs first (a source line containing neither `sorry` nor `axiom` could and did fail to elaborate). A verified numerical cutoff remains to be layered on. Boshernitzan's criterion belongs in a named external-assumption boundary until a formal statement and proof are imported. A Lean theorem must not be inferred from an exact Python certificate, nor a Python test from an uncompiled Lean term.

The τ monotonicity assertion should be a runtime property of actual manifests or a hypothesis of a rational-valued structure; it is false for a generic list, for example [1,0]. An uninterpreted proposition named an obstruction has no consequences until related to a mathematical construction. The old periodic zeta and heat statements are true with their hypotheses; heat density has a broader Abelian version. The tropical maximum and cofinite Čech statement are elementary observations. The BSD receipt should be replaced by the shifted-curve application of Siegel. The research ledger in this package distinguishes these theorem dependencies, executable checks, and open questions.

### 8. Program ahead

The most useful next proof problems concern rates and exceptional arithmetic inside H=0. For a given family, ask whether there is a local congruence obstruction, an exact parameterization, a Pell-type sparse infinite family, a genus-one finiteness theorem, or a determinant-method bound that genuinely fits the anisotropic x/y ranges. For polynomial perturbations, ask whether the rigid finite-hit cutoff can be made tight enough to enumerate all hits; for nonrigid polynomials, ask whether a specific exponential-sum estimate supplies an explicit sublinear rate beyond abstract equidistribution. For transforms, prove what a stated asymptotic A(N)∼cN^α(log N)^β actually implies about Z_X and K_X, and record the Tauberian hypotheses needed for converses. For software, keep exact hit semantics at the input boundary and let independent arithmetic formulas be the regression oracles.

### Sources and dependency boundary

Michael D. Boshernitzan, “Uniform distribution and Hardy fields,” *Journal d'Analyse Mathématique* 62 (1994), 225–240, DOI [10.1007/BF02835955](https://doi.org/10.1007/BF02835955). The precise theorem is restated as Theorem 1.1 in Michael Reilly, [“A criterion for weighted uniform distribution along functions from a Hardy field”](https://arxiv.org/abs/2606.08040) (2026). Joseph H. Silverman, [*The Arithmetic of Elliptic Curves*, Chapter IX](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf), proves the relevant finiteness theorem of Siegel and explains its non-effective aspect. E. Bombieri and J. Pila, [“The Number of Integral Points on Arcs and Ovals”](https://people.maths.ox.ac.uk/pila/Ovals.pdf), establishes integral-point estimates in specified boxes; no general α bound is silently imported from that paper here.


## Open-front implementation checkpoint

The next implementation checkpoint is recorded in [OPEN_FRONTS.md](OPEN_FRONTS.md). It adds native cubic multiplication laws, weighted finite-zero and lattice-period lemmas, a complete even-quartic pilot, square-root arithmetic refinements, and concrete residue-ring coordinate export. The k=22 slab and named Matveev premises remain open; no additional Mordell completeness is claimed.


## Complete nonempty norm orbits and native cubic transport — October 3, 2026

The weighted-orbit framework now produces complete nonempty lists. `WeightedNormList.complete_of_cert` starts with the existing exact rank-one norm slab, rather than accepting an additional unproved orbit-generation assumption. It takes independently certified bounds for the forward and inverse unit orbits of each reduced representative and constructs the two finite exponent ranges, filtered by the exact norm and zero-coordinate conditions. A representative matrix need not be invertible. The sufficient weighted Skolem tests must still be checked separately in every residue class; there is no claim that all norm equations automatically satisfy them.

The worked example is the cubic order z³=−4 and norm ±107. The unit η=(5,−3,2) has inverse ε=(1,−1,−1). An exact rational certificate reduces the norm problem to a 3,631-candidate slab, whose complete representative list is (-1,-3,0) and (1,3,0). Both directional periods are 3 at the prime 3. Lean checks the matrix periods and the nonzero or first-order-zero alternatives for every residue class. In the plane with third coordinate zero, the complete norm ±107 list consists exactly of those two representatives. Therefore, for arbitrary integers u and v, u³+4v³=107 if and only if u=−1 and v=3. The final theorem has no named analytic premise.

This supplies another exact arithmetic atom that can be used inside a larger query. The consumer in `parallel_formula/norm107` proves that the cubic equation together with u≥0 is equivalent to False. In one local Z3 5.1.0 trial, the original query timed out at its 3-second limit and the finite linear replacement returned unsat in about 0.00077 seconds. Raw inputs, source hashes and timings are retained. This is one proof-supported example, not an industrial speedup claim: the separately committed 181-file industrial portfolio experiment remains a negative performance result and opt-in.

The native binary-cubic table also has a determinant norm and an exact integral basis bridge. Multiplication of native elements preserves this norm multiplicatively. With binary cubic coefficients (a,b,c,d), Norm(au+vω)=a²(au³+bu²v+cuv²+dv³), while det[1,ξ,ξ²]=−(au³+bu²v+cuv²+dv³) for ξ=uω+vθ. The a² factor is retained; norm and index form remain distinct objects. For shifted negative-monic coefficients (-1,-3h,P-3h²,Q+Ph−h³), the integral map (x₀,x₁,x₂)↦(x₀−hx₁+(h²−P)x₂,x₁+hx₂,x₂) has a proved inverse and preserves multiplication and norm in the order z³=Pz+Q. Arbitrary overorders and a basis-independent nonmonic source solver remain open.

The quartic pilot now excludes every even perfect-power exponent at nonzero arguments, by reducing v^(2d)=3u⁴+3u²+1 to its complete square classification. This does not settle odd powers. The integer square-root pilot now proves that a nonnegative root with r²≤X≤2,147,483,647 satisfies r≤46,340. Intermediate overflow and bitwise refinement in the original SPARK program still require separate work.

For the large k=22 source, `RankOneIntegerSlab` proves exact equality between the original rational floor/ceiling endpoints and denominator-cleared integer computations. The generator's integer mode prepares 100 modules of 2,000 slices each. The first module was reproduced successfully in 39.715 seconds. The earlier running job and its historical 53-chunk progress were lost during workspace maintenance; they are not used to claim a current complete proof. Only the checked pilot is committed, and the final k=22 source and curve classification remain unproved at this checkpoint. The resumable checker requires both a matching proof-input hash and an existing Lean object. A fresh full generation still needs every chunk and the final source check.

The new foundational modules, concrete norm result, quartic extension, square-root range and endpoint conversion were checked sequentially with Lean 4.20.0. A focused audit of 13 declarations and the whole-query consumer reports only propext, Classical.choice and Quot.sound. The full repository build and make verify were not rerun in the restored environment; committed validation receipts distinguish these scopes.

The restored Python suites ran 356 tests with no failures (352 passed, four skipped); the independent certificate audit passed 19/19. The integer-mode k=22 pilot passed again, and a subsequent resume check reused its matching proof-input hash.


## Closing k=22 and joining the parallel replay push — October 3, 2026

The expensive k=22 computation is complete. All 100 separate integer-endpoint modules passed Lean, and the assembled rank-one source passed afterward. The committed first chunk was reused through its matching proof-input hash; 99 fresh checks took 67.3 minutes in total. The final source theorem took 2.417 seconds once those modules were available. This is a long exact kernel computation, not a bounded search substituted for completeness. The complete source files, raw kernel log and per-module timing ledger are retained in the repository.

The arithmetic reduction has two binary-cubic classes. The class (0,−3,0,−22) is impossible modulo 9. For the remaining F(u,v)=−u³−6u²v−3uv²−4v³, the encoding is −Norm((u+2v)−vz) in z³=9z−14. The certified fundamental unit is (388537,−357959,99671), with inverse (−199,609,185). The norm slab checks 971,659 original candidates, and the two Skolem periods at the prime 3 prove the zero third coordinate occurs only at exponent zero. Consequently −u³+9uv²−14v³=1 exactly at (−1,0), and applying this at u+2v solves the original class exactly at (−1,0).

The separate class-list proof checks all 82 forms in its finite coefficient box and their exact unimodular transports. It then proves, for every pair of integers x,y, y²=x³+22 if and only if (x,y) is (3,−7) or (3,7). Both the class-list theorem and the final curve theorem passed. This raises the positive-curve registry from 72 to 73, with 34 curves using irreducible rank-one sources. There is no named Matveev or unproved class-list premise in this result. The focused source and curve axiom reports contain only the standard Lean axioms.

The existing finite-formula emitter now consumes the new curve theorem. Its retained example has the original curve equation and the additional constraint x>3. The emitted whole-query equivalence was accepted by Lean; the finite replacement rejects both complete curve points. Raw solver measurements for this one example are recorded separately, with a 3-second cap on the original. The point is an exact theorem-backed replacement of an integer search, not a general industrial speedup assertion.

The parallel session's newer commit 3789453 was reviewed and integrated before this release. It preserves the original solver strategy and improves command scanning and bounded native transport. Its retained single-host experiment reports identical slices for 3,602,272 commands in the pinned 307 MB ELSTER corpus, 2.7× faster scanning, and 4.73% less summed replay wall time across 5,612 fixed-prefix queries, with 64 more solved queries and no SAT/UNSAT conflicts. These results are distinct from the earlier negative strategy-portfolio experiment; neither result is overwritten. The complete package contains both the mathematical source closure and the parallel replay implementation, reports and monograph.

Regeneration retains the separate k=22 modules and matching proof-input identities. The heavy-build script checks independent chunks sequentially before building the assembled source. README counts combine the retained historical global axiom report with accepted focused checks; the entire repository Lean build and make verify were not rerun in this restored environment. k=94 and its 5,294,219-candidate slab remain open, as do the rank-two analytic premises, arbitrary-overorder transport, odd-power quartic questions and the concrete cryptographic prime certificate.

Final validation ran all four `make test` suites: 368 tests, 366 passed and two skipped because Why3 is unavailable, with no failures. The independent certificate audit passed 19/19. The retained k=22 example timed out on its original query at 3.004 seconds and returned unsat on the proved finite replacement in 0.001336 seconds with Z3 5.1.0; this is one local example.


---

# Generating functions, queryable populations, and observable dynamics

**What this extension delivers.** PerfectPower now connects exact rational formal series, restricted weighted-budget populations, positive-cost machine paths, DynaComp reduction packets, and differential-operator coefficient recurrences through one executable interface. The implementation extends existing rational-function arithmetic, recurrence execution, witness resolvents, future-state quotients and binomial period modules. It does not replace those engines with independently maintained versions. The new common operation is coefficient extraction: a coefficient can count original tuples, aggregate ordered action paths, encode an impulse response, or describe a normalized formal solution of a supplied differential equation. Those meanings remain attached to their sources.

The motivating reference is Herbert Wilf's [generatingfunctionology](https://www2.math.upenn.edu/~wilf/DownldGF.html), particularly its treatments of formal series, recurrence translation, the sieve method, combinatorial identities and WZ certificates. The implementation is original repository code based on established mathematics. Neither the book nor a copied edition is redistributed. Large-index rational coefficient extraction uses the parity-reduction method of Alin Bostan and Ryuhei Mori, described in their [2021 paper](https://mathexp.eu/bostan/publications/BoMo21.pdf). The certificate layer follows the rational shift identity introduced by Wilf and Zeilberger in [Rational Functions Certify Combinatorial Identities](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/rational.html). The repository contribution is the integration with preserved original-coordinate populations and exact observable transport, rather than a claim to invent these methods.

**Formal series as a shared representation.** A rational formal series is a fraction P(z)/Q(z) with rational coefficients and Q(0) nonzero after cancellation. Numerators and denominators are supplied constant-first. The interface normalizes Q(0)=1 and retains polynomial transients: cancelling an invisible pole or reducing a nilpotent machine to a finite polynomial must not lose its early nonzero coefficients. Its evidence method calls the existing recurrence compiler, which supports numerators of degree larger than the denominator. The coefficients then have a finite initial transient before the homogeneous recurrence applies.

The parity algorithm multiplies the numerator and denominator by Q(-z). The denominator becomes an even polynomial. To recover coefficient n, the numerator retains its even or odd coefficients according to the parity of n, the denominator retains its even coefficients, and n is replaced by floor(n/2). Repeating gives the answer without generating the preceding n coefficients. The implementation uses ordinary polynomial multiplication, so the useful complexity statement is quadratic in polynomial degree and logarithmic in the index in the arithmetic-operation model. Rational numerator and denominator sizes can still grow; an arithmetic-operation count is not a constant-time or fixed-memory guarantee.

Exact queries have an 8,192-bit coefficient limit, optionally tightened by the caller. Modular queries support composite as well as prime moduli when every supplied rational denominator is invertible modulo the chosen modulus. The library rejects a nonunit rather than inventing a modular fraction. A geometric coefficient at index 10^18 can therefore be queried modulo 1,009 without constructing an integer with 10^18 bits. Polynomial-growth counts can often be returned exactly at similarly large indices. A positive work or bit limit is part of the executable scope.

Multiplying rational series convolves their coefficients. Dividing by 1-z makes prefix sums. Applying theta=zD multiplies coefficient n by n; repeated applications supply moments. Arithmetic subsequences reuse the existing companion-matrix witness resolvent, including constant subsequences and singular transition matrices. These operations concern formal identities. They require no numerical eigenvalues, empirical recurrence fitting, or analytic convergence assumptions.

**Budget populations retain actual objects.** A budget population has between one and sixteen named-by-position original integer coordinates. Each coordinate has a positive integer weight, a nonnegative lower bound, an optional upper bound, and an optional residue restriction. Objects satisfy an exact weighted budget. Equal weights do not identify coordinates: the objects (1,0) and (0,1) remain distinct when both are legal. Their ordering is lexicographic in the original coordinate tuple.

For weights 1,2,3 without further restrictions, the counting series is 1/((1-z)(1-z^2)(1-z^3)). The retained budget-20 example has exactly 44 objects. Rank seven is (2,0,6), whose weighted sum is 20. The population supplies an exact count, an inclusive cumulative count, selection by rank, reverse rank and bounded paging. Coordinate restrictions change the factors before counting, so selection does not recover an illegal representative from an unrestricted count.

If the first admissible value of coordinate i is a, its modulus is m and weight is w, the unbounded factor is z^(wa)/(1-z^(wm)). A finite coordinate with K admissible values multiplies this by 1-z^(wmK). Large lower bounds are retained as a separate shift, avoiding an enormous dense numerator full of zeros. A lower bound of 10^12 is consequently a legitimate supported onset when the rational factors themselves fit the degree budget.

Rank selection is not a scan through the coordinate interval. For a prospective coordinate prefix, the count is a difference of two coefficients of the suffix series divided by 1-z^(wm). Binary search locates the coordinate containing the requested rank; the algorithm subtracts the preceding prefix mass and continues with the remaining coordinates. Reverse ranking uses the same prefix identity. The retained two-coordinate example counts 1,000,000,000,001 objects at budget 10^12 and selects rank 100,000,000,007 as (100,000,000,007,899,999,999,993). It constructs neither that population nor a trillion-element coordinate list.

This backend handles independent coordinate bounds and residues together with one additive budget. Arbitrary cross-coordinate polynomial restrictions require another supported population backend or a new reduction. Degree limits also restrict dense finite factors: a huge finite upper bound can exceed the implemented factor budget even when its mathematical generating function is simple. Such a refusal is a resource limit, not a proof that counting is impossible.

The existing semilinear compiler has a separate adapter. Its disjoint periodic cells become a rational series marking admissible nonnegative integers. Finite progression tails subtract their first excluded monomial. The adapter replays the source cell certificate and does not double-count overlapping Boolean clauses. Its dense onsets and endpoints have an explicit degree limit. This complements the budget backend's lazy global shift rather than pretending every semilinear input has a small dense representation.

**Ordered paths with positive costs.** A machine operator A_c at cost c contributes z^c A_c. With seed s and readout H, the output series is H(I-sum_c z^c A_c)^-1 s. Operators act on column states. A coefficient sums weights of ordered paths having the requested total cost. Matrix multiplication remembers the order of actions, even when the scalar variable records only their total cost. Separate actions with the same destination and cost contribute separate multiplicities.

All costs must be positive integers. This makes the transfer polynomial zero at z=0 and guarantees a uniquely invertible formal matrix. Zero-cost cycles are not accepted: summing infinitely many such paths would need a separate closure rule. Signed rational matrix entries are allowed for linear observable systems; their coefficients are weighted responses, not necessarily nonnegative population counts.

Discovery solves the rational matrix system. The resulting packet contains the normalized source, its digest, the vector of rational solutions and the readout fractions. Replay checks (I-T)V=s and every output identity without rerunning elimination or fitting a finite prefix. A changed seed, vector, output or digest is rejected. The source argument can bind replay to the caller's actual original specification. Discovery is capped at twelve states, while a supplied exact quotient may transport a source of up to 256 states to a reduced system within that elimination limit.

Finite SOE machines use one matrix for each named enabled action. Disabled actions contribute no edge. The adapter can use the existing all-future quotient when the accepting set is constant on each quotient block. Acceptance is a protected output: an arbitrary subset cutting across a block cannot be transported through that quotient. In the retained two-state example, both states are future-equivalent, two actions have costs one and two, and the quotient has one state. The accepted-word coefficients are 1,1,2,3,5,8,... because the cost series is 1/(1-z-z^2). The distinction between two action names survives state minimization.

**The concrete DynaComp bridge.** This extension reads actual `dynacomp.linear/1` and `dynacomp.switched/1` formats from DynaComp commit 70f609c. The examples were generated by that repository's discovery functions and accepted by its own replay functions before being exported. PerfectPower requires no DynaComp installation to consume their saved packets. It performs its own exact transition, input and output identity checks.

A linear packet gives EA=GE, EB=H and DE=C. These establish C A^n B=D G^n H for every n, and likewise preserve an initial-state response after encoding. The interface exports one response series per input column and an optional initial-state series. Timing is explicit: coefficients C A^n B contribute at time n+1 for the convention x[t+1]=A x[t]+B u[t]. Omitting that delay would shift a forced response by one step.

The retained six-state model reduces to two states. Its reduced transition is [[1/2,1/4],[1/4,1/2]], and the common denominator of its observable responses is 1-z+3z^2/16. The first input's first output has numerator 1-z/2; its other output has numerator z/4. These fractions capture every future impulse coefficient of the declared exact model. They also expose cumulative responses, moments and large-index modular questions to the common series interface.

Switched packets require EA_a=G_aE for every supplied mode. Assigning each mode its own positive cost gives E T(z)=T_reduced(z) E, so the same quotient preserves every total-cost coefficient. The retained two-state, noncommuting example reduces to one state and yields denominator 1-3z-z^2. Noncommutativity is handled by the operator transport; it is not discarded during discovery. Aggregated cost counts alone do not prove equivalence on each mode word. That stronger fact comes from the cost-specific intertwining identities already checked.

This connects directly to DynaComp's current observable-reduction program. It does not turn an approximate thermal reduction into an exact one, remove its error bounds, or establish an industrial speedup. Historical Feynman-integral/IBP ambitions connect more naturally through the shift-certificate and differential-operator interfaces described below. This push supplies those algebraic entry points; it does not claim a general Laporta reducer, Ore-ideal elimination engine, or complete master-integral computation.

**Differential equations become coefficient engines.** For L=sum_j z^j q_j(theta), coefficient n of Lf is sum_j q_j(n-j)a[n-j], omitting j>n. `ThetaSeries` compiles that triangular equation, accepts polynomial forcing, and checks every supplied initial coefficient. Roots of q_0 at nonnegative integers are singular coefficient indices. Each needs a supplied seed; the remaining equation at that index must also be consistent. Away from those indices the leading coefficient determines the next value exactly. Missing seeds and incompatible initial data are rejected.

The Weyl bridge rewrites z^i D^j using theta(theta-1)...(theta-j+1). If negative z powers would occur, it first multiplies the operator on the left by the smallest sufficient power of z. Multiplication by z is injective on formal series, so this does not change the homogeneous formal kernel. The rational-differential adapter first clears a common polynomial denominator and then applies that normal ordering. Analytic interpretation at singular parameter values remains a separate question.

This compiler consumes the existing Vandermonde and Apéry operator packets. Thirty-two coefficients for each of the three named families agree with independent direct binomial summation. It also consumes the actual rational monic operator exported by the rank-two Apéry differential module, clears its denominators and reproduces the same normalized coefficients. This is an executable bridge between the period/differential machinery and sequence arithmetic. A formal solution with selected seeds is not automatically a particular analytic period integral or a perfect-power classification of its coefficients.

**WZ search keeps the boundary obligation visible.** The certificate engine works over Q(n)(k). Given r_n=F(n+1,k)/F(n,k), r_k=F(n,k+1)/F(n,k), and G=R F, it checks r_n-1=r_k R(n,k+1)-R(n,k) as an exact rational identity. Bounded discovery solves a supplied denominator ansatz for R with a polynomial numerator in k. Failure means the ansatz was unresolved, not that no WZ certificate exists. The normalized binomial example discovers R=-k/(2(n+1-k)).

The packet explicitly says that support and endpoint cancellation have not been proved. The interior identity can have poles on boundaries where factorial cancellations or zero extensions are needed. A complete summation theorem must justify those cases and retain the boundary contribution. The generic Lean telescope proves the finite difference sum equals g(n)-g(0), with both endpoints present. It therefore supplies the correct foundation for future source-bound WZ summation packets without silently assuming a vanishing boundary.

**What Lean has checked.** `PerfectPower/GeneratingFunctions.lean` needs only Lean 4.20's standard library. It proves uniqueness of integer coefficient sequences satisfying the normalized rational coefficient law, finite additive transport, all-coefficient preservation for positive-delay recurrences under cost-specific intertwining, target-output preservation, finite telescoping, and theta-recurrence uniqueness with explicit singular seeds. A concrete two-state/two-cost integer quotient instantiates the generic transport theorem and preserves its outputs at every total cost. Audited theorems use only standard `propext` and `Quot.sound`; there is no `sorry` or extra proof axiom.

These are mathematical foundation proofs and the concrete integer transport instance. They do not establish correctness of the Python coefficient algorithm, rational elimination, general JSON packet parser, population rank compiler or rational WZ search. The integer coefficient uniqueness theorem also must not be relabelled as a kernel proof of every rational-coefficient Python instance. The corresponding executable results carry exact arithmetic replay and independent tests. Keeping these meanings separate makes the new bridges useful without overstating formal coverage.

**Reproduction and limits.** Run `make generating-functions` for focused tests and deterministic example receipts. Run `make generating-functions-kernel` with Lean 4.20 on the path, or set `PERFECTPOWER_LEAN` to its executable. The foundation does not require Mathlib or a full historical project build. Use `python -m perfectpower generating-function examples/generating_functions/budget.json`, substituting any retained JSON example for a different operation. The persistent catalogue registers `rational_series`, `theta_series` and `budget_population`; the JSONL service also accepts the unified `generating_function` operation.

Rational polynomials have maximum degree 256 and coefficient size 8,192 bits; indices are nonnegative 64-bit integers. Subsequence compilation retains the existing 64-state companion limit. Theta execution is sequential and capped at 4,096 coefficients. WZ search bounds the numerator ansatz degree by eight and outer rational degrees by 32. Cost matrices use positive costs at most sixteen, at most sixteen operators and at most sixteen readouts, with rational algebra work limits. Limits produce explicit errors rather than incomplete answers presented as complete populations.

The next mathematical extensions are sparse shifted finite factors, multiple independent budget variables, automatic boundary certificates for summation, formal refinement of coefficient/rank algorithms, and generic q-shift or creative-telescoping discovery. Analytic singularity extraction and asymptotic estimates are not implemented in this push. What is delivered is a coherent exact route from preserved structures to queryable coefficient families, together with actual DynaComp interoperability and a small independently checked Lean foundation.


---

# From formal counting to exact binary inputs

This chapter records PerfectPower 0.9.4. It incorporates the generating-function branch `892987e`, then connects its formal rational series to exact minimal sequence realizations and analytic remainders. It also implements binary64 bit arithmetic and perfect-power queries on exact stored values. New certificates in this chapter are independently reconstructed in Python; no new Lean theorem is claimed for the bit kernel, analytic bounds or realization compiler. The merged Wilf branch has its own Lean scope and retained audit in `receipts/generating_functions`.

## Preserve the other session's machinery

The merged [generating-function chapter](GENERATING_FUNCTIONS_MONOGRAPH.md) supplies budget populations, cost-weighted machine resolvents, rational-series coefficient queries by Bostan–Mori parity reduction, holonomic coefficient engines, WZ identities and exact DynaComp packet transport. It retains coordinate maps, source semantics and input delays. This release does not replace those interfaces. The existing `RationalSeries` gains `realization_certificate` and `analytic_tail`, both using a portable stdlib kernel also shipped byte-for-byte in DynaComp 0.10.0. Its existing offset/step subsequence API remains intact. `Recurrence.minimal_generating_function` adds cancellation-aware compilation while preserving the old numerator/denominator API.

This matters because a formal identity, an analytic approximation, an exact recurrence definition and a conjecture discovered from a prefix have different scopes. None of the new operations turns prefix evidence into an all-index recurrence theorem. None turns a necessary congruence test into a complete solution family.

## A generating function can be a minimal machine

`RationalGF` stores a reduced rational fraction P(z)/Q(z), with coefficients constant first and Q(0)=1. It cancels the polynomial gcd, handles zero canonically, and rejects floating coefficients. For a nonzero fraction the minimal autonomous realization of its complete coefficient sequence has dimension r=max(deg Q,deg P+1). Its convention is a_n=C A^n x_0, starting at n=0. A shift register initialized by the first r coefficients realizes the sequence; padded zero recurrence coefficients retain every transient.

Denominator degree alone is insufficient for this convention. The fraction z/(1-z) describes 0,1,1,... and requires two states, whereas 1/(1-z) describes 1,1,1,... and needs one. A finite polynomial of degree k gives a finite-support coefficient sequence with k+1 states. Cancellation is equally important: (1-z)/(1-z) gives a single initial impulse and then zeros, not the persistent constant sequence. Transfer functions with feedthrough or delayed input injection have different indexing and are not silently identified with autonomous sequences.

The certificate includes an exact nonzero leading Hankel determinant of size r. Any s-state linear realization factors every Hankel matrix through an s-dimensional state space; the determinant supplies the lower bound r and the constructed shift register supplies the upper bound. Replay rebuilds the normalized fraction, sequence prefix, matrices and determinant. The zero sequence has an empty realization. State and sequence realization are bounded to 128 states. Arithmetic includes sums, products, index weights, eventual periodic prefixes and stride/offset extraction. Large indices use binary matrix powering, while the existing `RationalSeries` keeps its bounded Bostan–Mori path for coefficient queries.

The inverse state-to-fraction path uses the exact trace recurrence for det(I-zA), computes a numerator from the prescribed initial response, and cancels unobservable factors. This is minimality for a particular sequence; it does not prove that an arbitrary source state or every possible input is preserved.

## Two supported analytic remainder mechanisms

[Analytic Combinatorics](https://ac.cs.princeton.edu/home/) and [Wilf's generatingfunctionology](https://www2.math.upenn.edu/~wilf/DownldGF.html) explain why coefficient algebra and singularity structure can guide computation. The books are linked, not copied into the release. The implementation provides explicit remainder constants for two supported families rather than claiming a general singularity-analysis engine.

For P/Q with Q(0)=1, choose rational R>0 with delta=1-sum_{j>=1}|q_j|R^j>0. Then Q has no zero on |z|<=R and |P/Q|<=M=sum|p_j|R^j/delta. Cauchy's estimate bounds the coefficients by M/R^n. At |x|<R the discarded series terms n>=N have absolute sum at most M(|x|/R)^N/(1-|x|/R). Failure of this sufficient disk test refuses the certificate, without asserting a pole exists.

For rational alpha>0 and 0<=x<1, the coefficients of (1-x)^(-alpha) satisfy b_0=1 and b_{n+1}=b_n(n+alpha)/(n+1). They are positive. After N retained coefficients, every later term ratio is at most rho=x max(1,(N+alpha)/(N+1)). When rho<1, the remainder is at most b_N x^N/(1-rho), giving exact rational lower and upper endpoints. If rho>=1, more terms are required. This is a proved geometric majorant for a supported real branch, not an asymptotic estimate with an unspecified constant. Half-power tests independently square the endpoints to enclose the rational value 1/(1-x).

## Pell coordinates and modular hit counting

For a positive norm-one unit u+v sqrt(D), its powers have coordinates x_n,y_n satisfying both coordinate recurrences a_(n+2)=2u a_(n+1)-a_n. The initial conditions are x_0=1,x_1=u and y_0=0,y_1=v. `pell_generating` compiles these rational OGFs and their minimal sequence packets. A caller may supply a valid positive unit; otherwise the existing exact fundamental-unit routine supplies it. With a supplied nonfundamental unit the claim is just that unit's orbit, not all Pell solutions. Tests independently multiply units and check x_n^2-D y_n^2=1.

The retained D=2 unit is 3+2 sqrt(2). Index 100 is obtained by exact powering without scanning the coordinate interval. The sequence index n here counts unit powers. It is not the original integer-coordinate indicator of Pell solutions. Sparse coordinate-index hit sets should not be advertised as rational OGFs simply because their solution coordinates satisfy a recurrence.

`modular_power_gf` connects the existing exact finite-state recurrence cycles to rational indicator series. For a supplied integral recurrence and modulus M, it computes the exact set of d-th power residues, follows the full recurrence state until its first repeated state, and separates a finite prefix from a periodic cycle. If prefix weights are p_i and cycle weights are c_j, the accepted-index OGF is sum p_i z^i + z^mu(sum c_j z^j)/(1-z^period). It is normalized exactly, and replay reconstructs the entire cycle. The cycle table and OGF are canonical across JSON round trips.

Counts at huge exclusive endpoints use the existing exact prefix/block/remainder formula. In the retained Fibonacci square-residue filter modulo eight, exactly 416666666668 indices below 10^12 pass the congruence. This is not a count of Fibonacci squares. The constant sequence 17 passes the square-residue filter modulo eight at every index despite 17 not being a square. State discovery is budgeted; an unfinished cycle is not treated as periodic. The OGF normalization budget is 512 prefix-plus-cycle coefficients, with modulus at most 10000 and state exploration at most 100000.

## Binary64 words as exact arithmetic data

A normal word has exact value (-1)^s(2^52+F)2^(E-1075); a subnormal has (-1)^s F 2^(-1074). Decoding yields an integer significand and exponent, then removes powers of two. Thus every finite nonzero stored value has the unique form sign*u*2^e with u positive odd. Raw bit addition is not value addition. The encoding's negative order is reversed, signed zero has two encodings, and infinities/NaNs are not rational numbers. See the [NIST binary-format reference](https://dlmf.nist.gov/3.1).

The portable `binary64` module provides finite classification, exact dyadic decoding, bit transport, representable neighbors, a numeric order key excluding NaNs, exact integer dot accumulation, and rational round-to-nearest-even encoding. It handles subnormal ties, the normal boundary, exponent carry and overflow. NaN payloads survive transport but are refused as operands. Exact canceled sums round to positive zero; negative nonzero underflow can produce negative zero. The superaccumulator sums exact products of stored operands before one final rounding. This is a deterministic arithmetic contract, not a claim to emulate a sequential hardware dot product or to outperform it.

For degree d>=2, sign*u*2^e is a rational d-th power precisely when u is an integer d-th power, d divides e, and a negative sign has odd d. Necessity follows from prime valuations of a reduced rational power; sufficiency constructs the root. Odd u has at most 53 bits, so exact integer root search does not need factorization or a probable-prime assumption. Zero is a power at every supported degree. A replayable packet records the word, its fields, normalized dyadic pair, decision and exact rational root when one exists.

`binary_polynomial.polynomial_power_certificate` additionally evaluates a supplied exact rational polynomial at the exact stored argument, using rational Horner arithmetic. It classifies the resulting reduced numerator and denominator with the existing exact integer-root routine. A rational number is a d-th power exactly when both reduced numerator and positive denominator admit the corresponding integer roots, with the same sign restriction. This lane has explicit input and intermediate bit budgets; it never silently substitutes a rounded polynomial result. For the stored float 0.1, x^2 is exactly the square of 3602879701896397/36028797018963968. For x=10^16, x+1 evaluates to 10000000000000001, which is not a square, even though rounded hardware addition returns the square 10000000000000000. Neither statement recovers an intended decimal value from its rounded storage.

## Execution and reproduction

Use `python -m perfectpower arithmetic-series compile examples/arithmetic_series/pell.json --output packet.json`, then `python -m perfectpower arithmetic-series replay packet.json`. The same command compiles rational/recurrence/state OGFs, rational Cauchy bounds, binomial bounds, modular power OGFs, stored-value powers and exact polynomial queries. `PYTHONPATH=python python python/run_arithmetic_series.py` regenerates the receipts under `receipts/arithmetic_series` without timing noise. The merged Wilf demonstrations remain under `receipts/generating_functions`.

DynaComp uses the same binary kernel to run a specified exact-dot-then-round binary64 protocol and compose its loading and execution errors with existing finite source/model guarantees. Its 64-mode infinite heat source reduced to three states remains below 0.01 over 20 samples, including a uniform execution budget about 1.2e-15. PerfectPower does not import DynaComp to make its arithmetic decisions. The portable files are identical, and cross-check tests bridge PerfectPower's existing rational-series and recurrence interfaces.

Next priorities are a compiled exact-dot backend, all-time rounded-state invariants, certified efficient conventional dot products, additional algebraic branches with proved remainders, and applying cost/population resolvents to external query workloads. The scope of every accepted packet should remain explicit. A Python replay, a bounded arithmetic experiment and a Lean theorem remain separate forms of evidence.

Portable generating-function arithmetic additionally uses a 16384-bit value budget and at most 10000 retained coefficients. Large-index growing sequences refuse oversized arithmetic rather than attempting to allocate an unbounded answer. These limits do not change the exact mathematical identities.

Release verification for this extension: all 51 focused Python tests pass (22 new bit/analytic/arithmetic tests and the 29 merged generating-function tests). The continuation, expert-push and Galois suites also pass (14, 10 and 8 tests respectively). Both generating-function receipt scripts reproduce the retained packets unchanged. Python 3.12 is used locally with the declared research dependencies installed in an isolated environment. The broad package regression run is tracked separately; no new Lean build is claimed.

The broad regression run exposed an undeclared test dependency: eight existing modules import pytest, while CI installed only the research extras. This release adds a `test` extra and installs it in the Python workflow. It leaves the runtime dependencies unchanged. The affected pytest-style modules are exercised with pytest rather than treating a successful unittest import as a test run.

With the test dependency installed, all twelve affected pytest modules pass: 103 flavor/quartic tests and 41 Valentiner tests, with two intentional skips. CI now executes these function-based tests as well as the unittest suites. The dependency correction is a test-installation fix, not a change to mathematical runtime behavior.

A historical Weil regression still expected 457 unresolved Mordell lists after the retained backend receipts had closed them. Its assertion now protects both facts: the historical rank-witness frontier still has 457 rows (323 empty, 134 nonempty), and 457 checked external completions close those lists. It explicitly checks that these external completions do not claim Lean integral-list proofs. The reconciliation algorithm and mathematical receipts are unchanged.


---

# A=B: boundary-complete sum compilation (PerfectPower 0.9.5)

The source is Marko Petkovšek, Herbert S. Wilf and Doron Zeilberger,
*A=B*, [author-hosted PDF](https://sites.math.rutgers.edu/~zeilberg/AeqB.pdf).
Chapters 5–8 motivate rational antidifferences, creative telescoping, WZ
certificates and hypergeometric recurrence solutions. This release implements
an original bounded search and a small exact checker. It does not distribute the
book or claim to implement the complete Gosper, Zeilberger or Hyper algorithms.

## The missing connection

The existing `wz_certificates.py` verifies an interior rational identity in
Q(n)(k), but explicitly does not prove that summation endpoints disappear.
The existing `ThetaSeries` generates a formal series from a supplied operator,
but does not establish that an external sequence satisfies that operator.
This chapter supplies the missing link for a concrete family:

\[
S_p(n)=\sum_{k=0}^{n}\binom nk^p,\qquad p\in\{1,2,3,4\},\ n\ge0.
\]

The term definition, finite support, shift identity, endpoint cancellation and
initial values are checked together. The resulting differential operator is
therefore connected to a specified sum, rather than merely to numerical seeds.
The first two families yield order-one recurrences; the cube and fourth power
yield order-two recurrences. No rank or global minimal-order theorem is claimed.

## A polynomial certificate with safe endpoints

Fix an attempted order r and put N=n+r. Use the last shifted summand as the
common reference. For j=0,...,r,

\[
\frac{\binom{n+j}{k}^p}{\binom N k^p}
=\left(\frac{\prod_{h=0}^{r-j-1}(N-k-h)}
{\prod_{h=0}^{r-j-1}(N-h)}\right)^p=:U_j(n,k).
\]

This quotient is used as a rational identity first. The associated equality
of binomial terms extends across their zeros: when k>n+j, one numerator
factor is zero, and when k>N every binomial term is zero. Each denominator
factor is at least n+j+1 on the stated domain.

Seek coefficients a_j(n) in Q(n), normalized by a_r=1, and a polynomial
b(n,k) in k such that

\[
\sum_{j=0}^r a_j(n)U_j(n,k)
=(N-k)^p b(n,k+1)-k^p b(n,k).
\]

Matching powers of k produces an exact linear system over Q(n). Search tries
orders 1 through a supplied maximum, at most 3, and a supplied polynomial
degree, at most 12; the default degree is pr. This is a restricted ansatz,
not a universal denominator-reduction algorithm. An unsuccessful search says
`ANSATZ_UNRESOLVED`, never that no recurrence exists.

Set

\[
G(n,k)=k^p b(n,k)\binom Nk^p.
\]

The polynomial identity gives the summand recurrence as G(n,k+1)-G(n,k).
At k=N, the shifted binomial term is zero, so the same equality holds there
without dividing by it. G(n,0)=0 because p>0. G(n,N+1)=0 because its binomial
factor is zero. Summing from k=0 through N proves

\[
\sum_{j=0}^r a_j(n)S_p(n+j)=0\quad(n\ge0).
\]

The replay checks every certificate coefficient denominator is a polynomial
with positive constant coefficient and nonnegative remaining coefficients.
This sufficient test proves no poles for n>=0. It is deliberately stricter
than full real-root isolation: some valid alternative packets are refused.
There are no k denominators in b, so no hidden endpoint poles. Replay also
recomputes the first r sums directly. Leading coefficient one makes forward
execution unique for all n>=0.

For example, the cube sum compiles to

\[
(n+2)^2 S_3(n+2)
-(7n^2+21n+16)S_3(n+1)-8(n+1)^2S_3(n)=0,
\]

with S_3(0)=1 and S_3(1)=2. Its initial terms are
1, 2, 10, 56, 346, 2252, 15184, 104960.
This recurrence is discovered from the symbolic summand identity, not guessed
from those eight terms.

## Connecting the ordinary generating function

Clear the common Q(n) denominators to get polynomials A_j(n).
Let theta=z*d/dz and define

\[
L=\sum_{j=0}^r z^{r-j} A_j(\theta-j).
\]

At coefficient index m>=r, this is the forward recurrence at n=m-r.
The finitely many coefficients m<r need a polynomial forcing term calculated
from the checked initial sums. Keeping that forcing is essential: blindly
setting it to zero would reject or change the sequence. `theta_from_telescoping`
constructs the operator and delegates guarded exact execution to `ThetaSeries`.

These sequences generally have polynomial-coefficient recurrences. They are
not automatically finite-dimensional constant-coefficient realizations of the
kind DynaComp's rational generating-function bridge minimizes. This release
therefore changes PerfectPower only; it does not mislabel holonomic sequences
as finite-state linear systems.

## Antidifferences and proposed closed forms

`discover_antidifference` solves the identity

\[
r(k)R(k+1)-R(k)=1
\]

with a supplied polynomial denominator and bounded numerator degree. If
`t(k+1)=r(k)t(k)`, then R(k)t(k) is an antidifference. The checker independently
reconstructs the rational identity. `sum_from_antidifference` checks every
needed ratio denominator and certificate endpoint in a bounded integer
interval before returning its boundary difference. The supplied initial term
is a premise, explicitly recorded. This refuses poles even when a different
analytic continuation could cancel them. Empty intervals return zero only
when their certificate endpoint is defined.

The finite summation executor transports the term by exact ratio products;
it does not promise constant-time endpoint evaluation. The benefit here is a
reusable checked identity, not a universal faster summation claim.

`certify_hypergeometric_solution` substitutes a supplied rational first-order
ratio into the discovered forward recurrence and checks its initial values.
It proves equality to the sum using recurrence uniqueness and the positive
denominator guard. Retained packets prove ratios 2 for S_1 and
(4n+2)/(n+1) for S_2. A proposed constant ratio 8 for S_3 is rejected. Rejecting
one proposed solution does not establish that S_3 has no hypergeometric form.
Full Hyper and certified nonsummability decisions remain future work.

## Exact power queries and reproducibility

`BinomialSumSequence.power_hits` executes a bounded sequence window and calls
the existing exact integer power-root decision for each value. It reports all
hits in that window and explicitly denies an unbounded classification. For
S_1(n)=2^n, the square query over indices 0 through 119 finds exactly the even
indices. This illustrates the end-to-end definition→identity→recurrence→integer
value→power-root path. For the harder families, absence of hits in a finite
window proves nothing about all later indices.

Run the retained examples and independent direct-sum cross-checks with:

```sh
PYTHONPATH=python python python/run_telescoping.py
PYTHONPATH=python python -m perfectpower generating-function examples/telescoping/binomial_power_3.json
PYTHONPATH=python python -m perfectpower.telescoping replay receipts/telescoping/binomial_power_3.json
PYTHONPATH=python python -m unittest discover -s python/tests -p test_telescoping.py -v
```

Six example specifications, eight certificate receipts and a summary are
retained. Four families are independently cross-checked through index 100 in
the regeneration script. Tests also check shifted finite intervals, geometric
and polynomial sums, rational telescopes, corrupted identities, seed changes,
poles, incomplete searches, closed-form candidates and command-line replay.

All new proofs are exact Python replay, not Lean kernel theorems. Existing
Lean results are unchanged. Algebra, coefficient bits, term windows and
sequential indices have explicit limits inherited from the rational-function
and formal-series engines. Hitting a limit raises a work-limit exception;
it does not provide evidence against a mathematical identity. No performance
claim, revenue claim or benchmark extrapolation follows from this release.
