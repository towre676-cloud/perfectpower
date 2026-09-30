# Perfect-Power Hits Beyond Density

## Exact definitions, a polynomial dichotomy, finite-hit certificates, and the arithmetic of the zero branch

## 0. Status of every result (edition 0.8)

This table is the single source of truth. The research notes, the paper, the README and the trust boundary state the same claims. Labels: **Lean** means compiled and axiom-audited (only `propext`, `Classical.choice`, `Quot.sound`). **Lean ⇐ H** means compiled, with a named hypothesis that is not proved. **Paper** means a written proof. **External** means a computation by third-party software (Sage, Singular). **Evidence** means exact within a stated bound and silent beyond it.

| Result | Status | Depends on | Where |
|---|---|---|---|
| Density 0–1 law, rigid branch | Lean (`rigid_zero_one`, `rigid_dichotomy`) | — | `ZeroOne.lean`, `Rigid.lean` |
| Density 0–1 law, nonrigid branch | Paper | Boshernitzan (external theorem) | §3 below |
| Power type: all hits, or finitely many | Lean (`atlas_power`, `power_type_finite`) | — | `Atlas.lean`, `RungeReduction.lean` |
| Radical type $A(N)=\kappa N^{1/t}+O(1)$, $\kappa=(R/v)(v/z_0)^{1/t}$ | Lean for $c(vn-u)^rG(n)^d$ (`radical_asymptotic_int`, `atlas_radical`); general $F$ (rational bad degree 1): **Lean**. The pointwise reduction is `integer_radical_reduction`. The count is `Decomposition.radical_count`: $|A(N)-\kappa N^{1/t}|\le K$ with $\kappa\ge0$ and $2\le t\mid d$, keeping the exceptional zeros, both signs of the coefficient, negative shifts, and the unsolvable case ($\kappa=0$). The error is explicit: $K=2V+2(U+V|U|)+|U|+2+\deg F$ (`radical_count_explicit`). Positivity of $\kappa$ is decided in Lean (`radical_kappa_decide`): $\kappa>0$ iff there are infinitely many hits, iff some integer $n$ in an explicit finite range ($n\le |C|^{t-1}V^t+U+V|U|$) is a hit of the reduced form with $Vn>U$ | valuation core (Lean); rational Yun decomposition (Lean) | `RadicalAsymp.lean`; notes §3 |
| Pell type $A(N)=\kappa\log N+O(1)$, $\kappa=(\sum_\rho g_\rho/P_\rho)/\log\varepsilon$ | Lean for $An^2+Bn+C$ with a given unit (`pell_exact_count`, `atlas_pell`); general $F$ of Pell type (Theorem C): **Lean**. The pointwise reduction is `integer_pell_reduction`. The count is `Decomposition.pell_count`: $|A(N)-\kappa\log N|\le K$ for large $N$, $\kappa\ge0$. It uses a squarefree quadratic (nonzero discriminant), the branches $\pm\gamma_0$ of $\gamma^e=\mathrm{lc}(F)$, cleared denominators, the bounded cases $A<0$ and $A=\square$, Mathlib's Pell unit for $A>0$ non-square, the overlap at roots of $Q$, and the zeros of $F$. Positivity is decided in Lean (`pell_kappa_decide`): $\kappa>0$ iff some root $\gamma$ of $\gamma^e=\mathrm{lc}(F)$ is positive and not a rational square, and $\gamma Q(n)$ is a rational square at one integer $n$ past the vertex. Per branch, a bounded search with explicit range is `branch_infinite_iff_bounded`. The error is explicit (`pell_branch_explicit`, `pell_count_explicit`): $K=|B|+1+(2Z+3)^2(2A)^2K_c+(2Z+3)^2\log(2A+|B|)/\log\varepsilon$, with $Z=|\Delta|(1+u^2)$, $W=(2Z+2)(1+2\sqrt A)$ and $K_c=3+(2\log(W+|\Delta|)+\log(2+\sqrt{|\Delta|})+\log2)/\log\varepsilon$ per branch, and $\sum K_{\mathrm{branch}}+\deg F+2$ for $F$ | canonical orbit roots (Lean) | `PellExact.lean`; notes §4 |
| Finite type: finitely many hits | Lean ⇐ `SuperellipticSiegel` (`atlas_finite`) | Siegel (external) + geometric half of Theorem G (Paper) | `Atlas.lean`; notes §5 |
| Theorem G, combinatorial half ($\chi=d'(1-S)$; $\chi<0$ ⇔ non-exceptional) | Lean, all $d$ (`chi_eq`, `chi_neg_iff`); Riemann–Hurwitz integrality table for $d,\deg F\le12$ (`profile_table_ok`) | — | `ProfileG.lean` |
| Theorem G, geometric half (Kummer, Riemann–Hurwitz) | Paper; External check (Singular genus, Sage places at infinity) over the range stated in `receipts/theorem_g_check.json` | — | notes §5 |
| Runge enumeration, rigid branch | Paper (Theorem R); 19 instances Lean via pp-cert/1 (`check_sound`, `rungeCheck_sound`) | — | `Reflect.lean`, `CERTIFICATE_FORMAT.md` |
| Genus one: 399 non-monic/shifted families, 2 binomials | Lean ⇐ named Sage point lists (`Genus1.lean`, `Binomial.lean`) | Sage `integral_points` (External) | `Generated/Genus1.lean` |
| Genus one, unconditional: 1163 Mordell curves $y^2=x^3+k$, $0<|k|\le10^4$, with **no** integral points | **Lean** (elementary descent `MordellDescent.lean`; no hypothesis) | agrees with the Sage census, 0 conflicts | `Generated/MordellDescent.lean` |
| Genus one, unconditional and **nonempty**: $y^2=x^3-432u^6$ has exactly the integral points $(12u^2,\pm36u^3)$ for every $u\ne0$; so $n^3-432u^6=m^2$ iff $n=12u^2$ | **Lean** (`MordellFLT3.lean`, from Mathlib's `fermatLastTheoremThree`) | classical (the Fermat cubic) | `MordellFLT3.isHit_iff` |
| Genus one, unconditional, **positive rank**: $y^2=x^3-2$ (points $(3,\pm5)$), $y^2=x^3-4$ (points $(2,\pm2),(5,\pm11)$) | **Lean** (`MordellMinus2.lean`, `MordellMinus4.lean`; descent in ℤ[√−2], ℤ[i]) | Mathlib (Euclidean ℤ[i]; ours for ℤ[√−2]) | §5A |
| Genus one, unconditional, positive rank, **class number 2**: $y^2=x^3-13$ (points $(17,\pm70)$); with $y^2=x^3-5$, $y^2=x^3-6$ (no points) as further instances | **Lean** (`ClassTwo.lean` template: Thue lattice bound + kernel norm table; `MordellMinus13/5/6.lean`) | — | §5A.3′ |
| Transport of complete lists through $n\mapsto rn+s$ with exact counts; image-restricted genus-one premise | **Lean** (`affine_count`, `cubic_sound_image`, `n3m2_hits`) | — | `Transport.lean`, §5A |
| Exact constraint reductions (affine, quadratic discriminant, triangular), their composition, and transported completeness | **Lean** (`Reduction.Exact`, `Exact.comp`, `Exact.pull_complete`, `triangular_count`, `tri_cube_complete`) | — | `Reduction.lean`, §5B |
| Filtered Pell orbits: a divisibility filter from a reduction's way back leaves infinitely many solutions iff some root cycle mod $M$ meets an admissible state; otherwise a complete finite range | **Lean** (`FilteredPell.infinite_iff_root_state`, `quadRoot_infinite_iff`, `FinCert.sound`, `quadRoot_bound_of_cert`) | unit orbits (Lean) | `FilteredPell.lean`, §5B |
| Filtered Pell count $A(N)=\frac1{\log\varepsilon}\big(\sum_\rho g_\rho/P_\rho\big)\log N+O(1)$ over canonical roots, and a certificate for the constant | **Lean** (`FilteredPell.filtered_count`, `count_of_orbit_estimates`, `count_of_cert`, `quadRoot_count_of_cert`) | exact Pell count (Lean) | `FilteredCount.lean`, §5B |
| Compiler plans as theorems on the original constraint: 23 catalogued plans with 35 theorems (2 disguised Mordell curves with nonempty complete answers from a discovered descent; 7 transport chains; 5 infinite filtered plans with kernel-computed count constants, 4 with least solutions; 5 finite; a late family whose least solution $n=655680$ is proved; 2 Mordell-family members; one solution near $7.8\cdot10^{15}$) | **Lean** (`Generated/Plans.lean`, via `PlanCerts.power_transport`, `root_transport`, `quadRoot_subset_of_cert`, `FilteredPell.quadRoot_count_auto`, `quadRoot_isLeast`, `MordellFamily.no_points_cert`) | the rows above | `PlanCerts.lean`, §5B |
| Mordell's family $k=(4t-1)^3-4m^2$, $m$ free of primes $\equiv3\pmod4$: no integral point, for every member and every affine substitution | **Lean** (`MordellFamily.no_points`, `family_not_isHit`) | Mordell descent lemmas (Lean) | `MordellFamily.lean`, §5B |
| Descent certificates: under a kernel-checked table, `y^2 = x^3 - D` has exactly the points `(p^2 + D, p^3 - 3Dp)` with `3p^2 - D = ± 1`, and the list discharges `IntegralPointsOnImage` for every `m^2 = (rn + s)^3 - D` | **Lean** (`Descent.complete_of_cert`, `image_of_complete`, `hits_of_cert`) | `ClassTwo.short_relation` (Lean) | `Descent.lean`, `CONSTRAINT_COMPILER.md` §3F |
| Observations of filtered orbits: `#{v ≤ N} = (∑ g_ρ/(P_ρ log E_ρ)) log N + O(1)`; one orbit of `3 + √8` gives six sequences (Pell indices and roots, square triangular roots, values and odd values, triangular indices) with constants `1, 1, 1, 1, 1/2, 1/4` over `log(3 + 2√2)` | **Lean** (`Observation.observed_count`, `SquareTriangular.*_iff`, `*_count`) | exact Pell growth (Lean) | `Observation.lean`, `SquareTriangular.lean`, `OEIS.md` |
| Constraint compiler: plans, generated programs, timings | Python (tested against brute force, not verified); each plan cites its justification | the rows above | `CONSTRAINT_COMPILER.md`, §5B |
| Genus one: 622 monic cubics, Mordell census $0<\|k\|\le10^4$ | External (Sage; 485 census rows rest on an unproven rank) | — | `receipts/` |
| Genus ≥ 2 and quartic genus one outside Runge | Evidence (exact sieve to $10^8$) | — | `data/families.csv` |
| Transforms (Theorem T); log-periodic heat term (Theorem T2) | Paper; T2's $O(\tau)$ coefficient checked numerically | Mellin analysis (classical) | notes §8 |
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

**1. Arithmetic obstruction: curves with no integral points** (`MordellDescent.lean`). Let $k=c^3-Db^2$ with $D\in\{1,2,-2\}$. An integral point of $y^2=x^3+k$ gives
$$y^2+Db^2=(x+c)\,q,\qquad q=x^2-cx+c^2=\tfrac14\big((2x-c)^2+3c^2\big)\ge0.$$
Let $G_D$ be the residues mod 8 of the odd primes $p$ for which $-D$ is a square mod $p$: $\{1,5\}$, $\{1,3\}$ and $\{1,7\}$ respectively (Mathlib's supplementary laws). $G_D$ is closed under multiplication, so an odd $q$ with $q\bmod 8\notin G_D$ has a prime factor $p$ with $p\bmod 8\notin G_D$ (`exists_bad_prime`). The kernel evaluates every residue pair mod $M\in\{8,16,32\}$ and checks that the equation forces exactly this (`CongOK`). Such a $p$ divides $y^2+Db^2$, and $-D$ is not a square mod $p$, so $p\mid b$ (`good_of_dvd`). This is excluded by a certificate $b=2^jb_1$ with $b_1\mid u^2+D$ (`goodDivisors_of_cert`). The obstruction is arithmetic, not local: the curves have points modulo every integer. For $0<|k|\le10^4$ the search finds 1163 such $k$, 28 of them census rows whose Sage rank was unproved. For $D=3$ the mod-8 mechanism cannot work. $-3$ is a square modulo $p$ exactly when $p\equiv1\pmod3$, while $q\equiv(x+c)^2\pmod 3$ lies in $\{0,1\}$, so no congruence on $q$ can force a prime factor $\equiv2\pmod3$. (Such a prime may still divide $q$ when it divides $\gcd(x,c)$.) $D=-3$ is different and unexamined. The needed primes are $p\equiv\pm5\pmod{12}$, where $3$ is a non-residue, and a mod-12 version of the argument has not been attempted. An earlier edition wrongly stated that both signs fail.

**2. Reduction to a formalised theorem: a nonempty infinite family** (`MordellFLT3.lean`). On $y^2=x^3-432u^6$,
$$(36u^3+y)^3+(36u^3-y)^3=(6ux)^3,$$
so Mathlib's `fermatLastTheoremThree` forces a vanishing cube. This gives exactly the points $(12u^2,\pm36u^3)$.

**3. Positive rank: descent in a Euclidean quadratic ring** (`MordellMinus2.lean`, `MordellMinus4.lean`). $y^2=x^3-2$ and $y^2=x^3-4$ have rank one. There are infinitely many rational points, so no finite-group or congruence argument can close the list.
- *For $x^3-2$:* ℤ[√−2] is made Euclidean by integer rounding, and the remainder norm is at most $\tfrac34$ of the divisor's. By a congruence mod 4, $y$ is odd. The explicit Bézout identity $(-B-c\sqrt{-2})A+c\sqrt{-2}\,B=1$ with $A,B=y\pm\sqrt{-2}$ and $c=k^2+k+1$ proves coprimality. Mathlib's `exists_associated_pow_of_mul_eq_pow'` extracts a cube root, and the only units are $\pm1$. The $\sqrt{-2}$-coefficient gives $b(3a^2-2b^2)=1$, hence $(x,y)=(3,\pm5)$.
- *For $x^3-4$ in ℤ[i]:* every unit is a cube. When $y$ is odd, the argument gives $(5,\pm11)$. When $y$ is even, it passes through $y_1^2+1=2x_1^3$ and the factor $1+i$ to the Thue equation $(a-b)(a^2+4ab+b^2)=1$, giving $(2,\pm2)$.

These reprove in Lean 4 results that Baanen–Best–Coppola–Dahmen formalised in Lean 3 through class groups. For these two curves the route is elementary, because the rings are Euclidean.

**3′. Class number two, without ideals: a template** (`ClassTwo.lean`; instances `MordellMinus13.lean`, `MordellMinus5.lean`, `MordellMinus6.lean`). When ℤ[√−D] has class number 2, unique factorisation fails. The classical proof shows that the ideal $I$ with $I^3=(y+\sqrt{-D})$ is principal, because $3\nmid h$. `ClassTwo` makes each ingredient explicit *for every $D>0$*, in integer arithmetic. Write $\alpha=y+\sqrt{-D}$ and $x^3=y^2+D$.
- *The ideal $I$* is the lattice $\{(a,b): x\mid a-yb\}$ of index $x$.
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
$$A(N)=\#\{t\in T:\ r\mid t-s,\ 1\le (t-s)/r\le N\},$$
from the same hypothesis. For example, $(rn+s)^3-2$ is a square iff $rn+s=3$, so $A(N)\in\{0,1\}$ is decided by $r\mid 3-s$ and $1\le(3-s)/r\le N$ (`affine_cube_sub_two`).

The Weierstrass normalisation of `Genus1.lean` needs the same care. The old premise `IntegralPointsOn` asks for *every* integral point of the scaled model. A theorem about $m^2=F(n)$ only classifies the points in the image of $(n,m)\mapsto(9an+3b,\,27am)$. `IntegralPointsOnImage` asks only for those points (those with $9a\mid U-3b$ and $27a\mid V$), and `cubic_sound_image` proves the hit list from it. For $n^3-2$ the model is $V^2=U^3-1458$: `n3m2_image` discharges the image premise from `MordellMinus2.points`, and `n3m2_hits` recovers the unconditional list $\{3\}$ through the generic checker, without classifying the model's other integral points. The same distinction will be essential for quartic models, where the change of variables introduces denominators.

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
\cup\{\bot\}$ with $\mathrm{bwd}(\mathrm{fwd}\,a)=a$. The general theorems are:
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
  $y\in\mathbb Z$ or $y\ge0$. Hence `triangular_count`: $\#\{n\le N: F(n)\text{ triangular}\}=A_{8F}(2,1,N)$.

A square discriminant is not enough in general: $2y^2+y=1$ has discriminant $9$ but no root
$y\ge0$.

**3. Worked example, fully in Lean** (`tri_cube_complete`). With $n\ge1$ and $y\in\mathbb Z$,
$$\frac{y(y+1)}2=64n^3-120n^2+75n-16\iff (n,y)\in\{(1,2),(1,-3)\}.$$
The chain is: triangular, giving $m^2=(8n-5)^3-2$; then affine, $t=8n-5$; then `MordellMinus2.points`.
The pull-back of $\{(3,\pm5)\}$ is computed by `decide`. The compiler finds the same plan
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
$2a\mid sY-b$, where the admissible sign is $s=\operatorname{sign}a$ once the domain $y\ge L$
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

When ordinary density h exists, t K_X(t)→h. In general limsup_(t↓0)t K_X(t)≤H. Likewise (s−1)Z_X(s)→h along real s↓1 when density exists; this is an Abelian real-axis limit and does not assert meromorphic continuation. A T-periodic indicator admits the stronger residue-class expansion Z_X(s)=T^(−s)Σ_(r=1)^T X(r) ζ(s,r/T), and its meromorphic residue at s=1 equals P/T. The finite-window maximum sometimes called a tropical limit supplies none of these density claims. Cofinite-tail invariance is a basic property of limsup, not an independent Čech obstruction to arithmetic equality.

### 7. Formalization and research receipts

The Lean sources specify the hit predicate and elementary proofs. As of release 0.6 they compile against Lean and Mathlib `v4.20.0`: exact definitions, HasDensity⇒H, the bounded-count squeeze, the exact finite-surgery identity, periodic rationality, the rigid truncation, the integer-closure step, and the analytic finite-hit theorem are all `LEAN_VERIFIED`, and three files needed tactic repairs first (a source line containing neither `sorry` nor `axiom` could and did fail to elaborate). A verified numerical cutoff remains to be layered on. Boshernitzan's criterion belongs in a named external-assumption boundary until a formal statement and proof are imported. A Lean theorem must not be inferred from an exact Python certificate, nor a Python test from an uncompiled Lean term.

The τ monotonicity assertion should be a runtime property of actual manifests or a hypothesis of a rational-valued structure; it is false for a generic list, for example [1,0]. An uninterpreted proposition named an obstruction has no consequences until related to a mathematical construction. The old periodic zeta and heat statements are true with their hypotheses; heat density has a broader Abelian version. The tropical maximum and cofinite Čech statement are elementary observations. The BSD receipt should be replaced by the shifted-curve application of Siegel. The research ledger in this package distinguishes these theorem dependencies, executable checks, and open questions.

### 8. Program ahead

The most useful next proof problems concern rates and exceptional arithmetic inside H=0. For a given family, ask whether there is a local congruence obstruction, an exact parameterization, a Pell-type sparse infinite family, a genus-one finiteness theorem, or a determinant-method bound that genuinely fits the anisotropic x/y ranges. For polynomial perturbations, ask whether the rigid finite-hit cutoff can be made tight enough to enumerate all hits; for nonrigid polynomials, ask whether a specific exponential-sum estimate supplies an explicit sublinear rate beyond abstract equidistribution. For transforms, prove what a stated asymptotic A(N)∼cN^α(log N)^β actually implies about Z_X and K_X, and record the Tauberian hypotheses needed for converses. For software, keep exact hit semantics at the input boundary and let independent arithmetic formulas be the regression oracles.

### Sources and dependency boundary

Michael D. Boshernitzan, “Uniform distribution and Hardy fields,” *Journal d'Analyse Mathématique* 62 (1994), 225–240, DOI [10.1007/BF02835955](https://doi.org/10.1007/BF02835955). The precise theorem is restated as Theorem 1.1 in Michael Reilly, [“A criterion for weighted uniform distribution along functions from a Hardy field”](https://arxiv.org/abs/2606.08040) (2026). Joseph H. Silverman, [*The Arithmetic of Elliptic Curves*, Chapter IX](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf), proves the relevant finiteness theorem of Siegel and explains its non-effective aspect. E. Bombieri and J. Pila, [“The Number of Integral Points on Arcs and Ovals”](https://people.maths.ox.ac.uk/pila/Ovals.pdf), establishes integral-point estimates in specified boxes; no general α bound is silently imported from that paper here.
