# Perfect-Power Hits Beyond Density

## Exact definitions, a polynomial dichotomy, finite-hit certificates, and the arithmetic of the zero branch

## 0. Status of every result (edition 0.8)

This table is the single source of truth. The research notes, the paper, the README and the trust boundary state the same claims. Labels: **Lean** means compiled and axiom-audited (only `propext`, `Classical.choice`, `Quot.sound`). **Lean ⇐ H** means compiled, with a named hypothesis that is not proved. **Paper** means a written proof. **External** means a computation by third-party software (Sage, Singular). **Evidence** means exact within a stated bound and silent beyond it.

| Result | Status | Depends on | Where |
|---|---|---|---|
| Density 0–1 law, rigid branch | Lean (`rigid_zero_one`, `rigid_dichotomy`) | — | `ZeroOne.lean`, `Rigid.lean` |
| Density 0–1 law, nonrigid branch | Paper | Boshernitzan (external theorem) | §3 below |
| Power type: all hits, or finitely many | Lean (`atlas_power`, `power_type_finite`) | — | `Atlas.lean`, `RungeReduction.lean` |
| Radical type $A(N)=\kappa N^{1/t}+O(1)$, $\kappa=(R/v)(v/z_0)^{1/t}$ | Lean for $c(vn-u)^rG(n)^d$ (`radical_asymptotic_int`, `atlas_radical`); reduction of a general $F$ to that form: Paper | valuation core (Lean) | `RadicalAsymp.lean`; notes §3 |
| Pell type $A(N)=\kappa\log N+O(1)$, $\kappa=(\sum_\rho g_\rho/P_\rho)/\log\varepsilon$ | Lean for $An^2+Bn+C$ with a given unit (`pell_exact_count`, `atlas_pell`); reduction of a general $F$ (Theorem C): Paper | canonical orbit roots (Lean) | `PellExact.lean`; notes §4 |
| Finite type: finitely many hits | Lean ⇐ `SuperellipticSiegel` (`atlas_finite`) | Siegel (external) + geometric half of Theorem G (Paper) | `Atlas.lean`; notes §5 |
| Theorem G, combinatorial half ($\chi=d'(1-S)$; $\chi<0$ ⇔ non-exceptional) | Lean, all $d$ (`chi_eq`, `chi_neg_iff`); Riemann–Hurwitz integrality table for $d,\deg F\le12$ (`profile_table_ok`) | — | `ProfileG.lean` |
| Theorem G, geometric half (Kummer, Riemann–Hurwitz) | Paper; External check (Singular genus, Sage places at infinity) over the range stated in `receipts/theorem_g_check.json` | — | notes §5 |
| Runge enumeration, rigid branch | Paper (Theorem R); 19 instances Lean via pp-cert/1 (`check_sound`, `rungeCheck_sound`) | — | `Reflect.lean`, `CERTIFICATE_FORMAT.md` |
| Genus one: 399 non-monic/shifted families, 2 binomials | Lean ⇐ named Sage point lists (`Genus1.lean`, `Binomial.lean`) | Sage `integral_points` (External) | `Generated/Genus1.lean` |
| Genus one, unconditional: 1163 Mordell curves $y^2=x^3+k$, $0<|k|\le10^4$, with **no** integral points | **Lean** (elementary descent `MordellDescent.lean`; no hypothesis) | agrees with the Sage census, 0 conflicts | `Generated/MordellDescent.lean` |
| Genus one, unconditional and **nonempty**: $y^2=x^3-432u^6$ has exactly the integral points $(12u^2,\pm36u^3)$ for every $u\ne0$; so $n^3-432u^6=m^2$ iff $n=12u^2$ | **Lean** (`MordellFLT3.lean`, from Mathlib's `fermatLastTheoremThree`) | classical (the Fermat cubic) | `MordellFLT3.isHit_iff` |
| Genus one, unconditional, **positive rank**: $y^2=x^3-2$ (points $(3,\pm5)$), $y^2=x^3-4$ (points $(2,\pm2),(5,\pm11)$) | **Lean** (`MordellMinus2.lean`, `MordellMinus4.lean`; descent in ℤ[√−2], ℤ[i]) | Mathlib (Euclidean ℤ[i]; ours for ℤ[√−2]) | §5A |
| Transport of complete lists through $n\mapsto rn+s$ with exact counts; image-restricted genus-one premise | **Lean** (`affine_count`, `cubic_sound_image`, `n3m2_hits`) | — | `Transport.lean`, §5A |
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
- Theorems B, C (paper reductions) ⟶ general $F$ in the radical and Pell types.
- Atlas = power ∪ radical ∪ Pell ∪ finite.
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
Let $G_D$ be the residues mod 8 of the odd primes $p$ for which $-D$ is a square mod $p$: $\{1,5\}$, $\{1,3\}$ and $\{1,7\}$ respectively (Mathlib's supplementary laws). $G_D$ is closed under multiplication, so an odd $q$ with $q\bmod 8\notin G_D$ has a prime factor $p$ with $p\bmod 8\notin G_D$ (`exists_bad_prime`). The kernel evaluates every residue pair mod $M\in\{8,16,32\}$ and checks that the equation forces exactly this (`CongOK`). Such a $p$ divides $y^2+Db^2$, and $-D$ is not a square mod $p$, so $p\mid b$ (`good_of_dvd`). This is excluded by a certificate $b=2^jb_1$ with $b_1\mid u^2+D$ (`goodDivisors_of_cert`). The obstruction is arithmetic, not local: the curves have points modulo every integer. For $0<|k|\le10^4$ the search finds 1163 such $k$, 28 of them census rows whose Sage rank was unproved. For $D=\pm3$ the method fails structurally: every prime factor of $q$ is $3$ or $\equiv1\pmod 3$, so $-3$ is a quadratic residue modulo it.

**2. Reduction to a formalised theorem: a nonempty infinite family** (`MordellFLT3.lean`). On $y^2=x^3-432u^6$,
$$(36u^3+y)^3+(36u^3-y)^3=(6ux)^3,$$
so Mathlib's `fermatLastTheoremThree` forces a vanishing cube. This gives exactly the points $(12u^2,\pm36u^3)$.

**3. Positive rank: descent in a Euclidean quadratic ring** (`MordellMinus2.lean`, `MordellMinus4.lean`). $y^2=x^3-2$ and $y^2=x^3-4$ have rank one. There are infinitely many rational points, so no finite-group or congruence argument can close the list.
- *For $x^3-2$:* ℤ[√−2] is made Euclidean by integer rounding, and the remainder norm is at most $\tfrac34$ of the divisor's. By a congruence mod 4, $y$ is odd. The explicit Bézout identity $(-B-c\sqrt{-2})A+c\sqrt{-2}\,B=1$ with $A,B=y\pm\sqrt{-2}$ and $c=k^2+k+1$ proves coprimality. Mathlib's `exists_associated_pow_of_mul_eq_pow'` extracts a cube root, and the only units are $\pm1$. The $\sqrt{-2}$-coefficient gives $b(3a^2-2b^2)=1$, hence $(x,y)=(3,\pm5)$.
- *For $x^3-4$ in ℤ[i]:* every unit is a cube. When $y$ is odd, the argument gives $(5,\pm11)$. When $y$ is even, it passes through $y_1^2+1=2x_1^3$ and the factor $1+i$ to the Thue equation $(a-b)(a^2+4ab+b^2)=1$, giving $(2,\pm2)$.

These reprove in Lean 4 results that Baanen–Best–Coppola–Dahmen formalised in Lean 3 through class groups. The route here is elementary and applies only in class number one. $y^2=x^3-13$ (class number 2) is the next target and needs their class-group computation.

**4. Transport with integrality** (`Transport.lean`). Suppose a complete list is $\mathrm{CompleteArgs}(G,d,T)$: $G(t)$ is a $d$-th power iff $t\in T$, for every *integer* $t$. For $r\ne0$, the family $n\mapsto G(rn+s)$ then has hits exactly at $rn+s\in T$. By `affine_count`, the count is
$$A(N)=\#\{t\in T:\ r\mid t-s,\ 1\le (t-s)/r\le N\},$$
from the same hypothesis. For example, $(rn+s)^3-2$ is a square iff $rn+s=3$, so $A(N)\in\{0,1\}$ is decided by $r\mid 3-s$ and $1\le(3-s)/r\le N$ (`affine_cube_sub_two`).

The Weierstrass normalisation of `Genus1.lean` needs the same care. The old premise `IntegralPointsOn` asks for *every* integral point of the scaled model. A theorem about $m^2=F(n)$ only classifies the points in the image of $(n,m)\mapsto(9an+3b,\,27am)$. `IntegralPointsOnImage` asks only for those points (those with $9a\mid U-3b$ and $27a\mid V$), and `cubic_sound_image` proves the hit list from it. For $n^3-2$ the model is $V^2=U^3-1458$: `n3m2_image` discharges the image premise from `MordellMinus2.points`, and `n3m2_hits` recovers the unconditional list $\{3\}$ through the generic checker, without classifying the model's other integral points. The same distinction will be essential for quartic models, where the change of variables introduces denominators.

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
