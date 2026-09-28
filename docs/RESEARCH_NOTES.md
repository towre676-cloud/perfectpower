# Beyond the 0–1 law: the exponent spectrum of polynomial perfect-power hits

**Research notes for release 0.6 (28 September 2026).** These notes extend [the monograph](MONOGRAPH.md). Notation is unchanged: for $F\in\mathbb Z[x]$ and $d\ge 2$, a *hit* is an index $n\ge 1$ with $F(n)=m^d$ for some $m\in\mathbb Z$, and $A(N)=\#\{1\le n\le N: n \text{ is a hit}\}$. The shift $k$ of the monograph is absorbed into $F=S+k$ except in §7.

Every result below carries one of the status labels of [the receipt policy](RECEIPTS.md). In summary:

| Result | Status | Where |
|---|---|---|
| Theorem P (power type) | `LEAN_VERIFIED`: density one is `hasDensity_one_of_pow`; finiteness is `power_type_finite` | §2, `PerfectPower/ZeroOne.lean` |
| Theorem B (radical type, exact parametrisation) | `PAPER_PROOF` + `EXACT_COMPUTATION` cross-check. `LEAN_VERIFIED`: the monomial case (`monomial_count`) and the valuation core for general $c$ (`isHit_iff_natAbs` sign condition, `isHit_iff_rat` denominator step, `mul_pow_isPow_iff_congr`, `mul_pow_isPow_iff_param`: $z=z_0w^t$) and the count (`radical_count_bound`: $|vA(N)-RW|\le2Rv$); only $W\sim(v/z_0)^{1/t}N^{1/t}$ is left informal | §3, `atlas.py`, `PerfectPower/Monomial.lean` |
| Lemma Q, Theorem C (Pell type) | `PAPER_PROOF` + `EXACT_COMPUTATION` cross-check; for $2n^2+1$, infinitude and density zero are `LEAN_VERIFIED` (`pell_hasDensity_zero`). In general, `LEAN_VERIFIED`: the norm-equation reduction, pure periodicity modulo $2A$, good classes, finitely many orbit representatives (`pell_orbits_exhaust`), geometric counting, and $A(N)=O(\log N)$ (`pell_count_log`); the exact constant $\kappa$ is not | §4, `atlas.py`, `PerfectPower/Pell.lean` |
| Theorem A (atlas) and Corollary A (exponent spectrum) | `THEOREM_EXTERNAL_DEPENDENCY` on Siegel's theorem (standard form) via Theorem G; LeVeque 1964 kept as historical context | §5 |
| Theorem G ($\chi=d'(1-S)$; finite type ⇔ $\chi<0$) | Geometric half (Kummer, Riemann–Hurwitz): `PAPER_PROOF` (not refereed), checked against Sage normalisation for $d\le12$, $\deg F\le12$ (`receipts/theorem_g_check.json`). Combinatorial half: `LEAN_VERIFIED` (`S_le_one_iff`, `profile_table_ok`) | §5, `PerfectPower/ProfileG.lean` |
| Function-field Pillai ($\deg(f^a-g^b)$ bound) | `LEAN_VERIFIED` (`pillai_polynomial`, `pillai_polynomial_balanced`), unconditional | `PerfectPower/Davenport.lean` |
| Genus-one hit lists (non-monic/shifted cubics, $m^3=$ quadratic) | `EXTERNAL_COMPUTATION` (Sage), re-verified in plain Python | `receipts/genus1_crossval.json` |
| Theorem R (complete Runge enumeration) | `PAPER_PROOF`; the reduction to the $G_t$ is `LEAN_VERIFIED` (`runge_finite`); 19 instances have generated Lean certificates (17 by Taylor-shift plans, 2 by interval sandwiches); adversarial planted-hit test, 220 trials, 0 failures; prior art (Walsh 1992, Beukers–Tengely 2005) not yet compared | §6, `runge.py`, `lean_emit.py`, `lean_sandwich.py` |
| Rigid-branch 0–1 law | `LEAN_VERIFIED` (`rigid_zero_one`) | §6 |
| Corollary K (shift spectrum) | `THEOREM_EXTERNAL_DEPENDENCY` (Siegel, via Theorem G) | §7 |
| Schäffer's sums-of-powers list, recovered with constants | `THEOREM_EXTERNAL_DEPENDENCY` (Siegel, via Theorem G) + `EXACT_COMPUTATION` | §7 |
| Theorem T (transforms) | `PAPER_PROOF` | §8 |
| Theorem T2 (log-periodic second term, Pell type) | `PAPER_PROOF` (corrected: shift $\beta=-B/2A$; two-term remainder $O(\tau\log(1/\tau))$ if $B\ne0$) + numerical check of residual/scale | §8, `pell_heat.py` |
| Theorem E (exponential sequences) | `PAPER_PROOF` + `EXACT_COMPUTATION`; the $d$-periodicity and rational density $P/d$ are `LEAN_VERIFIED` (`exp_hasDensity`, `two_pow_hasDensity_half`) | §9, `exponential.py`, `PerfectPower/Exponential.lean` |

## 1. Summary

The monograph proves that the hit density of $F(n)$ is $1$ if $F=G^d$ with $G\in\mathbb Z[x]$ and $0$ otherwise, and asks for finer information inside the zero-density branch: rates, exponents, exact counts, and effective enumeration. These notes answer the rate question for polynomials, conditionally on Siegel's theorem on integral points (standard form), which is ineffective. The reduction to Siegel is Theorem G, a paper proof in these notes that has not been independently refereed.

**Positioning.** The atlas and the exponent spectrum below are a *synthesis*: Siegel's theorem (through the Euler-characteristic computation of Theorem G, which recovers LeVeque's 1964 exceptional patterns) combined with classical Pell and valuation counting, made explicit (with constants) and decidable (by an implementation). We make no priority claim for them until a literature pass, which must cover in particular the Bilu–Tichy and Schinzel–Tijdeman lineages, shows the packaging is new. The parts with a chance of being new are the certified pipeline: the rigid-branch enumerator, which must still be compared with the Runge implementations of Walsh and of Beukers–Tengely, and the Lean certificate emitter. See [RELATED_WORK.md](RELATED_WORK.md) and [TRUST_BOUNDARY.md](TRUST_BOUNDARY.md). LeVeque's theorem is no longer an input: it was only ever available to us in secondary sources, and Theorem G replaces it by a direct argument from Siegel.

Write $F=c\prod_i(x-\alpha_i)^{r_i}$ over $\overline{\mathbb Q}$ with distinct $\alpha_i$, and put $t_i=d/\gcd(d,r_i)$. Call the multiset $\{t_i\}$ the *$t$-profile* of $(F,d)$. It is computable exactly from a squarefree decomposition, without factoring $F$.

**Theorem A (atlas).** Let $F\in\mathbb Z[x]$ be nonconstant and $d\ge2$. Exactly one of the following holds.

1. **Power type** (all $t_i=1$). Then $F=cG^d$ with $G\in\mathbb Q[x]$ monic. If $c$ is an integer $d$-th power, then $F$ is the $d$-th power of an integer polynomial and $A(N)=N$. Otherwise the hits are exactly the positive integer roots of $F$.
2. **Radical type** ($t$-profile $\{t,1,\dots,1\}$, $t\ge2$). There is an explicit $\kappa\ge0$ with $A(N)=\kappa N^{1/t}+O(1)$; $\kappa$ is computed from one congruence count (Theorem B).
3. **Pell type** ($t$-profile $\{2,2,1,\dots,1\}$, so $d$ is even). There is an explicit $\kappa\ge0$ with $A(N)=\kappa\log N+O(1)$; $\kappa$ is computed from Pell orbits modulo $2A$ (Theorem C).
4. **Finite type** (every other profile). The hit set is finite.

Parts 1–3 are elementary and are proved here. Part 4 follows from Siegel's theorem by Theorem G (§5).

**Corollary A (exponent spectrum and the root barrier).** Let $\alpha(F,d)=\limsup_N \log(1+A(N))/\log N$. Then
$$\alpha(F,d)\in\{0,1\}\cup\{1/t:\ t\mid d,\ t\ge2\},$$
and every value in this set occurs. Moreover $\alpha=1$ exactly when $F$ is an integer-polynomial $d$-th power. Otherwise $A(N)=O(N^{1/p})$, where $p$ is the least prime factor of $d$. In particular $A(N)=O(N^{1/2})$ for every non-power $F$, and $A(N)=O(N^{1/3})$ when $d$ is odd. All these bounds are sharp.

*Proof of the corollary from Theorem A.* In the radical type $t=d/\gcd(d,r)$ divides $d$ and exceeds $1$, so $t\ge p$. The Pell and finite types have $\alpha=0$. The monomial $F=x^{r}$ with $\gcd(r,d)=d/t$ has hits exactly at the $t$-th powers, so $A(N)=\lfloor N^{1/t}\rfloor$ realises $1/t$. This is Theorem B, and it is also the compiled Lean theorem `monomial_count`. For sharpness take $r=d/p$. $\square$

This refines the monograph's 0–1 law in two ways, both conditional on Siegel's theorem through Theorem G.

1. The zero branch has a quantitative ceiling, $N^{1/2}$, instead of $o(N)$.
2. There is a second proof of density zero that does not use Boshernitzan's equidistribution theorem. It rests on Siegel's theorem through Theorem G, however, so it is **ineffective**. It cannot replace the Boshernitzan argument, or any argument, where effectivity matters. The two proofs are logically independent, but neither gives computable bounds in the finite type.

## 2. The power type

**Theorem P.** Suppose every root of $F$ has multiplicity divisible by $d$, so $F=cG^d$ with $G=\prod_j S_j^{j/d}\in\mathbb Q[x]$ monic ($S_j$ the squarefree parts). Here $c=\operatorname{lc}(F)\in\mathbb Z$.

1. If $c=b^d$ with $b\in\mathbb Z$, then $bG\in\mathbb Z[x]$, $F=(bG)^d$, and every $n$ is a hit.
2. Otherwise $n\ge1$ is a hit if and only if $F(n)=0$. There are at most $\deg G$ hits.

*Proof.* (1) $(bG)^d=F\in\mathbb Z[x]$, and $\mathbb Z[x]$ is integrally closed in $\mathbb Q[x]$ by Gauss's lemma, so $bG\in\mathbb Z[x]$. This step is `integral_closure_step` in the Lean kernel. (2) If $G(n)\ne0$ and $F(n)=m^d$, then $c=(m/G(n))^d$ is the $d$-th power of a rational number. A rational number whose $d$-th power is an integer is itself an integer, so $c$ is an integer $d$-th power, a contradiction. If $G(n)=0$ then $F(n)=0=0^d$. $\square$

The Lean theorem `twisted_hits_subset` proves (2) in the form: if $D^dF=cH^d$ in $\mathbb Z[x]$ and $c$ is not an integer $d$-th power, then every hit is a root of $H$. `twisted_finite` and `twisted_density_zero` follow. Examples are $2n^2$ with $d=2$ (no hits), $F=4n^2+4n+1$ with $d=2$ (all hits), and the next example.

**Remark (local–global failure, Grunwald–Wang).** Take $F=16x^8$ and $d=8$. For every odd prime $p$, $16$ is an $8$-th power modulo $p$; the receipt checks this for all $p<2\cdot10^4$, and it is the classical Grunwald–Wang phenomenon. Hence $F(n)$ is an $8$-th power residue modulo every prime, for every $n$, yet Theorem P says $F$ has no hits at all. Consequently, any attempt to prove density zero by sieving with residues modulo *primes* must fail in general. The obstruction here lives modulo $32$: for odd $n$, $16n^8\equiv16$, while $8$-th powers are $0$ or $1$ modulo $32$. The atlas makes such local considerations unnecessary.

## 3. The radical type

Suppose exactly one root $\alpha$ has $t=d/\gcd(d,r)\ge2$, where $r$ is its multiplicity. Galois conjugate roots of $F\in\mathbb Q[x]$ have equal multiplicities. So the unique special root is fixed by $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and is rational, $\alpha=u/v$ with $v\ge1$, $\gcd(u,v)=1$. The remaining roots have multiplicities divisible by $d$, and
$$F=c\,(x-\alpha)^r\,G(x)^d,\qquad c=\operatorname{lc}(F),\ G\in\mathbb Q[x]\text{ monic}.$$

Put $K=\lceil r/d\rceil$ and $c_1=c\,v^{dK-r}\in\mathbb Z$. Let $g=\gcd(r,d)$, $t=d/g$, and $r'=r/g$. If $g$ divides $v_p(c_1)$ for every prime $p$, define
$$\tau_p\equiv-\tfrac{v_p(c_1)}{g}\,(r')^{-1}\pmod t,\quad 0\le\tau_p<t,\qquad z_0=\prod_p p^{\tau_p}.$$
The admissible signs are all $\sigma\in\{\pm1\}$ when $d$ is odd, and only $\sigma$ with $c_1\sigma^r>0$ when $d$ is even.

**Theorem B.** In the radical type, $n\ge1$ is a hit if and only if either $F(n)=0$, or $g\mid v_p(c_1)$ for all $p$ and
$$vn-u=\sigma z_0 w^t\quad\text{for an admissible sign }\sigma\text{ and an integer }w\ge1 .$$
Let $\varrho$ be the number of residues $w \bmod v$ with $z_0w^t+u\equiv0\pmod v$. If $\sigma=+1$ is admissible and the divisibility condition holds, then
$$A(N)=\kappa N^{1/t}+O(1),\qquad \kappa=\frac{\varrho}{v}\Big(\frac{v}{z_0}\Big)^{1/t}.$$
Otherwise $A(N)=O(1)$. In particular $\alpha(F,d)\in\{0,1/t\}$.

*Proof.* Let $n\ge1$ with $F(n)\ne0$, so $G(n)\ne0$ and $n\ne\alpha$. Then $F(n)=m^d$ with $m\in\mathbb Z$ if and only if $c(n-\alpha)^r$ is the $d$-th power of a rational number. One direction divides by $G(n)^d$. For the other, $F(n)=(\xi G(n))^d$ is an integer and a rational $d$-th power, hence an integer $d$-th power. With $z=vn-u\neq0$ we have $c(n-\alpha)^r=c z^r v^{-r}$. Multiplying by the $d$-th power $v^{dK}$ gives the equivalent condition that the *integer* $c_1z^r$ is a $d$-th power in $\mathbb Q$, hence in $\mathbb Z$.

An integer $X\ne0$ is a $d$-th power if and only if $d\mid v_p(X)$ for all $p$ and, when $d$ is even, $X>0$. For $X=c_1z^r$ the valuation condition reads $v_p(c_1)+r\,v_p(z)\equiv0\pmod d$. This is solvable only if $g\mid v_p(c_1)$, and then it is equivalent to $v_p(z)\equiv\tau_p\pmod t$. The positive integers whose valuations satisfy these congruences are exactly $z_0w^t$ with $w\ge1$, since $v_p(z_0w^t)=\tau_p+t\,v_p(w)$. This proves the characterisation.

For the count with $\sigma=+1$, the hits are $n=(z_0w^t+u)/v$ with $w$ in one of the $\varrho$ good residue classes modulo $v$ and $z_0w^t\le vN-u$. That gives $\varrho\,v^{-1}((vN-u)/z_0)^{1/t}+O(\varrho)$ values, and $(vN-u)^{1/t}=(vN)^{1/t}+O(1)$. The sign $\sigma=-1$ forces $n<\alpha$ and contributes finitely many hits. So do the roots of $F$. $\square$

*Examples* (all cross-checked in `receipts/atlas_benchmarks.json`):

- $4n+1$ with $d=2$: $\alpha=-\tfrac14$, $c_1=16$, $z_0=1$, $\varrho=2$ (namely $w\equiv1,3$), so $\kappa=\tfrac24\cdot2=1$. This recovers the monograph's $\sqrt N$.
- $2n-5$ with $d=2$: $\kappa=2^{-1/2}$.
- $3n+5$ with $d=3$: cubes $\equiv2 \pmod 3$ give $\kappa\approx0.4807$.
- $3n+2$ with $d=6$: $\varrho=0$, no hits.
- $12n^2$ with $d=3$: $c_1=12$, $\tau_2=2$, $\tau_3=1$, $z_0=12$, so the hits are $n=12w^3$ and $\kappa=12^{-1/3}\approx0.4368$.
- $16n^3$ with $d=6$: $g=3\nmid v_2(16)=4$, so there are no hits.

The monograph's linear formula $A(N)\sim R\,a^{1/d-1}N^{1/d}$ for $an+c$ is the special case $t=d$.

**Proposition (Dirichlet series in the radical type).** If $u=0$ (the special root is $0$) and $G$ has no positive integer roots, then $Z_X(s)=\sum_{w\ge1}(z_0w^t)^{-s}=z_0^{-s}\zeta(ts)$ up to a Dirichlet polynomial. In general $Z_X$ is a finite sum over good classes $w\equiv\rho \pmod v$ of $\sum_k\big((z_0(\rho+vk)^t+u)/v\big)^{-s}$. Expanding $(1+u/(z_0w^t))^{-s}$ binomially for large $w$ writes this as a locally uniformly convergent series of Hurwitz zeta functions $\zeta\big(t(s+j),\rho/v\big)$. Hence $Z_X$ continues meromorphically to $\mathbb C$, with at most simple poles in $\{1/t-j:j\ge0\}$ and residue $\kappa/t$ at $s=1/t$.

## 4. The Pell type

Suppose exactly two roots have $t\ne1$ and both have $t=2$. Then $d=2e$, and each special multiplicity $r$ satisfies $\gcd(r,d)=e$, so $r$ is an odd multiple of $e$ and $(x-\alpha)^r=(x-\alpha)^e\cdot(x-\alpha)^{r-e}$ with $d\mid r-e$. The two special roots form a Galois-stable set, so they are both rational or a conjugate pair. Their monic product $W$ lies in $\mathbb Q[x]$, has distinct roots, and
$$F=c\,W^e H^d,\qquad H\in\mathbb Q[x]\text{ monic}.$$

**Theorem C (reduction).** Let $\Gamma=\{\gamma\in\mathbb Q:\gamma^e=c\}$, which has at most two elements. For $\gamma=\gamma_1/\gamma_2\in\Gamma$ in lowest terms, and $L$ the least common denominator of $W$, put $P_\gamma(x)=\gamma_1\gamma_2L\cdot(L\,W(x))\in\mathbb Z[x]$. Then $n\ge1$ is a hit if and only if $F(n)=0$ or $P_\gamma(n)$ is a perfect square for some $\gamma\in\Gamma$. Each $P_\gamma$ is a quadratic with nonzero discriminant.

*Proof.* As in Theorem B, when $F(n)\ne0$, $n$ is a hit if and only if $cW(n)^e=y^{2e}$ for some $y\in\mathbb Q^\times$. Put $w=W(n)\ne0$ and $\gamma=y^2/w$. Then $\gamma^e=c$, so $\gamma\in\Gamma$ and $\gamma w=y^2$. Conversely, $\gamma w=y^2$ with $\gamma^e=c$ gives $cw^e=y^{2e}$. Finally $\gamma W(n)$ is a rational square if and only if $(\gamma_2L)^2\gamma W(n)=P_\gamma(n)$ is. Since $P_\gamma(n)$ is an integer, that means a perfect square. $\square$

**Lemma Q (square values of a quadratic).** Let $P=An^2+Bn+C\in\mathbb Z[x]$ with $A\ne0$ and $\Delta=B^2-4AC\ne0$, and let $S=\{n\ge1: P(n)=m^2\}$.

1. If $A<0$, then $S$ is finite, contained in $n\le(\sqrt\Delta+|B|)/(2|A|)$.
2. If $A=s^2$, then $S$ is finite. Each hit gives a factorisation $(X-2sm)(X+2sm)=\Delta$ with $X=2An+B$, so $\#S\le 2\tau(|\Delta|)$.
3. If $A>0$ is not a square, let $\varepsilon=x_1+y_1\sqrt{4A}$ be the fundamental solution of $x^2-4Ay^2=1$. The solutions of $X^2-4AY^2=\Delta$ with $\eta=X+Y\sqrt{4A}>0$ fall into finitely many orbits $\mathcal O$ under multiplication by $\varepsilon$. Along each orbit the pair $(X,Y) \bmod 2A$ is purely periodic, with some period $\pi_{\mathcal O}$. Let $g_{\mathcal O}$ be the number of steps in one period with $X\equiv B\pmod{2A}$. Then
$$\#(S\cap[1,N])=\kappa\log N+O(1),\qquad \kappa=\frac1{\log\varepsilon}\sum_{\mathcal O}\frac{g_{\mathcal O}}{\pi_{\mathcal O}} .$$

*Proof.* We have $4A\,P(n)=X^2-\Delta$ with $X=2An+B$, and $n\mapsto X$ is a bijection onto $X\equiv B\pmod{2A}$. So $P(n)=m^2$ with $m\ge0$ if and only if $X^2-4Am^2=\Delta$. Parts 1 and 2 are immediate.

For part 3, the solutions form finitely many classes (Nagell). The code computes class representatives with the Lagrange–Matthews–Mollin algorithm and checks them against Nagell's bounded search. For large $n$ we have $m>0$, so $\eta=X+m\sqrt{4A}$ is large and positive. Distinct $n$ give distinct $X$, and for each large hit exactly one of $X\pm m\sqrt{4A}$ exceeds $1$. So large hits correspond bijectively to large elements $\eta=\eta_0\varepsilon^k$ of the positive orbits with $X\equiv B\pmod{2A}$.

Along an orbit, $(X_{k+1},Y_{k+1})=(x_1X_k+4Ay_1Y_k,\;y_1X_k+x_1Y_k)$. This matrix has determinant $1$, so it is invertible modulo $2A$ and the residues are purely periodic. Also $\log X_k=k\log\varepsilon+\log(\eta_0/2)+o(1)$. The good $k$ with $X_k\le 2AN+B$ therefore number $(g/\pi)\log N/\log\varepsilon+O(1)$ per orbit. $\square$

*Examples.* For $2n^2+1$, $\kappa=1/\log(3+2\sqrt2)=0.567296\ldots$. The exact counts at $N=10^6,10^{12},10^{24},10^{48}$ are $8,16,31,63$, against $\kappa\log N=7.84,15.67,31.35,62.70$. The other receipt values are $\kappa=0.75933$ for $3n^2+1$, $1.13459$ for $2n^2-7$, $0.34635$ for $5n^2+n+3$, and $0.28365$ for $2n^2+n$. The quartic $(2n^2+1)^2$ with $d=4$ reduces via Theorem C to $2n^2+1=\pm m^2$ and gives the same counts as $2n^2+1$ with $d=2$. For $n^2+n$ we have $A=1$, a square, so there are no hits.

**Formal status.** For $2n^2+1$ the descent step behind Lemma Q(3), infinitude, the bound $A(N)\le\sqrt N$ and density zero are compiled Lean theorems (`PerfectPower/Pell.lean`). The logarithmic asymptotic itself is not yet formalised.

**Corollary.** In the Pell type, $\alpha(F,d)=0$. The hit set is either finite or of exact logarithmic order $\kappa\log N$ with $\kappa>0$. This is the "Pell exception" to the heuristic that infinitely many hits force a positive exponent; the monograph observed it for $2n^2+1$, and here it is characterised.

## 5. The atlas theorem

The finite type (part 4) no longer needs LeVeque's theorem as a black box. It follows from the standard form of Siegel's theorem by the Euler-characteristic computation below (Theorem G). LeVeque's theorem (Acta Arith. 9 (1964) 209–219), which is the historical source of the exceptional patterns, is retained as context only; its primary text was not accessible in the build environment. Brindza (Acta Math. Hungar. 44 (1984)) made the finiteness effective via Baker's method, with astronomically large bounds.

**Siegel's theorem (standard form).** Let $C$ be an affine curve over a number field $K$, irreducible over $\overline K$. Let $\tilde C$ be the smooth projective model of $C$, of genus $g_C$, and let $n_\infty$ be the number of points of $\tilde C(\overline K)$ lying over the complement of $C$. If $2g_C-2+n_\infty>0$, then for every finite set $S$ of places, $C$ has only finitely many $S$-integral points. In words: every affine curve other than $\mathbb P^1$ minus at most two points has finitely many $S$-integral points. References: Siegel (1929), Mahler (S-integers); Hindry–Silverman, *Diophantine Geometry*, Theorem D.9.1; Bombieri–Gubler, *Heights in Diophantine Geometry*, §7.3.

**Theorem G (geometry of $y^d=F(x)$).** Let $F=c\prod_{i=1}^s(x-\alpha_i)^{r_i}$ with distinct $\alpha_i\in\overline{\mathbb Q}$ and $d\ge2$. Put $g=\gcd(d,r_1,\dots,r_s)$, $d'=d/g$, $t_i=d/\gcd(d,r_i)$ and $S=\sum_i(1-1/t_i)$.

1. Over $\overline{\mathbb Q}$, the curve $y^d=F(x)$ is the union of $g$ irreducible components $y^{d'}=\zeta c^{1/g}\prod(x-\alpha_i)^{r_i/g}$, one for each $g$-th root of unity $\zeta$.
2. Each component, after normalisation, is a cyclic cover of $\mathbb P^1_x$ of degree $d'$. It has:
   - $d'/t_i$ points over $\alpha_i$;
   - $n_\infty=\gcd(d',\deg F/g)$ points over $x=\infty$;
   - $d'$ points over every other $x$ (the cover is unramified there).
3. Hence the affine part of each component has Euler characteristic
$$\chi \;=\; 2-2g_C-n_\infty \;=\; d'\,(1-S).$$
4. In particular, $y^d=F(x)$ has finitely many integral points whenever $S>1$. And $S\le1$ holds exactly for the $t$-profiles $\{1,\dots,1\}$ (power), $\{t,1,\dots,1\}$ (radical) and $\{2,2,1,\dots,1\}$ (Pell).

*Proof.* (1) We have $Y^d-F=\prod_\zeta\bigl(Y^{d'}-\zeta c^{1/g}\prod(x-\alpha_i)^{r_i/g}\bigr)$. Each factor is irreducible over $\overline{\mathbb Q}(x)$ by Capelli's theorem: the exponents $r_i/g$ have $\gcd(d',r_1/g,\dots,r_s/g)=1$, so the right-hand side is not a $p$-th power in $\overline{\mathbb Q}(x)$ for any prime $p\mid d'$. Over an algebraically closed field, Capelli's extra condition $-4w^4$ is subsumed.

(2) Kummer theory for the cyclic extension $\overline{\mathbb Q}(x)(y)/\overline{\mathbb Q}(x)$ of degree $d'$. At a place where $y^{d'}$ has valuation $v$, the ramification index is $d'/\gcd(d',v)$, and there are $\gcd(d',v)$ places above it. At $x=\alpha_i$ the valuation is $v=r_i/g$, and $d'/\gcd(d',r_i/g)=d/\gcd(d,r_i)=t_i$. At $x=\infty$ the valuation is $-\deg F/g$. Everywhere else the extension is unramified.

(3) Riemann–Hurwitz for the degree-$d'$ map to $\mathbb P^1$ gives
$$2g_C-2=d'(-2)+\sum_i(d'-d'/t_i)+(d'-n_\infty),$$
which rearranges to $2-2g_C-n_\infty=d'(1-S)$.

(4) An affine curve other than $\mathbb P^1$ minus at most two points has $\chi<0$; conversely $\chi<0$ is exactly Siegel's condition $2g_C-2+n_\infty>0$. If $S>1$, apply Siegel over a number field $K$ containing $c^{1/g}$, the $\alpha_i$ and the $g$-th roots of unity, to each component $C_j$, using its normalisation $\tilde C_j$. There are three technical points:

- *Singular points.* An integral point of $C_j$ that is not one of its finitely many singular points lifts uniquely to $\tilde C_j$.
- *Integrality after normalisation.* The affine part of $\tilde C_j$ is $\tilde C_j$ minus the $n_\infty$ points over $x=\infty$. Its coordinate ring is the integral closure of $K[x]$ in the function field, and it is generated by finitely many functions $w_\ell$, each integral over $K[x]$. Multiplying by a fixed integer $N$ makes each $Nw_\ell$ integral over $\mathcal O_K[x]$. So at a point with $x\in\mathbb Z$ every $w_\ell$ takes values in $N^{-1}\mathcal O_K$. These points are $S$-integral for $S$ containing the primes dividing $N$, and Siegel applies.
- *Fields of definition.* Every rational integral point lies on some $C_j$, and there are finitely many components.

So there are finitely many integral points when $S>1$. Finally, each special root contributes $1-1/t_i\ge\tfrac12$ to $S$. Hence $S\le1$ allows either one special root with any $t$ (radical type), or two special roots with $t=2$ each (Pell type, $S=1$), or none (power type). $\square$

*Corollary (Theorem A, part 4, now from Siegel).* Profiles outside the power, radical and Pell types have $S>1$, hence finitely many hits. The classification in Theorem A therefore rests on Siegel's theorem in the standard form above. That form is stated with proof in textbooks (Hindry–Silverman; Bombieri–Gubler), which removes the dependence on a secondary-source quotation of LeVeque. The formula $\chi=d'(1-S)$ also explains the growth types: the exceptional curves are exactly those of genus $0$ with $n_\infty=1$ (power and radical, $\chi>0$: polynomial-size families) or $n_\infty=2$ (Pell, $\chi=0$: unit-group orbits, logarithmic counts).

*Status.*
- The proof is a `PAPER_PROOF` written in this repository. It has not been independently refereed.
- The Siegel input is `THEOREM_EXTERNAL_DEPENDENCY` and is ineffective.
- `atlas.curve_invariants` computes $g$, $d'$, $n_\infty$, $g_C$ and $\chi$ for every classification.
- The test suite checks, on 1500 random $(F,d)$ with repeated and complex roots, that $2g_C$ is a non-negative even integer, and that $\chi<0$ exactly for the finite type. Earlier runs of the same check covered 4000 cases.
- *Independent geometry.* `crosscheck/theorem_g_sage.py` computes, for every $2\le d\le12$ and every multiplicity profile of degree $\le12$, the invariants of $y^{d'}=\prod(x-i)^{r_i/g}$. The geometric genus comes from Singular (normalisation of the plane curve) in every case. The places at infinity come from Sage's function fields (integral closure) wherever that finishes within a per-case time limit. The script compares $g_C$ with the Riemann–Hurwitz value $(2-n_\infty-d'(1-S))/2$, and $n_\infty$ with $\gcd(d',\deg F/g)$. See `receipts/theorem_g_check.json` for the case count and any disagreements.
- *Lean.* The combinatorial content is compiled. `S_le_one_iff` shows that $S\le1$ exactly for the power, radical and Pell profiles, and `profile_table_ok` checks the Riemann–Hurwitz integrality and the sign of $\chi$ over the same finite range by kernel evaluation. What a referee must still trust is the geometric normalisation step (2) and Siegel's theorem.

*Proof of Theorem A.* The $t$-profile is determined by Yun's squarefree decomposition $F=c\prod_jS_j^j$: a root of $S_j$ has $t=d/\gcd(d,j)$. The types are therefore mutually exclusive and exhaustive. Parts 1–3 are Theorems P, B and C, the last with Lemma Q. Part 4 is Theorem G. $\square$

Two observations connect the atlas to the monograph's rigid branch ($d\mid\deg F$ and $\operatorname{lc}F$ an integer $d$-th power).

*Rigid polynomials are never of radical type.* In the radical type $\deg F=r+d\deg G\equiv r\not\equiv0\pmod d$.

*Rigid polynomials of Pell type have finitely many hits.* Here $c=b^d=(b^2)^e$, so $\Gamma\subseteq\{b^2,-b^2\}$ and each $P_\gamma$ has leading coefficient $\pm$ a square. Lemma Q(1–2) then applies. This agrees with the Lean theorem `rigid_dichotomy`. For example, $n^2+1$ and $n(n+1)$ are rigid and of Pell type.

## 6. Complete enumeration in the Runge branch

The v0.5 certificate proves that there are no hits beyond a cutoff $B$ but leaves $[1,B)$ to a scan, and $B$ can be huge: $\approx3.9\cdot10^{10}$ for the product of $12$ consecutive integers with $d=4$. The following refinement makes the whole hit set computable, using work that is polylogarithmic in the old cutoff.

**Theorem R.** Let $F\in\mathbb Z[x]$ be rigid of degree $dq$ with leading coefficient $b^d$, and not a $d$-th power. Let $Q=P/D$ be its truncated root ($P\in\mathbb Z[x]$, $D\ge1$) and $R=F-Q^d\neq0$, of degree $r<(d-1)q$. For a threshold $x_0\ge1$ put
$$a(x_0)=|b|-\sum_{i<q}|Q_i|x_0^{i-q},\qquad C(x_0)=\sum_{i\le r}|R_i|x_0^{i-r},\qquad T(x_0)=\Big\lfloor\frac{D\,C(x_0)}{a(x_0)^{d-1}x_0^{(d-1)q-r}}\Big\rfloor .$$
Assume $a(x_0)>0$ and, if $d$ is odd, $C(x_0)x_0^r<a(x_0)^dx_0^{dq}$. Then every hit $n\ge x_0$ is an integer root of one of the $2T(x_0)+1$ nonzero polynomials
$$G_t(x)=D^dF(x)-(P(x)+t)^d,\qquad |t|\le T(x_0).$$
Consequently the number of hits is at most $x_0-1+(2T(x_0)+1)(d-1)q$. Since $T(x_0)\to0$, only $G_0=D^dR$ survives for large $x_0$.

*Proof.* For $x\ge x_0$ the bounds $|Q(x)|\ge a(x_0)x^q>0$ and $|R(x)|\le C(x_0)x^r$ follow termwise. If $F(n)=m^d$, choose $y\in\{m,-m\}$ with $y^d=F(n)$ and $yQ(n)\ge0$. For even $d$ both signs are available. For odd $d$, $y=m$ works because $|R(n)|<|Q(n)|^d$ forces $F(n)=Q(n)^d+R(n)$ to have the sign of $Q(n)$. Write $y=sQ(n)$ with $s\ge0$. Then $s^d-1=R(n)/Q(n)^d$, and the elementary inequality $|s-1|\le|s^d-1|$ (Lean: `abs_sub_one_le_abs_pow_sub_one`) gives
$$|Dy-P(n)|=D|Q(n)||s-1|\le \frac{D|R(n)|}{|Q(n)|^{d-1}}\le \frac{D\,C(x_0)\,n^{r-(d-1)q}}{a(x_0)^{d-1}}\le \frac{D\,C(x_0)\,x_0^{r-(d-1)q}}{a(x_0)^{d-1}},$$
because $r<(d-1)q$ and $n\ge x_0$. So $t=Dy-P(n)$ is an integer with $|t|\le T(x_0)$, and $D^dF(n)=(Dy)^d=(P(n)+t)^d$.

Next, $G_0=D^dR\ne0$. For $t\ne0$, $G_t=D^dR-\big((P+t)^d-P^d\big)$, and the second term has degree exactly $(d-1)q>r$ with leading coefficient $d\,t\,(Db)^{d-1}$. So $G_t\ne0$ and it has at most $(d-1)q$ roots. $\square$

**Algorithm (`runge.py`).** Scan $[1,B_0)$ where $B_0$ is the least power of $2$ satisfying the hypotheses. Then walk the dyadic blocks $[x_0,2x_0)$: for each block either scan it, or find the integer roots in the block of every $G_t$ with $|t|\le T(x_0)$ by exact Sturm-sequence bisection, whichever is cheaper. Stop at the first $x_0$ with $T(x_0)=0$ and solve $G_0=0$ on $[x_0,\infty)$. Every step uses exact integer or rational arithmetic, so the output is a complete hit list.

The list can be reproduced by `python -m perfectpower enumerate`. It has been cross-checked against direct scans on about 1000 random rigid polynomials, in the tests and in the receipt generator.

**Corollary R′ (divisor trick).** If $F$ is rigid with respect to some divisor $d'\ge2$ of $d$, then the hit set of $(F,d)$ is effectively computable, because every $d$-th power is a $d'$-th power. For example, $n^4+1$ with $d=6$ is handled through $d'=2$.

**Remark (Runge's criterion).** For the curve $y^d=F(x)$ with $\deg F=M$ and $g=\gcd(d,M)$, the places at infinity correspond to the roots of $X^g=\operatorname{lc}F$. Runge's method applies when these places split into at least two Galois orbits, that is, when $X^g-\operatorname{lc}F$ is reducible over $\mathbb Q$. By Capelli's theorem this happens exactly when $\operatorname{lc}F$ is a $p$-th power for some prime $p\mid g$, or when $4\mid g$ and $\operatorname{lc}F\in-4\mathbb Q^{4}$.

The first case is precisely Corollary R′ with $d'=p$. In the second case $d$ is even and $\operatorname{lc}F<0$, so $F(n)<0$ for large $n$ and there are trivially finitely many hits, found by a scan up to the last sign change. So the effective class of `runge.py` together with this trivial case covers every superelliptic equation to which the leading-term form of Runge's criterion applies. (This bookkeeping is a remark, not an independent proof of Runge's theorem.)

**Named consequences** (`receipts/atlas_benchmarks.json`), each a complete proof relative to Theorem R and exact arithmetic:

- $1+n+n^2+n^3+n^4$ is a square for $n\ge1$ only at $n=3$, where it equals $121$. This is Ljunggren's classical result, recovered with one polynomial solve; v0.5 cutoff $48$.
- The product of $k$ consecutive positive integers $n(n+1)\cdots(n+k-1)$ is never a perfect $d$-th power for the following pairs, each settled in at most $0.03$ s. These are the fixed-$(k,d)$ instances of the Erdős–Selfridge theorem that the Runge condition $d\mid k$ covers:

  | $k$ | $d$ |
  |---|---|
  | 4 | 2, 4 |
  | 6 | 2, 3, 6 |
  | 8 | 2, 4, 8 |
  | 10 | 2, 5 |
  | 12 | 2, 3, 4, 6 |

  The largest v0.5 cutoff among them was $3.87\cdot10^{10}$ ($k=12$, $d=4$).
- $n^4+1$ is never a square or a sixth power.

**Lean certificates.** For 17 of these instances the complete hit set is a compiled Lean theorem emitted by `lean_emit.py`; see `PerfectPower/Generated/Runge.lean` and the formal audit. The instances include all the consecutive-product pairs above. $(10,2)$ and $(12,4)$ use *interval-sandwich* certificates (`lean_sandwich.py`): $[1,\infty)$ is covered by intervals on which $(P+t)^d<D^dF<(P+t+1)^d$ is proved once, symbolically, by a Taylor shift split into nonnegative parts (`gcongr` and `positivity`), plus a tail and a few isolated points. For $(10,2)$ this takes 283 pieces below a tail at $n=20277$; for $(12,4)$, 49 pieces below $n=478$.

**Formal status.** The two smallest named cases are compiled Lean theorems: `ljunggren_hitSet` (the hit set is exactly $\{3\}$) and `consecutive_four_hitSet` (empty). Each traps $2m$ or $m$ between consecutive integers, which is Theorem R with an explicit $t$-range. The analytic core — eventually $|y-Q(n)|<1/(2D)$ with $y\neq Q(n)$ — is the compiled Lean theorem `eventually_no_hit`. The formal 0–1 law `rigid_zero_one` states that on the rigid branch the hit density exists and equals $1$ if $F=G^d$ with $G \in \mathbb Z[X]$, and $0$ with a finite hit set otherwise. The reduction itself is compiled in integer form: `runge_pointwise`, `runge_uniform`, `runge_finite` in `PerfectPower/RungeReduction.lean`. Their hypotheses are the integer inequalities $|D^dF(n)-P(n)^d|<(T+1)|P(n)|^{d-1}$, and for odd $d$, $<|P(n)|^d$. Only the derivation of these inequalities for all $n\ge x_0$ from $a(x_0)$ and $C(x_0)$ is not yet formalised.

## 7. The shift spectrum

The monograph studies $S(n)+k$ for a fixed sequence $S$ and a variable shift $k$. For polynomial $S$ the atlas gives a complete answer in terms of the *critical values* of $S$.

**Corollary K.** Let $S\in\mathbb Z[x]$ with $\deg S=M\ge1$ and $d\ge2$. Let $\mathcal K(S)$ be the set of integers $-S(\xi)$ with $S'(\xi)=0$; it is the set of integer roots of $\operatorname{Res}_x(S(x)+k,S'(x))$, which has degree $M-1$ in $k$. For $k\notin\mathcal K(S)$ the polynomial $S+k$ is squarefree, every root has $t=d$, and:

- if $M=1$: $S+k$ is of radical type with exponent $1/d$ or bounded;
- if $M=2$ and $d=2$: $S+k$ is of Pell type (logarithmic or bounded);
- otherwise ($M\ge3$, or $M=2$ and $d\ge3$): $S+k$ has finitely many hits.

In particular, if $M\ge3$, then *for all but at most $M-1$ shifts $k$ the hit set of $S(n)+k$ is finite*, and polynomial or logarithmic growth can occur only at critical values. At most one $k$ makes $S+k$ an integer-polynomial $d$-th power. The reason is that $G_1^d-G_2^d$ is a nonzero constant only if both $G_1$ and $G_2$ are constant.

*Examples.* For $S=n^3$ and $d=2$, $\mathcal K=\{0\}$: the Mordell curves $m^2=n^3+k$ have finitely many integral points for each $k\ne0$ (Siegel), while $k=0$ gives $\sqrt N$ hits. For $S=n^3-3n$ and $d=2$, $\mathcal K=\{\pm2\}$, and $n^3-3n+2=(n-1)^2(n+2)$ is of radical type with $\kappa=1$. For $S=n^2+n$, $\mathcal K=\emptyset$ over $\mathbb Z$ because the critical value $-1/4$ is not an integer. `python -m perfectpower shifts` computes $\mathcal K(S)$ exactly by resultant interpolation.

**Remark (all exponents at once).** Let $\mathcal P$ be the set of perfect powers $m^d$ with $|m|\ge2$ and $d\ge2$, and consider $A_{\mathcal P}(N)=\#\{n\le N: F(n)\in\mathcal P\}$. If $F$ has at least two distinct roots, the Schinzel–Tijdeman theorem (Acta Arith. 31 (1976)) bounds $d$ effectively in terms of $F$. So $A_{\mathcal P}$ is a finite union of the atlas counts over $d\le d_0(F)$, and it again has growth $N$, $N^{1/t}$, $\log N$ or $O(1)$. If $F=c(x-\alpha)^r$ has a single root, Theorem B applies to each $d$ separately, and the union is dominated by the smallest $t$.

**Remark (integer-valued polynomials).** If $F\in\mathbb Q[x]$ takes integer values on $\mathbb Z$ and $L$ is its coefficient denominator, then $F$ and $L^dF\in\mathbb Z[x]$ have the same hits. Indeed $M^d=L^dF(n)$ makes $F(n)=(M/L)^d$ an integer that is a rational $d$-th power, hence an integer $d$-th power. The atlas therefore covers binomial coefficients (`atlas.integerize`).

- *Square triangular numbers.* $n(n+1)/2$ is of Pell type with $\kappa=1/\log(3+2\sqrt2)$, and its hits are $1,8,49,288,1681,\dots$.
- *Square values of $\binom n3$.* These are of finite type (an elliptic curve), with scan hits $n=3,4,50$ up to $10^5$. This agrees with the classical theorem that these are the only ones.

**Application (sums of powers; Schäffer).** Let $S_k(n)=1^k+\cdots+n^k$, an integer-valued polynomial of degree $k+1$. Schäffer (1956) proved, via LeVeque's theorem (which Theorem G replaces here), that $S_k(n)=m^d$ has infinitely many solutions only for $(k,d)\in\{(1,2),(3,2),(3,4),(5,2)\}$. The atlas classifies every $(k,d)$ from the root multiplicities of $S_k$ and recovers exactly this list, which the receipt checks for $k\le10$, $d\le6$. It also supplies the constants:

| $(k,d)$ | type | first hits | growth |
|---|---|---|---|
| $(1,2)$ | Pell | $1,8,49,288,\dots$ (square triangular numbers) | $\kappa=0.567296$ |
| $(3,2)$ | power | all $n$ (Nicomachus: $S_3=(n(n+1)/2)^2$) | $N$ |
| $(3,4)$ | Pell | same as $(1,2)$ | $\kappa=0.567296$ |
| $(5,2)$ | Pell | $1,13,133,1321,13081,\dots$ | $\kappa=0.436218=1/\log(5+2\sqrt6)$ |

Every other pair is of finite type. A scan to $10^4$ finds nontrivial hits only for $(k,d)=(2,2)$: $n=24$, which is Lucas's cannonball problem, settled by Watson (1918).

The implementation also handles $F=G^e$ exactly for a divisor $e$ of $d$. In that case $F(n)=m^d$ if and only if $G(n)=\pm s^{d/e}$, and the atlas recurses on $(G,d/e)$. For example, $(n+1)^2$ with $d=4$ has hits $n=3,8,15,\dots$.

## 8. Transforms of each type

For the indicator $X$ of hits put $Z_X(s)=\sum X(n)n^{-s}$ and $K_X(\tau)=\sum X(n)e^{-\tau n}$. The monograph asked what count asymptotics imply for these transforms. Abel summation gives $Z_X(s)=s\int_1^\infty A(x)x^{-s-1}\,dx$ and $K_X(\tau)=\tau\int_0^\infty A(x)e^{-\tau x}\,dx$.

**Theorem T.** Suppose $A(x)=\kappa x^{\beta}+E(x)$ with $0<\beta\le1$ and $E$ bounded. Then

- $Z_X(s)=\kappa s/(s-\beta)+H(s)$, where $H(s)=s\int_1^\infty E(x)x^{-s-1}dx$ is holomorphic on $\Re s>0$. So $Z_X$ continues meromorphically to $\Re s>0$ with one simple pole, at $s=\beta$, with residue $\kappa\beta$.
- $K_X(\tau)=\kappa\,\Gamma(1+\beta)\,\tau^{-\beta}+O(1)$ as $\tau\downarrow0$.

If instead $A(x)=\kappa\log x+E(x)$ with $E$ bounded, then $Z_X(s)=\kappa/s+H(s)$ with $sZ_X(s)\to\kappa$ as $s\downarrow0$, and $K_X(\tau)=\kappa\log(1/\tau)+O(1)$.

*Proof.* Substitute the asymptotic into the Abel integrals, using $s\int_1^\infty x^{\beta-s-1}dx=s/(s-\beta)$, $s\int_1^\infty \log x\,x^{-s-1}dx=1/s$, $\tau\int_0^\infty x^\beta e^{-\tau x}dx=\Gamma(1+\beta)\tau^{-\beta}$, and $\tau\int_1^\infty\log x\,e^{-\tau x}dx=\log(1/\tau)-\gamma+o(1)$. The error terms are bounded because $|s\int E x^{-s-1}|\le |s|\sup|E|/\Re s$ and $\tau\int|E|e^{-\tau x}\le\sup|E|$. $\square$

By Theorems B and C the hypotheses hold exactly, with $\beta=1/t$, in the radical type and with the logarithm in the Pell type. So every polynomial hit sequence has fully explicit transform asymptotics:

| Type | $Z_X$ | $K_X$ |
|---|---|---|
| Power, $c=b^d$ | $\zeta(s)$ | $\sim1/\tau$ |
| Radical | pole at $1/t$ | $\sim\kappa\Gamma(1+1/t)\tau^{-1/t}$ |
| Pell | $\sim\kappa/s$ at $0$ | $\sim\kappa\log(1/\tau)$ |
| Finite | Dirichlet polynomial | bounded |

The receipt `heat_kernel_checks_theorem_T` evaluates $K_X(\tau)$ from exact structural hit lists at $\tau=10^{-3},10^{-5},10^{-7}$. The difference $K_X(\tau)-\text{main term}$ stays bounded:

- $4n+1$: tends to $-1$;
- $3n+5$ with $d=3$: tends to $-0.167$;
- $2n^2+1$: about $-0.24$;
- $3n^2+1$: about $0.005$.

This answers the monograph's question "what does $A(N)\sim cN^\alpha(\log N)^\beta$ imply" in the polynomial case, where only $(\alpha,\beta)\in\{(1,0),(1/t,0),(0,1),(0,0)\}$ occur.

**Theorem T2 (second-order heat asymptotics, Pell type).** Let $P=An^2+Bn+C$ be of Pell type with infinitely many square values, and put $\beta=-B/(2A)$. Apart from finitely many terms, the hits split into subsequences
$$n_j=\alpha E^j+\beta+O(E^{-j}),\qquad j\ge0.$$
There is one subsequence for each positive Pell orbit $\mathcal O$ and each good residue class $r$ of the orbit index modulo the period $\pi_{\mathcal O}$, with $E=\varepsilon^{\pi_{\mathcal O}}$ and $\alpha=\eta_r/(4A)$. (The shift comes from $X=2An+B$: the orbit element $X_j+Y_j\sqrt{4A}=\eta_rE^j$ has $X_j=\tfrac12(\eta_rE^j+\bar\eta_rE^{-j})$, so $n_j=(X_j-B)/(2A)=\alpha E^j+\beta+O(E^{-j})$.) Then
$$K_X(\tau)=e^{-\tau\beta}\sum_{\text{classes}}\Big(\frac{\log(1/(\tau\alpha))-\gamma}{\log E}+\frac12+\Phi_E\big(\log(\tau\alpha)\big)\Big)+c_{\mathrm{int}}+O(\tau),$$
where
$$\Phi_E(u)=\frac2{\log E}\,\mathrm{Re}\sum_{m\ge1}\Gamma\!\Big(\frac{2\pi i m}{\log E}\Big)e^{-2\pi i m u/\log E}$$
is continuous and $\log E$-periodic, and $c_{\mathrm{int}}=\#\{\text{hits}\le M\}-\#\{\text{model terms}\le M\}$ for any $M$ beyond which hits and model terms coincide. Expanding $e^{-\tau\beta}=1-\tau\beta+O(\tau^2)$ gives the two-term form
$$K_X(\tau)=\kappa\log\frac1\tau+C_0+\sum_{\text{classes}}\Phi_E\big(\log(\tau\alpha)\big)+O\big(\tau\log(1/\tau)\big),\qquad C_0=\sum_{\text{classes}}\Big(\frac{\log(1/\alpha)-\gamma}{\log E}+\frac12\Big)+c_{\mathrm{int}},$$
with $\kappa$ the Lemma Q constant. The remainder is $O(\tau)$ when $B=0$. When $B\ne0$ the leading correction is $-\beta\kappa\,\tau\log(1/\tau)$, and $O(\tau)$ is false.

*Correction.* An earlier version of this theorem stated $n_j=\alpha E^j+O(E^{-j})$ and an $O(\tau)$ remainder for the two-term form. Both are wrong when $B\ne0$. The receipt shows the failure: for $2n^2+2n$ the unshifted residual divided by $\tau$ grows from $2.8$ to $8.1$ as $\tau$ goes from $10^{-4}$ to $10^{-12}$, while the shifted residual divided by $\tau$ stays at $0.25$.

*Proof.* The Mellin transform of $\lambda\mapsto\sum_{j\ge0}e^{-\lambda E^j}$ is $\Gamma(s)/(1-E^{-s})$ for $\Re s>0$. Shift the contour to $\Re s=-\tfrac12$.
- The double pole at $s=0$ contributes $(\log(1/\lambda)-\gamma)/\log E+\tfrac12$.
- The simple poles at $s=2\pi im/\log E$, $m\ne0$, contribute $\Phi_E(\log\lambda)$. The series converges absolutely because $|\Gamma(iy)|\sim\sqrt{2\pi/|y|}\,e^{-\pi|y|/2}$.
- The remaining integral is $O(\lambda)$.

Write $e^{-\tau n_j}=e^{-\tau\beta}e^{-\tau\alpha E^j}e^{-\tau\delta_j}$ with $\delta_j=O(E^{-j})$. Replacing $e^{-\tau\delta_j}$ by $1$ costs $O(\tau\sum_jE^{-j})=O(\tau)$. Then apply the Mellin expansion with $\lambda=\tau\alpha$. Each of the finitely many discrepancies between hits and model terms is $\pm e^{-\tau n}=\pm1+O(\tau)$, which gives $c_{\mathrm{int}}$. For the two-term form, $(e^{-\tau\beta}-1)$ times the class sum is $-\tau\beta\kappa\log(1/\tau)+O(\tau)$. $\square$

*What it adds.*
- **It distinguishes families with the same $\kappa$.** $2n^2+1$ and $2n^2+2n$ (four times the triangular numbers) share $\kappa=1/\log(3+2\sqrt2)$, but their constants differ: $C_0=-0.2376$ and $-0.0410$.
- **The oscillation is not negligible.** It has peak-to-peak amplitude $0.011$ for $2n^2+1$ but $0.58$ for $5n^2+n+3$.
- **It connects to the Dirichlet series.** Because $Z_X(s)=\sum_{\text{classes}}\alpha^{-s}/(1-E^{-s})+(\text{entire near }\Re s=0)$ up to the shift, the heat fluctuations are the contributions of the imaginary poles $s=2\pi im/\log E$ of $Z_X$.

*Status.* `PAPER_PROOF` (standard Mellin analysis). `receipts/pell_heat.json` checks seven families and reports, for $\tau=10^{-4},\dots,10^{-12}$, the ratio of the residual to its claimed scale.
- *Shifted model:* residual$/\tau$ is constant to four digits for $\tau\ge10^{-10}$. The values are $0.5$, $0.5$, $0.2$, $0.125$ and $0.25$ for the families with a nonzero next term; for $2n^2-7$ and $6n^2-2$ the ratio is at rounding level.
- *Unshifted two-term form:* residual$/(\tau\log(1/\tau))$ stays bounded, and residual$/\tau$ grows when $B\ne0$.
- *Precision:* at $\tau=10^{-12}$ the residual is about $10^{-13}$, close to double-precision rounding of $K\approx 10$–$20$, so that ratio carries noise of about $0.06$.

## 9. Exponential sequences: a dual spectrum

For polynomials, the *exponents* $1/t$ with $t\mid d$ are discrete and the density is $0$ or $1$. For pure exponentials the roles swap: the density itself takes the discrete values $1/L$ with $L\mid d$.

**Theorem E.** Let $a\ge2$, $c\ne0$, $d\ge2$, and write $a=b^s$ with $s$ maximal. The set of $n\ge1$ for which $c\,a^n$ is a $d$-th power is either empty or a full residue class $n\equiv n_0\pmod L$ with $L=d/\gcd(d,s)$. So the hit density exists and equals $0$ or $\gcd(d,s)/d$.

*Proof.* For $d$ even and $c<0$ there are no hits. Otherwise $c\,a^n$ is a $d$-th power if and only if $v_p(c)+n\,v_p(a)\equiv0\pmod d$ for every prime $p$.

- For $p\nmid a$ this is a solvability condition, $d\mid v_p(c)$.
- For $p\mid a$ it is solvable if and only if $\gcd(d,v_p(a))\mid v_p(c)$, and then it pins $n$ down modulo $d/\gcd(d,v_p(a))$.

All these moduli divide $d$, so the intersection is empty or a single class modulo their lcm. That lcm is $d/\gcd(d,\gcd_p v_p(a))=d/\gcd(d,s)$. $\square$

*Examples* (receipt `exponential_theorem_E`, each cross-checked by a scan to $n\le120$):

- $2^n$ is a square for $n$ even, density $1/2$;
- $5\cdot5^n$ is a fifth power for $n\equiv4\pmod5$, density $1/5$;
- $36^n$ is a fourth power for $n$ even;
- $12\cdot18^n$ is never a sixth power.

`perfectpower/exponential.py` computes $(n_0,L)$.

**Shifted exponentials.** For $k\neq0$, $c\,a^n+k=m^d$ has only finitely many solutions (`THEOREM_EXTERNAL_DEPENDENCY`). Write $n=dq+r$ and $X=a^q$. The equation becomes $Y^d-c\,a^rX^d=k$. For $d\ge3$ this is a Thue equation, or it factors. For $d=2$ it is Pell-type, and the $X$-coordinates of a Pell class form a binary recurrence that meets the powers of $a$ only finitely often (S-unit theorem). So the shift destroys the positive density completely.

The receipt `shifted_exponential_scans` lists all hits with $n\le400$ for $a\in\{2,3\}$, $|k|\le9$ and $d\in\{2,3\}$. These lists are `EXACT_COMPUTATION` only. Among them is Ramanujan–Nagell, $2^n-7=m^2$ only for $n=3,4,5,7,15$ (proved by Nagell in 1948), which the scan reproduces.

## 10. What remains open

1. **Effective enumeration in the finite type outside the Runge branch.** Examples are $n^3+k=m^2$ (Mordell curves) and $n^3+n+4=m^2$, which has the isolated hit $n=4128$. Brindza's bounds are effective but impractical. Elliptic-logarithm methods, as in Magma or Sage, solve genus-one cases. **Status now:**
   - For $m^2=n^3+an+b$ with $|a|,|b|\le12$, all 622 curves, including $n^3+n+4$, have hit lists certified by an *independent* computation: Sage `integral_points`, see `receipts/cubic_crossval.json`. These agree with our scans.
   - That certification is external. Lean does not check it.
   - `crosscheck/genus1_sage.py` extends this to 400 non-monic or shifted cubics and cubes $m^3=aX^2+bX+c$. Each is reduced to an integral short Weierstrass model, and the Sage points are pulled back through explicit congruences. The results are in `receipts/genus1_crossval.json`: 399 are certified, one rests on an unproven rank, and none disagrees with an exact sieve scan to $10^6$. Three families have certified hits beyond $10^6$: $6n^2-7n-6=95339^3$ at $n=12{,}017{,}947$, $6n^2+n+1=61301^3$ at $n=6{,}196{,}204$, and $3n^2-n-3=19483^3$ at $n=1{,}570{,}085$.
   - $\binom n2=m^3$ and $\binom n3=m^2$ are settled given Sage's integral points of $Y^2=X^3+1$ and $Y^2=X^3-36X$ (`PerfectPower/Binomial.lean`).
   - Genus $\ge2$ non-Runge families, e.g. $n^5+2=m^2$, remain **scan evidence only** (`SCAN_EVIDENCE_ONLY`). They are scanned exactly to $10^8$ by a modular sieve, and no completeness is claimed.
   - *How late are late hits?* The external reviewer's finite-bucket fuzzer (seed 11) scanned 1322 random finite-type polynomials exactly to $10^8$ (`receipts/late_hits_fuzz.json`). Only one has a hit beyond $5000$: $n^3+2n^2-3n-1$, with hits $2$ and $47882$, which is genus one and certified by Sage. The very late hits in the genus-one receipt ($n\approx1.2\cdot10^7$) come from cubes of quadratics with larger coefficients, which that fuzzer does not sample.
   - The cross-validation also shows that scan horizons matter. Scans to $10^3$ or $10^4$ would have missed hits on 18 and 4 of the 622 curves; the largest hit is $n=80327$.
2. **Formalisation of Theorems B, C, R in Lean.** The valuation core and the count of Theorem B are compiled, and so are the Pell interfaces, orbit exhaustion and the bound $A(N)=O(\log N)$. Still open: the exact $\kappa\log N$ asymptotic, and the threshold inequalities of Theorem R. Siegel's theorem itself is far beyond current formal libraries and should remain an external boundary.
3. **Uniformity.** Bound the number of hits in the finite type uniformly in the height of $F$. Theorem R gives such a bound in the Runge branch, $x_0-1+(2T(x_0)+1)(d-1)q$; is there a Runge-type bound polynomial in the height?
4. **Beyond polynomials.** Exponential sequences ($a^n+k$; Catalan–Mihăilescu, Pillai), factorials (Brocard–Ramanujan), and linear recurrences each need their own theorems. The atlas shows that the polynomial exponent spectrum is discrete. Is the exponent spectrum of $\{S(n)+k\}$ discrete for every linear recurrence $S$?
5. **Thin sets.** Theorem A implies that the hit set of a non-power polynomial is contained in a thin set of type 2 with at most $O(N^{1/2})$ elements up to $N$, consistent with the Cohen–Serre bound for thin sets (Serre, *Topics in Galois Theory*, §3.4). A direct large-sieve proof of Corollary A's barrier, avoiding Siegel, would give an effective exponent bound in the finite type.

## References

- W. J. LeVeque, On the equation $y^m=f(x)$, *Acta Arith.* 9 (1964), 209–219.
- B. Brindza, On S-integral solutions of the equation $y^m=f(x)$, *Acta Math. Hungar.* 44 (1984), 133–139.
- T. Nagell, *Introduction to Number Theory*, Wiley 1951 (bounds for fundamental solutions of $x^2-Dy^2=N$).
- K. Matthews, The Diophantine equation $x^2-Dy^2=N$, $D>0$, *Expo. Math.* 18 (2000), 323–331; J. P. Robertson, Solving the generalized Pell equation (2004) (the LMM algorithm).
- C. Runge, Über ganzzahlige Lösungen von Gleichungen zwischen zwei Veränderlichen, *J. reine angew. Math.* 100 (1887), 425–435.
- W. Ljunggren, Noen setninger om ubestemte likninger av formen $(x^n-1)/(x-1)=y^q$, *Norsk Mat. Tidsskr.* 25 (1943), 17–20 (the case $n=5$, $q=2$: only $x=3$ among $x>1$).
- P. Erdős and J. L. Selfridge, The product of consecutive integers is never a power, *Illinois J. Math.* 19 (1975), 292–301.
- J. J. Schäffer, The equation $1^p+2^p+\cdots+n^p=m^q$, *Acta Math.* 95 (1956), 155–189.
- A. Schinzel and R. Tijdeman, On the equation $y^m=P(x)$, *Acta Arith.* 31 (1976), 199–204.
- S. Wang, A counter-example to Grunwald's theorem, *Ann. of Math.* 49 (1948), 1008–1009.
- J.-P. Serre, *Topics in Galois Theory*, Jones and Bartlett 1992, Chapter 3.
