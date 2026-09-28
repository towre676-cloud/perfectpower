# Beyond the 0–1 law: the exponent spectrum of polynomial perfect-power hits

**Research notes for release 0.6 (28 September 2026).** These notes extend [the monograph](MONOGRAPH.md). Notation is unchanged: for $F\in\mathbb Z[x]$ and $d\ge 2$, a *hit* is an index $n\ge 1$ with $F(n)=m^d$ for some $m\in\mathbb Z$, and $A(N)=\#\{1\le n\le N: n \text{ is a hit}\}$. The shift $k$ of the monograph is absorbed into $F=S+k$ except in §7.

Every result below carries one of the status labels of [the receipt policy](RECEIPTS.md). In summary:

| Result | Status | Where |
|---|---|---|
| Theorem P (power type) | `LEAN_VERIFIED`: density one is `hasDensity_one_of_pow`; finiteness is `power_type_finite` | §2, `PerfectPower/ZeroOne.lean` |
| Theorem B (radical type, exact parametrisation) | `PAPER_PROOF` + `EXACT_COMPUTATION` cross-check; the monomial case $c=1,\alpha=0$ is `LEAN_VERIFIED` (`monomial_count`) | §3, `atlas.py`, `PerfectPower/Monomial.lean` |
| Lemma Q, Theorem C (Pell type) | `PAPER_PROOF` + `EXACT_COMPUTATION` cross-check | §4, `atlas.py` |
| Theorem A (atlas) and Corollary A (exponent spectrum) | `THEOREM_EXTERNAL_DEPENDENCY` (LeVeque 1964) | §5 |
| Theorem R (complete Runge enumeration) | `PAPER_PROOF`; its analytic core is `LEAN_VERIFIED` (`eventually_no_hit`) | §6, `runge.py` |
| Rigid-branch 0–1 law | `LEAN_VERIFIED` (`rigid_zero_one`) | §6 |
| Corollary K (shift spectrum) | `THEOREM_EXTERNAL_DEPENDENCY` (LeVeque) | §7 |
| Theorem T (transforms) | `PAPER_PROOF` | §8 |

## 1. Summary

The monograph proves that the hit density of $F(n)$ is $1$ if $F=G^d$ with $G\in\mathbb Z[x]$ and $0$ otherwise, and asks for finer information inside the zero-density branch: rates, exponents, exact counts, and effective enumeration. These notes answer the rate question completely for polynomials, conditional only on LeVeque's classical finiteness theorem.

Write $F=c\prod_i(x-\alpha_i)^{r_i}$ over $\overline{\mathbb Q}$ with distinct $\alpha_i$, and put $t_i=d/\gcd(d,r_i)$. Call the multiset $\{t_i\}$ the *$t$-profile* of $(F,d)$. It is computable exactly from a squarefree decomposition, without factoring $F$.

**Theorem A (atlas).** Let $F\in\mathbb Z[x]$ be nonconstant and $d\ge2$. Exactly one of the following holds.

1. **Power type** (all $t_i=1$). Then $F=cG^d$ with $G\in\mathbb Q[x]$ monic. If $c$ is an integer $d$-th power, then $F$ is the $d$-th power of an integer polynomial and $A(N)=N$. Otherwise the hits are exactly the positive integer roots of $F$.
2. **Radical type** ($t$-profile $\{t,1,\dots,1\}$, $t\ge2$). There is an explicit $\kappa\ge0$ with $A(N)=\kappa N^{1/t}+O(1)$; $\kappa$ is computed from one congruence count (Theorem B).
3. **Pell type** ($t$-profile $\{2,2,1,\dots,1\}$, so $d$ is even). There is an explicit $\kappa\ge0$ with $A(N)=\kappa\log N+O(1)$; $\kappa$ is computed from Pell orbits modulo $2A$ (Theorem C).
4. **Finite type** (every other profile). The hit set is finite.

Parts 1–3 are elementary and are proved here. Part 4 is LeVeque's theorem.

**Corollary A (exponent spectrum and the root barrier).** Let $\alpha(F,d)=\limsup_N \log(1+A(N))/\log N$. Then
$$\alpha(F,d)\in\{0,1\}\cup\{1/t:\ t\mid d,\ t\ge2\},$$
and every value in this set occurs. Moreover $\alpha=1$ exactly when $F$ is an integer-polynomial $d$-th power. Otherwise $A(N)=O(N^{1/p})$, where $p$ is the least prime factor of $d$. In particular $A(N)=O(N^{1/2})$ for every non-power $F$, and $A(N)=O(N^{1/3})$ when $d$ is odd. All these bounds are sharp.

*Proof of the corollary from Theorem A.* In the radical type $t=d/\gcd(d,r)$ divides $d$ and exceeds $1$, so $t\ge p$. The Pell and finite types have $\alpha=0$. The monomial $F=x^{r}$ with $\gcd(r,d)=d/t$ has hits exactly at the $t$-th powers, so $A(N)=\lfloor N^{1/t}\rfloor$ realises $1/t$. This is Theorem B, and it is also the compiled Lean theorem `monomial_count`. For sharpness take $r=d/p$. $\square$

This refines the monograph's 0–1 law in two ways. First, the zero branch has a quantitative ceiling, $N^{1/2}$, instead of $o(N)$. Second, the proof of density zero no longer uses Boshernitzan's equidistribution theorem, although it now depends on LeVeque's theorem, which in turn rests on Siegel's theorem. The two proofs of the 0–1 law are logically independent.

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

**LeVeque's theorem** (W. J. LeVeque, *On the equation $y^m=f(x)$*, Acta Arith. 9 (1964) 209–219). Let $f\in K[x]$ over a number field $K$, with root multiplicities $r_i$ and $t_i=m/\gcd(m,r_i)$. The equation $y^m=f(x)$ has only finitely many solutions in integers of $K$ unless $\{t_i\}$ is $\{t,1,\dots,1\}$ or $\{2,2,1,\dots,1\}$. B. Brindza (*On S-integral solutions of the equation $y^m=f(x)$*, Acta Math. Hungar. 44 (1984)) made the finiteness effective via Baker's method, with bounds that are astronomically large.

*Proof of Theorem A.* The $t$-profile is determined by the multiplicities $\{j:\ S_j\ne1\}$ and degrees $\deg S_j$ of Yun's squarefree decomposition $F=c\prod_jS_j^j$: a root of $S_j$ has $t=d/\gcd(d,j)$. The types are therefore mutually exclusive and exhaustive. Part 1 is Theorem P, part 2 is Theorem B, part 3 is Theorem C with Lemma Q, and part 4 is LeVeque's theorem with $K=\mathbb Q$. $\square$

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

## 9. What remains open

1. **Effective enumeration in the finite type outside the Runge branch.** Examples are $n^3+k=m^2$ (Mordell curves) and $n^3+n+4=m^2$, whose scan finds the isolated hit $n=4128$. Brindza's bounds are effective but impractical. Elliptic-logarithm methods, as in Magma or Sage, solve genus-one cases. A general superelliptic implementation needs Baker–Davenport reduction. Until then these hit lists are `EXACT_COMPUTATION` over a range, not complete.
2. **Formalisation of Theorems B, C, R in Lean.** Theorem B needs $p$-adic valuations of $c_1z^r$, which are available in Mathlib. Theorem R needs the explicit threshold inequalities; its analytic core is already compiled. LeVeque's theorem itself is far beyond current formal libraries and should remain an external boundary.
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
- A. Schinzel and R. Tijdeman, On the equation $y^m=P(x)$, *Acta Arith.* 31 (1976), 199–204.
- S. Wang, A counter-example to Grunwald's theorem, *Ann. of Math.* 49 (1948), 1008–1009.
- J.-P. Serre, *Topics in Galois Theory*, Jones and Bartlett 1992, Chapter 3.
