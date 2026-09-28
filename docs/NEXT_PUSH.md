# Research roadmap after release 0.6

## Done in 0.6

**Lean kernel.**
- The Lean kernel compiles against Mathlib `v4.20.0`.
- It carries an axiom audit and CI.
- It proves the rigid 0–1 law and twisted-power finiteness.

**Rate question.** The monograph's rate question has a complete answer for polynomials, the atlas (research notes, Theorem A):
- A decidable type, computed from root multiplicities.
- Exact parametrisations and asymptotic constants for the power, radical and Pell types.
- LeVeque finiteness for all other types.
- The discrete exponent spectrum $\{0,1\}\cup\{1/t : t\mid d\}$, with an $N^{1/2}$ barrier for non-powers.

**Runge branch.** The branch is now completely enumerable.

**Transforms.** Their asymptotics are proved for every type.

## Formal kernel

1. Derive Theorem P over $\mathbb Q[x]$ from `twisted_hits_subset` by clearing denominators. Connect it to `integral_closure_step` for the density-one half.
2. Formalise the valuation characterisation of Theorem B: $c_1z^r$ is a $d$-th power iff $v_p(z)\equiv\tau_p \pmod t$ for all $p$, together with the sign condition. Mathlib's `padicValInt` and `Nat.factorization` suffice. The monomial count $A(N)=\lfloor N^{\gcd(r,d)/d}\rfloor$ for $n^r$ is done (`monomial_count`); the general case adds a twist $c$ and a rational root $\alpha$.
3. Formalise the explicit thresholds of Theorem R: $a(x_0)$, $C(x_0)$, $T(x_0)$. A certificate from `runge.py`, consisting of $x_0$, the $G_t$, and their root lists, could then be checked by `decide`/`norm_num` inside Lean, closing the gap between the Python tool and the kernel.
4. Keep Boshernitzan and LeVeque as named external boundaries. If a nonrigid statement is wanted formally, state it as a hypothesis-carrying theorem, `LeVeque → …`.

## Arithmetic

1. **Effective finite type outside Runge.**
   - Implement elliptic-logarithm enumeration for genus-one curves $m^2=\text{cubic}$ and $m^3=\text{quadratic}$. Candidates: a Baker bound plus LLL reduction; stdlib-only LLL is feasible.
   - Test on the Mordell curves $m^2=n^3+k$ and on $n^3+n+4$ (hit at $n=4128$).
2. **Uniform bounds.** Is there a hit-count bound in the Runge branch polynomial in $\log H(F)$? Theorem R gives $x_0-1+(2T+1)(d-1)q$, with $T$ polynomial in $H(F)$.
3. **Large-sieve route to the $N^{1/2}$ barrier.** A proof that avoids Siegel (Cohen–Serre thin sets) would make the barrier effective.
4. **Beyond polynomials.** For linear recurrences, factorials and exponential–polynomial sequences:
   - Is the exponent spectrum discrete?
   - Does a shift spectrum with finitely many critical shifts hold?

## Analysis

Theorem T covers exact asymptotics. The Tauberian converses — from $Z_X$ or $K_X$ back to $A(N)$ — remain to be stated with minimal hypotheses. For non-polynomial sequences, the log-log exponent can hide slowly varying factors, and the monograph's warnings apply.

## Numerics

- Keep exact, hash-reproducible receipts.
- The atlas receipt already reaches $N=10^{24}$ structurally and cross-checks against scans at $10^5$.
- Add runtime and memory instrumentation.
- Never let a finite maximum masquerade as $H$ or $\alpha$.
