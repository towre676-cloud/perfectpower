# Research roadmap after release 0.6

Current counts (audited declarations, generated certificates, census sizes) are generated into the README by `make counts`; the numbers in the "Done in 0.6" section below are historical snapshots of that release.

## Done in 0.6

**Lean kernel.**
- The Lean kernel compiles against Mathlib `v4.20.0`.
- It carries an axiom audit and CI.
- It proves the rigid 0–1 law and twisted-power finiteness.

**Rate question.** The monograph's rate question has a complete answer for polynomials, the atlas (research notes, Theorem A):
- A decidable type, computed from root multiplicities.
- Exact parametrisations and asymptotic constants for the power, radical and Pell types.
- Finiteness for all other types (originally quoted from LeVeque; now Theorem G from Siegel).
- The discrete exponent spectrum $\{0,1\}\cup\{1/t : t\mid d\}$, with an $N^{1/2}$ barrier for non-powers.

**Runge branch.** The branch is now completely enumerable, and at release 0.6 17 instances had machine-generated Lean certificates.

**Applications.** The atlas recovers Schäffer's sums-of-powers theorem with constants and covers integer-valued polynomials.

**Formal kernel.** At release 0.6 it proved 56 audited theorems, including:
- the monomial count;
- infinitude and density zero for $2n^2+1$;
- Theorem P over $\mathbb Q[x]$;
- Theorem R in integer form.

**Transforms.** Their asymptotics are proved for every type.

## Done after 0.6

- **Provenance gate.** The axiom audit checks every declaration it lists (count in the README). The Mordell census has a per-curve JSONL record (curve, engine and version, rank method and proof status, generators, saturation index, $x$-list and hash, scan), and the CSV names the engine. `make receipts` re-checks every row and its label (`TRUST_BOUNDARY.md` §4).
- **Theorem G** replaces the LeVeque dependency with a Riemann–Hurwitz computation plus Siegel's theorem.
- **Binomial rows.** $\binom n2=m^3$ holds only for $n\in\{1,2\}$, and $\binom n3=m^2$ only for $n\in\{1,2,3,4,50\}$. Lean proves both reductions and hit lists; the integral points of the two curves are a Sage-certified hypothesis.
- **Theorem B valuation core** in Lean (`RadicalValuation.lean`).
- **Theorem T2.** The heat transform of a Pell-type family has a log-periodic second-order term. Corrected after review: the hits are $n_j=\alpha E^j-B/(2A)+O(E^{-j})$, the shifted model has remainder $O(\tau)$, and the unshifted two-term form only $O(\tau\log(1/\tau))$ when $B\ne0$ (`receipts/pell_heat.json` records residual/scale).

- **Lean interfaces for the counts.** `PellGeneral.lean` (norm equation, periodicity modulo $2A$, good classes, geometric counting) and `RadicalCount.lean` ($|vA(N)-RW|\le2Rv$).

## Done after the second review

- **T2 corrected.** The hits are $n_j=\alpha E^j-B/(2A)+O(E^{-j})$. The shifted model has remainder $O(\tau)$, and the two-term form has only $O(\tau\log(1/\tau))$ when $B\ne0$. The receipt reports residual divided by the claimed scale.
- **Gates.**
  - The census domain is checked: the exact key set, unique keys, sorted unique lists and the declared bound.
  - A plain-Python binomial gate ties the Sage receipt to the Lean hypotheses, and a genus-one gate re-verifies the new receipt.
  - `make crosscheck` reruns all Sage steps.
  - Negative tests plant corruptions.
- **Status language.** Everything that rested on LeVeque now rests on Siegel through Theorem G. Theorem G's step 2 now counts $d'$ points over an unramified $x$.
- **Lean.**
  - Pell orbit exhaustion by a descent to a finite box, and the Pell-type bound $A(N)=O(\log N)$ (`pell_count_log`).
  - Function-field Pillai.
  - The combinatorial half of Theorem G, including an exhaustive kernel-checked table for $d,\deg F\le12$.
  - Verified reflective checkers for all generated certificates: the sandwich certificates went from 768 KB to 12 KB, the Runge certificates from 136 KB to 31 KB, and the census is data plus a soundness theorem.
- **Evidence.**
  - Singular/Sage normalisation check of Theorem G.
  - 400 further genus-one families, with certified hits as late as $n=12{,}017{,}947$.
  - A modular sieve for exact scans to $10^8$.
  - The external fuzzers are in `make fuzz` and `make test` with fixed seeds.
- **CI diagnosed.** Jobs are never assigned a runner. That is an account-level Actions block, and only the owner can lift it (README).

## Done after the third review

- **Exact counts in Lean.**
  - `pell_exact_count`: canonical orbit roots, ε-growth, per-class counting, and $\kappa=(\sum g/P)/\log\varepsilon$, cross-checked against the atlas constant.
  - `radical_asymptotic_int`: $\kappa=(R/v)(v/z_0)^{1/t}$, with $R=0$ allowed.
  - `Atlas.lean`: the finite type as an implication from the named premise `SuperellipticSiegel`.
- **Theorem G.** `chi_eq` and `chi_neg_iff` hold for all $d$. The Sage sweep now uses Singular's genus and runs robustly.
- **T2.** The contour now moves past $s=-1$, and the full $O(\tau)$ coefficient is checked numerically.
- **Genus one.** 399 generated Lean hit-list theorems, each from a named Sage point hypothesis.
- **pp-cert/1.** A versioned, hash-bound certificate format with importer, round-trip tests, kernel-checked rejection tests and benchmarks.
- **Quartics.** Now listed, as evidence only.
- **Manuscripts.** A single status table in the monograph, and related work marked unverified where primary texts were unreachable.

**Next:** Theorems B and C (the general reductions) in Lean; one kernel-checked completeness proof for a nonrigid genus-one family; the primary-source comparison; the Bilu–Tichy counting sequel for one family.

## Order of work after 0.6 (recommended)

The centre of gravity moves from proving more theorems to closing the gap between *scan evidence* and *certified statement*.

1. **Done in this round.**
   - Interval-sandwich certificates for $(10,2)$ and $(12,4)$.
   - Cubic cross-validation against Sage: 622/622.
   - Epistemic labels on every data row.
   - `make verify`, trust boundary and licences.
2. ~~Read LeVeque (1964) in the primary source.~~ Superseded by Theorem G, which derives the finite type from Siegel's theorem directly (`TRUST_BOUNDARY.md` §3).
3. **Literature pass.** Cover Bilu–Tichy, Schinzel–Tijdeman, Walsh, Beukers–Tengely and existing formalisations. Write the result into `RELATED_WORK.md` before any announcement or priority claim.
4. **Extend certification of the finite type.**
   - Cover general Weierstrass models (e.g. $\binom n3$) in `crosscheck/`.
   - Add quartic models.
   - Produce Baker-type height bounds where Brindza applies.
   - Lean can check final lists against sieve output, but never the Baker step.
5. **Bilu–Tichy atlas** as the next monograph part (`OPEN_PROBLEMS.md` §2).
6. **Upstreaming and outreach, to be done by the owner.** The actions:
   - propose Mathlib PRs or Archive entries for the candidates in `OPEN_PROBLEMS.md` §5;
   - post on the Lean Zulip about the certificate emitter;
   - tag a release and mint a Zenodo DOI;
   - post on arXiv in math.NT, cross-listed to cs.LO, aimed at CPP/ITP or experimental mathematics.

**Not worth effort:** uniformity in $d$ via Schinzel–Tijdeman (bounds too weak to compute with), and Erdős–Selfridge certificates beyond $k=12$ (already theorems; pure engineering).

## Formal kernel

1. Done: Theorem P over $\mathbb Q[x]$ is `power_type_finite`, and Theorem R in integer form is `runge_finite`.
2. Formalise the valuation characterisation of Theorem B: $c_1z^r$ is a $d$-th power iff $v_p(z)\equiv\tau_p \pmod t$ for all $p$, together with the sign condition. Mathlib's `padicValInt` and `Nat.factorization` suffice. The monomial count $A(N)=\lfloor N^{\gcd(r,d)/d}\rfloor$ for $n^r$ is done (`monomial_count`); the general case adds a twist $c$ and a rational root $\alpha$.
3. Extend the certificate emitter to instances whose Runge plan needs a large $x_0$ or roots of $G_t$ beyond $x_0$. Examples are the consecutive products $(k,d)=(10,2)$ and $(12,4)$. Two routes: a verified range check by `decide` over a computable integer-root predicate, or emitting explicit factorisations of the $G_t$.
4. Keep Boshernitzan and Siegel as named external boundaries. If a nonrigid statement is wanted formally, state it as a hypothesis-carrying theorem, `Siegel → …`.

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
