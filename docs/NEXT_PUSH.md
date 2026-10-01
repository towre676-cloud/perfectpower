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
- The discrete exponent spectrum $\lbrace 0,1\rbrace \cup\lbrace 1/t : t\mid d\rbrace$, with an $N^{1/2}$ barrier for non-powers.

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
- **Binomial rows.** $\binom n2=m^3$ holds only for $n\in\lbrace 1,2\rbrace$, and $\binom n3=m^2$ only for $n\in\lbrace 1,2,3,4,50\rbrace$. Lean proves both reductions and hit lists; the integral points of the two curves are a Sage-certified hypothesis.
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

*(The "next" items listed at this point have since been done: Theorems B and C with explicit constants (`OPEN_PROBLEMS.md` §6, §8), unconditional nonempty genus-one lists (`MordellMinus2/4/13`, `MordellFLT3`, the 36 branch-compiler lists), and a narrow Bilu–Tichy counting module. The primary-source comparison is in `RELATED_WORK.md`.)*

## Remaining theorem statements (current)

Each item is stated as the theorem that would close it, with its first unproved dependency.
Superseded recommendations from earlier rounds have been removed; the history is above and in
git.

1. **Complete lists for `D = 7, 28, 63`, from one shared field** (`MORDELL_BRANCH.md` §7.3).
   - **Target:** `∀ x y, y² = x³ − D ↔ (x, y) ∈ L_D` for the three curves.
   - **Route:** for each of the 7 classes `F_i = M_i`, every solution has
     `c₀a − bφ = ±α_{i,j} ε₁^{e₁} ε₂^{e₂}` with `max |eᵢ| ≤ B_{i,j}`; then the finite search and the
     branch transport.
   - **First missing piece:** the bound `B_{i,j}` (linear forms in logarithms, then reduction).
     After it: the norm = determinant identification for the field of discriminant 756, and
     completeness of the norm representatives and of the unit basis (`h = 1`, certified externally).
2. **The `D = 72` residual equation.**
   - **Target:** `∀ u v, H72 u v ≠ 1 ∧ H72 u v ≠ −1`.
   - **Already in Lean** (`NormForm.lean`): the `δ` basis, the lattice criterion and the norms.
   - **Missing:** that `ε₁, ε₂` generate the units, completeness of the norm-±9 representatives,
     and the exponent bound.
   - This closes two classes and no curve.
3. **Descent certificates that carry nonempty lists.**
   - **Target:** a checker whose split nodes prove
     `S(F, M) = ⋃_λ T_λ S(G_λ, M/p^{s_λ}) ∪ p·S(F, M/p³)` and whose leaves carry proved complete
     finite lists.
   - **Foundations in Lean:** `Interfaces.sublattice_branch` (image condition included) and the
     per-node prime of `descM`.
4. **A consumer-accepted replacement.**
   - **Target:** for one independently authored verification condition, a checked instance of
     `Γ ∧ C ∧ ¬G ↔ Γ ∧ L ∧ ¬G` that a downstream verifier (Why3/GNATprove) accepts.
   - **Today:** the curve theorem is Lean-proved, and the substitution into the SMT source is
     checked in Python (`smt_cert.check_certificate`).
5. **Default-checked bounded Pell plans.**
   - **Target:** for a bounded query `lo ≤ N ≤ hi`, a Lean theorem listing every solution, so the
     adapter can apply it without `--allow-unchecked`.
   - **Obstacle:** large fundamental units. For `263n² + 1` the unit is about `8.4·10¹⁹`, so the
     root box is impractical; a proved continued-fraction (or LMM) root characterization is the
     direct route.
6. **Positive `k`** (`MORDELL_BRANCH.md` §7.4).
   - **Target:** seed coverage of `p² − |D|q² = k³` modulo cubes of the fundamental unit, with
     ideal classes, exceptional primes and the integral readout.
   - `orbit_mod_three` is only the exponent normalization.
7. **Smaller formal items.**
   - Coefficient-bound lemmas for `runge_uniform` (`OPEN_PROBLEMS.md` §7).
   - Theorem T2 (the log-periodic second term) in Lean.
   - Tauberian converses with minimal hypotheses.
   - Effective genus-one enumeration outside the Mordell family (elliptic logarithms with
     reduction).

**Not worth effort:** uniformity in `d` via Schinzel–Tijdeman (the bounds are too weak to compute
with), and Erdős–Selfridge certificates beyond `k = 12` (already theorems; pure engineering).

**Owner actions:** Mathlib or Archive proposals (`OPEN_PROBLEMS.md` §5), a Lean Zulip post, a
tagged release with a DOI, and arXiv (math.NT, cross-listed to cs.LO).
