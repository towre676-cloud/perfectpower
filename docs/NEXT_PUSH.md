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
   - **In Lean, under one named premise per class** (`matveev_i`, Matveev's lower bound;
     `Generated/Field756.lean`). Unit generation (`unitGen_proved`), the norm representatives
     (`normRep_*_proved`) and the analytic inequality (`analytic_i_proved`) are proved:
     `minus7`, `minus28` and `minus63`. Kernel-checked: the direct-`H` reduction chains, norm
     identities, boxes, small-`b` searches and branch transport.
   - **Missing:** Matveev's theorem, the boundary that stays external, and a Lean check of the
     height bounds behind its constants ([UNIT_PREMISES.md](UNIT_PREMISES.md)).
2. **The `D = 72` residual equation.**
   - **Target:** `∀ u v, H72 u v ≠ 1 ∧ H72 u v ≠ −1`.
   - **In Lean, under Matveev's bound only** (`D72Residual.residual_empty`,
     `Generated/D72Unit.lean`). The bound drops to `H ≤ 4`, a box of 81 elements.
   - **Missing:** Matveev's theorem itself (`matveev_pos`).
   - This closes two classes and no curve.
3. **Descent certificates that carry nonempty lists.**
   - **Done for branch transport:** `DescentThueList.complete_of_lists` accepts obligations
     `(G, M, L)` with complete lists and reads `y` off each listed solution.
   - **Done for split nodes** (`DescentLists.lean`). `descL` is the `descB` checker with leaves
     that carry lists (`KindL.given`). `candL` composes the candidate list: the zero child scaled
     by `p` (only when `p³ ∣ M`), and each line child mapped by its matrix. `descL_complete` and
     `root_iff` prove
     `S(F, M) = p·S(F, M/p³) ∪ ⋃_λ T_λ S(G_λ, M/p^{s_λ})`, filtered by evaluation, from complete
     leaves (`LeafComplete`, a hypothesis).
   - **Since then:** every node carries its prime (splits and lifting leaves), unit leaves are
     carried from source equations by checked unimodular maps, and the root's solutions are a
     `Finset` (`rootSet`, duplicates removed).
   - **Worked instance:** `D = 23` (`Generated/Minus23.lean`): classes 8, 9, 10 through two unit
     equations in the field 621, under Matveev for those two equations.
   - **Still open:** complete lists at the other leaves. In the measured workload
     (`receipts/descent_residual.json`) they are 109 distinct unit equations `G = ±1` in other
     cubic fields, so each needs a Thue bound (the field-756 pipeline, applied per field).
4. **A consumer-accepted replacement.**
   - **Target:** for one independently authored verification condition, a checked instance of
     `Γ ∧ C ∧ ¬G ↔ Γ ∧ L ∧ ¬G` that a downstream verifier (Why3/GNATprove) accepts.
   - **Today:** the curve theorem is Lean-proved, and the substitution into the SMT source is
     checked in Python (`smt_cert.check_certificate`).
5. **Default-checked bounded Pell plans.**
   - **Done for small units** (`BoundedPell.lean`, `quad_bounded`). The adapter emits a
     kernel-checked instance per bounded query and applies it by default.
   - **Remaining: large fundamental units.** For `263n² + 1` the unit is about `8.4·10¹⁹`, so
     the root box `Y ≤ 2.5·10²⁰` cannot be enumerated, and the plan refuses. A proved
     continued-fraction (or LMM) root characterization would replace the box.
   - **Remaining:** ranges crossing `2qN + p = 0` (split at the turning point, with the
     single-`N` case checked directly), and a Why3 emission for these lists.
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
