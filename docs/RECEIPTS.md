# Research receipt policy

## Status labels

- **`THEOREM_EXTERNAL_DEPENDENCY`**: the receipt names the exact imported theorem and the step it is applied to. Current external dependencies:
  - The polynomial 0–1 proof of the monograph depends on Boshernitzan's uniform-distribution criterion in its nonrigid branch.
  - The atlas (research notes, Theorem A, part 4), the exponent spectrum, and the shift spectrum depend on LeVeque's theorem on $y^m=f(x)$, which rests on Siegel's theorem.
  - The shifted nonsingular-cubic finiteness statement depends on Siegel's theorem.
- **`PAPER_PROOF`**: a written mathematical argument.
- **`EXACT_COMPUTATION`**: records parameters, range, exit code, and reproducible integer calculations.
- **`FINITE_HIT_CERTIFICATE`**: records rational polynomial identities and inequalities proving the absence of hits beyond a cutoff.
- **`COMPLETE_HIT_LIST`** (new in 0.6): the full hit set, produced by a procedure whose correctness is a `PAPER_PROOF` and whose arithmetic is exact. Two procedures qualify: the Runge enumeration (Theorem R) and the structural descriptions (Theorems P, B, C).
- **`LEAN_VERIFIED`**: reserved for declarations compiled against a named immutable dependency revision and passing `audit/check_axioms.sh`. This includes the machine-generated hit-set theorems in `PerfectPower/Generated/`: Python proposes the data, and Lean checks the proof.

## Receipts in release 0.6

**`LEAN_VERIFIED`.** Every declaration listed in [the formal audit](FORMAL_AUDIT.md) is compiled against Lean `v4.20.0` and Mathlib `v4.20.0`. These include the rigid dichotomy, the rigid 0–1 law, and twisted-power finiteness.

**`exact_benchmarks.json`** is an `EXACT_COMPUTATION`. Its counts are exact over the recorded ranges, and it asserts no numerical `limsup`. A certificate's `exact_identity` means polynomial equality was checked. A valid cutoff that is not an identity means no hit occurs at or above that cutoff, by the explicitly checked inequalities. A nonrigid classification is neither a certificate of infinitely many hits nor a rate estimate.

**`atlas_benchmarks.json`** has three kinds of rows:

- **Types `power`, `radical`, `pell`.** The structural counts are exact consequences of Theorems P, B, C (`PAPER_PROOF`). They are cross-checked against the defining scan at $N=10^5$ (`EXACT_COMPUTATION`), and the generator aborts on any disagreement. The constant $\kappa$ is a floating-point evaluation of an exact formula.
- **Rows marked `effective` with `complete_hit_list` or `runge` entries.** These are `COMPLETE_HIT_LIST` receipts.
- **Rows of `finite` type that are not effective.** For example, the elliptic curves $n^3+1$ and $n^3+n+4$. Their finiteness is `THEOREM_EXTERNAL_DEPENDENCY` (LeVeque/Siegel), and their listed hits are only an `EXACT_COMPUTATION` up to $10^5$. Observed absence of further hits is not promoted to a theorem.

## Finite surgery

The code constructs the modified sequence by finitely many overrides, and the exact integer $D$ then proves the count identity for all later $N$. The Lean theorem `A_sub_eq_const` proves the same identity in general. A finite-range check of two arbitrary source functions would not.

## Recast earlier receipts

- Periodic zeta residue is a theorem under periodicity. Periodic heat density is a special case of an Abelian theorem valid whenever the ordinary density exists. Research notes §8 gives the corresponding statements for every polynomial type.
- Tropical finite-window maximum is an elementary observation.
- Periodic entropy zero is elementary.
- A cofinite-tail Čech construction that only restates invariance of limsup under finite-prefix change is tautological.
- The BSD link for a shifted nonsingular cubic is an unconditional Siegel application and does not use $L(E,1)$. It is now a special case of the shift spectrum.
