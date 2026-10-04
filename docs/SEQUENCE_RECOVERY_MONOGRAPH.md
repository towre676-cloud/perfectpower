# More arithmetic recovered from our old work

This push turns five older lines of work into reusable exact Python machinery, while preserving the existing Lean integral-pullback, covering-map and target-recovery bridges. The recovered material connects sequence discovery, modular reconstruction, formal operators and finite primary modules to the integer repository. It introduces no new Lean theorem and does not promote a finite sequence match into a proof of an infinite definition.

## Signed recurrence arithmetic

The November 2025 Padovan work supplies the concrete recurrence

\[a_{n+3}=a_{n+1}+a_n,\qquad a_0=a_1=a_2=1.\]

Its annihilator is \(E^3-E-1\). `perfectpower.recurrence.Recurrence` now handles arbitrary exact rational constant-coefficient recurrences. Quotient-polynomial binary powering evaluates distant indices without iterating through all preceding terms. Negative indices use the inverse of the shift when its constant coefficient is nonzero. A singular shift explicitly rejects backward evaluation.

The engine converts recurrence data to a rational formal generating function, and converts any rational generating function with nonzero constant denominator back to a recurrence. Polynomial numerators can introduce an initial transient; the resulting homogeneous order includes that delay. No convergence assumption is involved.

Modulo an integer, the engine tracks the complete state until repetition. Noninvertible recurrences can have a preperiod, which is kept separately from the cycle. A predicate on the state produces accepted positions; block counting gives exact finite counts at arbitrarily large bounds. Padovan modulo seven has preperiod zero and period 48. Exactly 250,000,000,000 indices below \(10^{12}\) have a term divisible by seven. This is a modular filter, not a count of integer zeros or perfect-power values.

## Bounded reconstruction and the actual sequence atlas

The August 2026 saved tube reports, *The Fixed Locus Tube Theorem V10.18 Live Robust* and *V10.26 Dynamic Mathematics*, describe modular annihilator discovery, Chinese remaindering, bounded rational reconstruction and held-out-prime checks. Their reported order-eight operator and 747 coefficients are provenance for the method; this push does not reproduce that original operator.

`perfectpower.modular_reconstruction` supplies Berlekamp–Massey over prime fields, generalized consistent CRT and exact rational reconstruction. For numerator bound A and denominator bound B, reconstruction requires M > 2AB, an invertible denominator, and exact congruence verification. Insufficient modulus or inconsistent congruences fail explicitly.

`scan_seq_directory` runs that workflow on the repository's staged `.seq` files. It separates training terms from held-out terms, requires consistent modular order, reconstructs bounded rational coefficients, verifies the full supplied prefix exactly, and checks disjoint held-out primes. Each record retains the sequence ID, offset, source name, source-file hash and relative path. Rejections are recorded alongside candidates.

The committed receipt scans all 149 staged sequence files: 135 candidates and 14 rejections. Seven supplied rational generating functions also translate successfully and match every supplied term at the recorded offset. These are finite-prefix candidates and translated source formulas. They do not prove the OEIS definitions and do not change the existing Lean-backed promotion policy. This scan does not process the entire external OEIS index.

## Exact operator replay and polynomial projectors

The November 7, 2025 hypergeometric work supplies

\[{}_3F_2(1,1,1;1/4,3/4;t),\qquad
\Theta(\Theta-1/4)(\Theta-3/4)-t(\Theta+1)^3.\]

The recovered coefficient ratio is \(16n^2/((4n-3)(4n-1))\). `perfectpower.exact_operators.Weyl` implements sparse rational differential operators in normal form, using the exact relation Dt − tD = 1. The replay checks the annihilator against 24 computed coefficients. Tests extend that replay and check composition and the commutator. This is a formal coefficient calculation; no analytic continuation or zeta identity is asserted.

The Wilson current identity Q³ = −11Q gives the quotient modulus x(x²+11). Its two polynomial projectors are 1+x²/11 and −x²/11. The generic quotient-projector builder checks factorization, idempotence, orthogonality and sum-to-one. Pairwise coprime primary factors are supported; splitting a repeated-root component into noncoprime factors is rejected. The original Wilson matrix is not reconstructed here.

## Formation phases and finite primary modules

The September 20 Formation work retained relative phases in cyclic p-primary subgroups. A height profile or modulo-p shadow alone loses information: in (Z/4Z)², the generators (1,1) and (1,3) share a modulo-two shadow but generate different subgroups. `cyclic_phase` canonically normalizes the unit ambiguity while retaining those phases.

`primary_cyclic_counts` counts elements by exact p-power order and divides by the number of generators to count nontrivial cyclic subgroups. `subgroup_census` independently enumerates finite subgroups by closure under joins, with explicit element and join budgets. The three recovered fixtures reproduce the recorded counts: Z/8 × Z/4 × Z/2 has 81 subgroups and 27 nontrivial cyclic subgroups; (Z/4)³ has 129 and 35; (Z/9)² has 23 and 16. These cyclic subgroups are not all lattice atoms. `presentation_cyclic_counts` connects this machinery to the existing integral-lattice local torsion profile, and requires a finite cokernel.

## Reproduction

Run from the repository root with `PYTHONPATH=python`:

```sh
python -m perfectpower recurrence --coeff 1,1,0 --initial 1,1,1 --index -10 --modulus 7 --stop 1000000000000
python -m perfectpower sequence-atlas --seq-dir data/oeis/seq
python -m perfectpower primary-module --prime 2 --exponents 3,2,1 --census
python -m perfectpower operator-replay
python python/sequence_recovery_receipt.py
python -m unittest discover -s python/tests -v
```

`receipts/sequence_recovery/results.json` contains the actual scan and recovered examples. Companion CLI receipts preserve executable examples. The regression suite checks exhaustive small rational reconstruction, randomized modular recurrences and signed evaluation, generating-function identities, transient modular counting, held-out corruption rejection, complete subgroup censuses, phase invariance, differential-operator arithmetic and quotient projectors. Validation results and their scope are recorded beside the receipts. Runtime replay records retain `execution_verified: false`: successful Python checks are not Lean proof certificates.

The final complete Python suite passes 403 tests with four skips; the focused recovery and OEIS suite passes all 44 tests. Python compilation and whitespace checks pass. Existing Lean files are preserved without modification; no new Lean build is claimed.
