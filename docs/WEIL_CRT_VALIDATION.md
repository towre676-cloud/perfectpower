# Exact commutant validation

`bash scripts/check_weil_commutant.sh` passed with Lean 4.20.0 and the pinned Mathlib dependencies. It regenerated and independently replayed complete exact certificates at all 63 levels from 2 to 64. Every one of the 42 unordered coprime pairs with factors at least two and product at most 64 agrees with the product of the independently certified dimensions. The compressed packet corpus retains every integer basis matrix and every rank minor, rather than only summary dimensions.

All 21 focused tests passed, including the larger odd and dyadic prime powers, level 64, comparison with the old cyclotomic elimination at levels 2 through 9, explicit product certificates, JSON roundtrip, basis and minor corruption, nonprimitive roots, invalid primes, domain and work-budget rejection, query operations and the 457-row reconciliation.

The general Lean module compiled, and all seventeen theorem declarations were audited. Dependencies are subsets of propext, Classical.choice and Quot.sound. Neither sorryAx nor Lean.ofReduceBool appears. These are general Gauss, Fourier inverse, finite-power projection, Kronecker sufficiency and typed generator-separation results. The paper-level all-modulus dimension conclusion is not counted as a separately kernel-proved theorem.

Adjacent regression checks passed all 29 deep-gems tests and 18 query-space tests, for 68 focused and adjacent Python tests. This is targeted validation and does not claim a full rebuild of the historical repository.

The generated Mordell ledger contains 457 distinct remaining census rows: 323 empty computed lists and 134 nonempty lists. Exactly 28 conditional census rows match unconditional generated descent theorem names. No additional unconditional curve-list registry entry removes a conditional row. The ledger makes no new rank or curve-completeness claim.
