# Orbit dimension and symmetry validation

`make check-weil-orbit` generates exact phase/reflection certificates for all 160 levels from 1 through 160 and six additional levels: 243, 256, 343, 512, 625 and 729. The resulting 166 dimensions agree with the paper formula. Every surviving orbit passes the phase-sensitive transpose identity, and every rejected orbit is outside the even-index sublattice. All 63 previous finite cyclotomic basis/rank-minor dimensions match.

Independent twisted-convolution checks reduce both orbit-product orders modulo the cyclotomic polynomial at eight levels: 3, 4, 6, 8, 9, 12, 16 and 18. Modular integer entry calculations verify the conjugation and transpose phases. The ten unit tests include invalid levels, resource limits, a planted phase corruption and the public query scope. No floating-point tolerance is used.

`PerfectPower/WeilOrbitSymmetry.lean` contains twelve general theorem declarations. Its focused audit rejects sorryAx and Lean.ofReduceBool and allows only propext, Classical.choice and Quot.sound. It proves six gauge identities, closure of the simultaneous commutant, transpose-product reversal consequences, symmetry of a finite sum under a reflecting permutation, symmetry of its linear span, and commutativity under an explicit spanning hypothesis. The concrete Heisenberg basis and all-level orbit classification are still paper mathematics, not hidden assumptions counted as closed Lean results.

The previous complete finite packets are unchanged. Their summary metadata now points to the paper theorem, and their producer emits that same metadata. This validation does not claim a rebuild of every historical repository module or any new Mordell closure.
