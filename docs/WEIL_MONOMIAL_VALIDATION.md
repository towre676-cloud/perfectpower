# Concrete monomial bridge validation

`make check-weil-monomial` passed with Lean 4.20.0 and the pinned Mathlib revision. The focused audit covers thirty-five theorem declarations and six proof-carrying constructions, forty-one declarations in total, across `MonomialOrbitSpace` and `WeilMonomial`. Each dependency set is contained in propext, Classical.choice and Quot.sound. Neither sorryAx nor Lean.ofReduceBool appears.

The audit includes both analysis/synthesis inverse identities, the actual Heisenberg basis, basis representation and expansion, literal Fourier and chirp intertwining/conjugation, chirp inverses in both orders, exact commutant coefficient equations, quotient descent, a nonvanishing-gauge equivalence, fixed-space dimension laws, the actual odd-level matrix/quotient equivalence, transpose action, and concrete symmetry/commutativity from explicit reflection connectivity. The positive odd cyclic specialization derives its half from oddness.

The ten existing exact orbit tests also pass. The 166-level phase/reflection receipt and all 63 prior finite dimension certificates are unchanged. No new Python traversal, JSON refinement claim, Mordell closure or global orbit-classification theorem is presented as delivered. The remaining arithmetic premises are documented beside the statements and in the handoff.
