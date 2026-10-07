# Kernel dimension validation

`make check-commutant-dimension` passed with Lean 4.20.0 and the pinned Mathlib revision. It builds `SeparatedDimension`, `CommutantDimension` and `WeilTensorDimension`, then audits all thirty new general theorem declarations. Every dependency is a subset of propext, Classical.choice and Quot.sound; neither sorryAx nor Lean.ofReduceBool occurs.

The audit includes explicit assembly injectivity and surjectivity, the rectangular product-dimension theorem, all four matrix block-multiplication identities, the separate-action commutant equivalence, its product dimension, the general separation-packet dimension theorem, literal cyclic chirp projections, the Gauss recovery word in a tensor factor, the cyclic tensor dimension theorem, product and cyclic character primitivity, both actual CRT matrix identities and the final CRT-compatible-character dimension theorem.

The previous module's seventeen general declarations remain the audited Gauss and generator-separation foundation, bringing the bridge to forty-seven declarations across the two releases. No new Python arithmetic or packet format was introduced, so the existing exact 63-level census is retained rather than presented as a new computational experiment. This validation is focused and does not claim a rebuild of every historical repository theorem.

The final theorem uses one characteristic-zero coefficient field, positive coprime cyclic moduli, primitive local characters and an odd second factor. It derives the matrix factorization and separation data. It assumes no rank, no centralizer dimension and no prime-power formula. Independently chosen primitive roots and coefficient-field normalization retain a separate transport obligation.
