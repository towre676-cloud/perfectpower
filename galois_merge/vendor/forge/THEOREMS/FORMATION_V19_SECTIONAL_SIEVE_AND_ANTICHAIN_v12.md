# Formation v19 sectional sieve and first induced-H2 antichain — Forge v0.12

Forge imports Formation Polarization v19 byte-for-byte and places its sectional multiplier-exponent sieve before the v17 integral-signature compiler.

For `L3(4)`, v19 proves that the only proper nonabelian simple section species are `A5`, `A6`, and `L3(2)`.  Their 2-primary multiplier exponents are all 2, whereas the 2-primary multiplier of `L3(4)` has exponent 4.  Therefore no proper semisimple section rooted in `L3(4)` can support a primitive `C4` target character.  The primitive-C4 query terminates before H2-map enumeration.  Even/order-two `C4` relations remain a separate downstream atlas problem.

The package also freezes the first normalized induced-H2 matrix library below the three named roots `L3(4), A7, L2(11)`, using current CTblLib cover-fusion data plus the v18 full-signature theorem.  Up to multiplier-coordinate automorphisms the promoted rows are:

- `A7 <- A6` at primes 2 and 3: identity maps on `C2` and `C3`;
- `A7 <- L3(2)` at prime 2: identity on `C2`;
- the depth-two `A7 <- A5` 2-primary map obtained through `2.A5 -> 2.A6 -> 2.A7`: identity on `C2`;
- `L2(11) <- A5` at prime 2: identity on `C2`;
- `L3(4) <- A6` at prime 3: identity on `C3`;
- `L3(4) <- M20 -> A5` at prime 2: the v18 full signature, normalized as the isomorphism `C4^2 x C2 -> C4^2 x C2`.

Compressing these rows by exact signature equality, inclusion dominance and the available multiplier automorphisms leaves seven marked antichain records.  The count does not pretend to be the complete even-frequency section atlas: the actual 2-primary maps `M(A6)_(2), M(L3(2))_(2) -> C4^2` inside `L3(4)` remain explicitly unresolved.  V19 proves only that their images have exponent at most 2, which is already sufficient for the primitive-C4 stop rule.
