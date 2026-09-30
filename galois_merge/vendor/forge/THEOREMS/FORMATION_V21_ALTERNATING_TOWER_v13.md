# Formation v21 alternating-tower compiler — Forge v0.13

Formation Polarization v21 is imported byte-for-byte and compiled as a coefficient-universal section family.

For the natural alternating inclusions the multiplier transport is

`C6 --iso--> C6 --mod 2--> C2 --iso--> C2 --iso--> ...`

from `A6` upward.  More explicitly:

- `A6 -> A7` induces the identity on `C6` (v20, prime-to-index transfer at index 7);
- `A7 -> A8` induces the unique nonzero map `C6 -> C2`, hence is surjective with kernel `C3`;
- `A_n -> A_{n+1}` for `n>=8` induces an isomorphism `C2 -> C2`.

The v17 integral signature for the marked section `A8 <- A7 -> A7` is the graph generator `<(1,-1)> <= C2 x C6`, and its coefficient relation for every finite abelian coefficient group is the graph of pullback along `C6 -> C2`.  The published maximal-subgroup order sieve for `A8` makes the marked `A8 dashrightarrow A7` signature antichain a singleton modulo target automorphisms.

Forge stores this as one functorial tower rather than separate coefficient-specific relations.  Composition gives `A6 -> A8 : C6 -> C2` with kernel `C3`, followed by the stable `C2` tail.

This new branch does not resolve the two still-open even 2-primary maps from `A6` and `L3(2)` into `M(L3(4))_(2)=C4^2`; those remain a separate finite section-data problem.
