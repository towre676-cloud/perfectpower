# Named M22 primary Schur signatures — Forge v0.11

Forge v0.11 upgrades the v16 coefficient-specific Schur relation database to the v17 coefficient-independent integral signature

`Lambda_alpha = im(H_2(L,Z) -> M(G) + M(Q)), z |-> (i_*(z),-q_*(z))`.

For coefficient group `A`, the relation is `Hom((M(G)+M(Q))/Lambda_alpha,A)`.  The package preserves v17 and v18 byte-for-byte and imports their reference compilers/regressions.

## Named M22 inclusions

For the inclusion section `Q <= M22` with quotient map `q=id_Q`, current ATLAS/GAP cover-preimage data determines the following primary restrictions, normalized up to automorphisms of multiplier coordinates.

| Q | 2.M22 preimage | 3.M22 preimage | 4.M22 preimage | normalized primary homology restriction |
|---|---|---|---|---|
| `L3(4)` | `2.L3(4)` | `3.L3(4)` | `4_1.L3(4)` | `C4^2 -> C4 : (x,y)|->x`; `C3->C3` identity |
| `A7` | `2 x A7` | `3.A7` | `2.(2 x A7)` | `C2 -> C4 : 1|->2`; `C3->C3` identity |
| `L2(11)` | `2 x L2(11)` | `3 x L2(11)` | `2.(2 x L2(11))` | `C2 -> C4 : 1|->2`; no 3-primary target |

The `A7` and `L2(11)` rows are the important new phenomenon.  At `C2` coefficients the source double-cover character restricts trivially, so the relation is `(x,0)`.  At `C4` coefficients the same integral signature is nontrivial: if the source character is `a in C4`, the target `C2` character is `2a`.  Thus a split double-cover shadow can hide a depth-one `C4` restriction.  This is an explicit named realization of the nonunit Schur-balance mechanism isolated in v16.

The machine-readable file `DATA/FORMATION/SCHUR_SIGNATURES/m22_primary_restrictions_v11.json` contains the integral signatures and every specialized `C2`, `C3`, `C4` relation pair for these rows.

## Imported v18 hard mask

The v18 named section `L3(4) <- M20=2^4:A5 -> A5` has full 2-primary integral signature in `C4^2 x C2`; therefore its annihilator is zero for every finite 2-primary coefficient group.  Forge retains this as the first named hard mask in the integral-signature compiler.

## Boundary

This is not yet an exhaustive Atlas-grade section category.  The named M22 rows are direct subgroup inclusions determined by cover-preimage types; v18 supplies one nontrivial partial epimorphism.  Deeper subgroup domains and semisimple quotients still require induced `H_2` maps, ideally via GAP/HAP or an equivalent exact computation.  v17's signature layer is designed so those future rows can be inserted without rebuilding coefficient-specific tables.
