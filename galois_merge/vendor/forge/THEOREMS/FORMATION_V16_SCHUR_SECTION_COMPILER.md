# Formation v16 Schur-section compiler layer

Formation Polarization v16 adds the exact internal-factor layer missing from the v14-v15 Forge interface. A partial epimorphism `alpha=(H,q):G --> Q` carries the finite-abelian relation

`R_n(alpha) = {(x,y) : i^*x = q^*y}`

in degree-two Schur-character coordinates. The runtime Fourier state `D_X`, the formation join state `Theta(X)`, and the internal-factor relation `R_n(alpha)` are therefore three distinct data structures.

The relation is additive under products and diagonal strips recover coefficient addition. Composition is lax rather than strict, so the compiler MUST retain primitive section relations and MUST NOT replace them by ordinary graph transitive closure. The higher-2-power unique-double criticality problem is reduced exactly to a finite witness search in this relation library. The v15 heuristic that a cross-species edge must itself carry a unit is withdrawn; nonunit balancing such as `(1,1,2)` modulo 4 can be decisive.

Forge v0.9 ships the v16 source archive byte-for-byte, a machine schema for relation rows, and a reference finite-cyclic relation engine. It does not claim that an Atlas-grade database of actual subgroup epimorphisms and induced H_2 maps has already been populated.
