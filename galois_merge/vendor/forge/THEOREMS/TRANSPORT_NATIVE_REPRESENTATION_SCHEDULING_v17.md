# Native five-arrow representation theory and execution scheduling — v0.17

## The basic category

The v0.16 Morita corner is the path algebra of the acyclic quiver

```
          u1,u2
     row -------> plus
      |
      | v1,v2,v3
      v
     minus
```

with three vertices and five arrows.  Because every arrow starts at `row` and ends at a sink there are no composable arrow pairs, so the Jacobson radical is the arrow span and its square is zero.  The algebra is hereditary, of global dimension one.  A representation is exactly a triple of vector spaces `(P,M,R)` together with two maps `R -> P` and three maps `R -> M`.

For dimension vectors `d=(p,m,r)` and `e=(p',m',r')`, the Euler form and Tits form are

`<d,e> = pp' + mm' + rr' - 2 r p' - 3 r m'`,

`q(p,m,r) = p^2 + m^2 + r^2 - 2rp - 3rm`.

The simple dimension vectors are `(1,0,0)`, `(0,1,0)`, `(0,0,1)`.  The indecomposable projectives have dimension vectors `(1,0,0)`, `(0,1,0)`, `(2,3,1)`, while the indecomposable injectives have dimension vectors `(1,0,2)`, `(0,1,3)`, `(0,0,1)`.

This is **not** a finite- or tame-representation-type algebra.  Setting the plus vertex to zero leaves the three-Kronecker quiver, so the full representation category is wild.  Therefore the useful Wilson classification problem is not a finite catalogue of all indecomposables; it is the exact classification of the finite Wilson-generated families and their invariant arrow ranks.

## Basis-invariant arrow concentration

The two plus arrows and three minus arrows have independent arrow-basis groups `GL2` and `GL3`.  A statement such as “only `u1` is used” is therefore coordinate-dependent.  The correct invariant for one element is the row rank of the `2 x 5` plus flattening and the row rank of the `3 x 75` minus flattening.  For a family of `N` elements, concatenate these flattenings horizontally.  The resulting ranks

`r_+ = rank(2 x 5N)`, `r_- = rank(3 x 75N)`

are simultaneously (i) lower bounds on the number of plus/minus channels in every common arrow basis and (ii) attainable after one common `GL2 x GL3` arrow change.  Thus `(r_+,r_-)` is the exact native-channel complexity of the family.

The historical two-generator Wilson transport is maximally non-sparse in this invariant sense.  The stored generators `g` and `h` each have rank pair `(2,3)`.  Exhaustive native multiplication of all `2^L` binary words for every `1 <= L <= 8` gives `(2,3)` for **every nonempty word**.  The selected 486-word exact basis has one identity element of rank `(0,0)` and 485 elements of rank `(2,3)`.  No common rebasing can eliminate any of the five native channels from this execution family.

The distinguished relation boundary behaves differently.  The full 235-dimensional radical has coordinate projection ranks `(10,225,235)` and family channel ranks `(2,3)`.  The 64-dimensional `B64` boundary has coordinate projection ranks `(0,64,64)` and family channel ranks **`(0,3)`**: it is exactly plus-blind, yet it uses all three minus multiplicity directions as a family.  The older 25-dimensional degree-eight wall has family ranks `(2,3)`.  Thus the minus-side concentration seen in v0.15 is now an exact native-category statement, not merely a large-carrier observation.

## Optimal native schedules

For a product `x_1 ... x_L`, each arrow is independent once the shared vertex prefixes/suffixes are known:

`u_i(x_1...x_L) = sum_t (prod_{s<t} a_s) u_i(x_t) (prod_{s>t} S_s)`,

`v_j(x_1...x_L) = sum_t (prod_{s<t} A_s) v_j(x_t) (prod_{s>t} S_s)`.

Hence the dependency-optimal channel schedule shares left prefixes in `a/A` and right suffixes in `S`, then reduces each live arrow independently.  There is no cross-arrow dependency to serialize.  If a target family has invariant ranks `(r_+,r_-)`, exactly those many channels suffice after a common arrow rebasing, and no exact schedule can use fewer.

Under the frozen naive dense scalar-multiplication accounting for one binary native product, the semisimple vertex payload costs `3501`, each live plus channel adds `30`, and each live minus channel adds `1500`.  The exact schedule cost is therefore

`3501 + 30 r_+ + 1500 r_-`.

The full `(2,3)` transport schedule costs `8061`; the `B64` family schedule `(0,3)` costs `8001`.  More importantly than this modest arithmetic saving, the invariant rank theorem tells the compiler *when an arrow can be deleted exactly*, and prevents false sparsification based on a convenient coordinate gauge.  These counts are algebraic operation counts, not wall-clock hardware measurements.

Machine certificate: `DATA/RELATION/NATIVE_REPRESENTATION_V17/native_representation_schedule_v17.json`, reproduced by `scripts/analyze_native_quiver_representation_v17.py`.
