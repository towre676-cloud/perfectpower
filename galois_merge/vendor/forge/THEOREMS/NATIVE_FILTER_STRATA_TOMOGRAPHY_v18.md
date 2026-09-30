# Native filter strata, rank-tomography duality, and the word-access ladder — v0.18

## 1. The twelve determinantal channel strata

In the v0.17 native coordinates an element consists of the semisimple vertex payload

`(a,A,S) in F_p x M15(F_p) x M5(F_p)`

and arrow payloads represented by matrices

`U in M_{2x5}(F_p)`, `V in M_{3x75}(F_p)`.

The native rank pair is `(rank U, rank V)`.  Because the vertex payload is completely independent of the radical coordinates, the closure of the stratum `(r_+,r_-)` is the product of the 251-dimensional vertex space with the determinantal varieties `rank(U)<=r_+` and `rank(V)<=r_-`.  Hence

`dim closure(r_+,r_-) = 251 + r_+(7-r_+) + r_-(78-r_-)`.

This gives all twelve channel strata exactly.  The full `(2,3)` stratum is Zariski open dense.  The nearest proper rank-drop locus is `r_+<=1`, of codimension 4.  Complete plus blindness `(0,3)` has codimension 10, whereas even a one-step minus rank drop `(2,2)` already has codimension 73.  Thus a generic unconstrained learned/native transport map is expected to have rank pair `(2,3)`: lower minus rank is highly structured, not an incidental numerical sparsity effect.

## 2. Rank-tomography duality

For a family `F`, let `R_+(F)` and `R_-(F)` be the occupied row spaces in the two- and three-dimensional arrow multiplicity spaces.  Their dimensions are the v0.17 invariants `r_+(F),r_-(F)`.

The same integers have three exact meanings:

1. the minimum numbers of common plus/minus execution channels after one shared `GL2 x GL3` arrow change;
2. the minimum sizes of exact shared linear arrow dictionaries for the family;
3. the minimum numbers of independent linear selectors required for tomography of the occupied arrow multiplicity spaces.

The proof is ordinary row-space duality.  A shared dictionary of size `k` can contain the family iff it contains the occupied row space, so `k>=r`; a basis of that row space attains equality.  Dually, fewer than `r` independent selectors have a nonzero common kernel on the occupied row space and therefore cannot be tomographically injective, while a dual basis of `r` selectors is injective.

For one family the `GL2 x GL3` orbit is determined by the two ranks, but for several families the ranks alone are not enough.  The exact compiler state is the pair of occupied subspaces `(R_+,R_-)` in the subspace lattices of `F_p^2` and `F_p^3`.  Combining families takes the join `(R_++R'_+,R_-+R'_-)`; intersection records reusable channels.  Thus two `(1,3)` families can remain `(1,3)` when their plus lines coincide or jump to `(2,3)` when those lines are transverse.  The rank pair is the dimension shadow of this finer Grassmannian/subspace-lattice state.

This is the precise Wilson analogue of the distinction emphasized by imported Formation v28-v29: global/reachability state and local selector tomography are different invariants.  V28 proves complete recovery from a primitive selector orbit in an irreducible module; v29 exhibits parity-only fixed selectors in the first reducible residual channel.  In the Wilson native category the analogous local quantity is exactly the channel-rank pair.

## 3. Exact word-filter accessibility

Let `W_<=L` be the evaluated span of all binary words in the frozen generators `g,h` of length at most `L`.  Its dimensions are the already certified sequence

`1,3,7,15,31,63,127,255,486`.

V0.18 computes, for every `L=0,...,8`, the intersections of `W_<=L` with the plus-blind locus `U=0`, the minus-blind locus `V=0`, the radical `a=A=S=0`, and the pure one-sided radicals.

The thresholds are sharp:

- Through degree 2, the only plus-blind or minus-blind element is the identity line.
- At degree 3, the plus-blind intersection jumps to dimension 5.  Its family rank is `(0,3)`.  Thus genuinely nontrivial plus-blind native filters already occur at degree 3.
- Through degree 6, the minus-blind intersection remains only the identity line.
- At degree 7, the minus-blind intersection jumps to dimension 30 and has family rank `(2,0)`.
- The radical is zero through degree 6.  At degree 7 it has dimension 4 and family rank `(2,3)`: the first pure-radical filters are necessarily mixed across both signs.
- At degree 7 both one-sided pure-radical intersections are still zero.
- At degree 8, the full radical appears: dimension `235=10+225`, with pure plus radical dimension 10 and pure minus radical dimension 225.

So there are two different senses of sparsity.  Semisimple-plus-arrow filters can become plus-blind as early as degree 3, and semisimple-minus-arrow filters can become minus-blind at degree 7.  But if the vertex payload is required to vanish, one-sided arrow transport is delayed until the final degree-eight closure.

## 4. Exact filtered degree of B64

The v0.15 boundary `B64` lies inside the pure minus radical `J_-` and has family rank `(0,3)`.  V0.18 computes

`B64 intersect W_<=7 = 0`.

Since `W_<=8=A`, every nonzero element of `B64` has evaluated filtered degree at most 8, while the zero intersection above shows that none has degree at most 7.  Therefore

`every nonzero B64 element has exact filtered degree 8.`

This sharpens the previous degree-nine boundary description.  `B64` was discovered as the old 64-dimensional obstruction subspace inside the degree-nine relation quotient, but as an actual transport operator family it sits precisely on the degree-eight pure-minus frontier.

## 5. Consequence for learned transport maps

The correct learned-map diagnostic is now exact.  A trainable native transport filter should be decoded to `(U,V)` and reported by `(r_+,r_-)`, not by named-arrow coefficient magnitudes.  The rank pair is simultaneously its exact shared-dictionary size and its exact linear-tomography dimension.  Generic unconstrained maps lie in `(2,3)`; observed concentration into `(0,3)`, `(2,0)`, `(1,3)`, `(2,2)`, or smaller strata is therefore structural evidence and comes with a certified execution schedule.

There is also an explicit category boundary.  The earlier 271-class route-filter learner lives in the 152-dimensional Wilson Hecke/orbital algebra.  It is not silently reinterpreted as a 486-dimensional native transport filter.  Only polynomial/linear filters in the transport generators and exact star-transport morphisms are classified here unless a future theorem constructs a functor between the two algebras.

Machine certificate: `DATA/RELATION/NATIVE_STRATA_V18/native_filter_strata_v18.json` and `native_filter_strata_bases_p1.npz`, reproduced by `scripts/analyze_native_filter_strata_v18.py`.
