# Formation v13 normal form -> Wilson architecture theorem

## Imported formation theorem
Formation Polarization v13 proves that every perfect mixed `C2`-Schur object has a central normal form `X=U_m/K`, with full character code `D_X=K^perp`, and that formation generation sees exactly

`Theta(X)=(S_X,A_X,C_X)`

with `supp(C_X) <= A_X <= S_X`.  For perfect objects, generated-formation join is exactly

`(S,A,C) join (S',A',C') = (S union S', A union A', C+C')`.

The activity mask is essential: it separates a centerless simple factor, a two-copy even amalgam, and a universal double cover even when parity alone does not.

v13 also closes repeated-amalgam criticality: `A_m` is formation-critical iff every nonzero multiplicity is one, or `m=2e_i` for one species.

## Forge specialization to the Hamming Schur layer
Use the seven Q192 route coordinates

`(49,12,125,48,116,59,95)`

as the seven labelled species slots and the binary `[7,4,3]` Hamming code as the full character/code layer.  Each nonzero Hamming codeword has an all-distinct common-center canonical atom on its support and is therefore formation-critical by v13.  The seven weight-three words are the support-minimal Fano atoms.

A naive selection among the 15 nonzero atoms has `2^15=32768` subsets.  The v13 join theorem makes the exact reachability quotient their binary span.  The four-dimensional Hamming space has exactly

`1 + 15 + 35 + 15 + 1 = 67`

subspaces, so the formation compiler reduces the architecture state space from 32768 selections to 67 exact `Theta` states, a factor `32768/67 ~= 489.075`.

For these canonical all-distinct states, `S=A=supp(C')`, so the state is determined by the selected subspace `C' <= C_Ham`.

## Spatial universality of every nonzero formation state
The Hamming code has minimum distance three, hence every nonzero subspace has route support at least three.  Wilson Forge v0.4 proved independently that every one of the 35 three-route subsets of Q192 generates the complete 152-dimensional Wilson commutant over `Q` (certified at two frozen primes).  Therefore every nonzero Hamming `Theta` state, regardless of its Schur dimension, has full Wilson spatial linear expressive closure.

This is the crucial separation of resources:

- formation/Schur dimension controls the number of central Fourier frequencies and legal nonlinear fusion channels;
- route support controls physical communication cost;
- Wilson spatial linear expressivity is already maximal for every nonzero state.

## Exact generalized-weight / hardware frontier
The subspace-support minima are the generalized Hamming weights of `[7,4,3]`:

`d_1,d_2,d_3,d_4 = 3,5,6,7`.

Because route 49 has valency 30 and the six C7 routes each have valency 60, the corresponding weighted minimum route degrees are

`150, 270, 330, 390`.

On 7392 Wilson states, one scalar route pass therefore needs at least

`1,108,800; 1,995,840; 2,439,360; 2,882,880`

directed edge visits for Schur-code dimensions `1,2,3,4`, respectively.  These carry `2,4,8,16` Fourier frequencies.  The minimizer counts are `3,15,6,1`.

Thus the Hamming/Theta layer supplies an exact hardware-capacity frontier while preserving the entire 152-dimensional Wilson spatial algebra at every nonzero point.

## Evidence boundary
The v13 group-theoretic normal form and criticality classification are imported from the nested v13 theorem package and its proof audit.  The 67-state Hamming quotient and weighted support profile are finite `F2` consequences independently recomputed in this Forge release.  Full spatial closure uses the already frozen 35/35 Wilson route-triple theorem.  The route/species identification is an engineering coupling, not a claim that the Wilson and formation groups are intrinsically the same object.
