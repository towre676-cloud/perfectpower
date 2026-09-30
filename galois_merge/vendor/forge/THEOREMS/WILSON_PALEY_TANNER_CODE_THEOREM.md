# Wilson-Paley Tanner Code Theorem

## Construction
For each of the eight certified Wilson Ramanujan orbital-union graphs G on n=7,392 vertices, let d be its degree and let B(G) be the bipartite double cover.  Thus B(G) has two parts L,R of size n, is d-regular, and has N=nd edges.  Put one symbol of F_397 on every edge of B(G).

The local code at every vertex is the ordinary Reed-Solomon evaluation code

C0 = RS_397[d, 2d/3, d/3+1]

with evaluation points 1,...,d in F_397.  All four Wilson degrees 180,240,300,390 are below 397, and each is divisible by three.  The package contains exact generator and parity-check matrices for all four local codes in DATA/LOCAL_RS/.  A global word is a codeword when the d incident edge symbols at every vertex lie in C0.  This is the unsigned Wilson Tanner code C+(G).

For a Wilson origin Q, every C7 orbital route in the support has its inherited Paley sign epsilon_j in {+1,-1}; the C3 route A49, when present, has sign +1.  At a vertex v, order the incident edges by outgoing orbital label and define Sigma_v to be the diagonal matrix of these signs.  Because transpose reverses the C7 Paley orientation, epsilon_{j*}=-epsilon_j on every C7 transpose pair, while the C3 block is fixed.  The signed code C-(G,Q) uses the local constraint Sigma_v x_v in C0 at every vertex.  Since 397 is odd, the two signs remain distinct.

## Rate theorem
The local code has k=2d/3 and d-k=d/3 independent parity equations.  There are 2n local constraint vertices and N=nd edge variables.  Hence

  dim C^(+/-) >= nd - 2n(d-k) = nd/3,

so every frozen Wilson-Paley code has rate at least 1/3.  This is a deterministic constraint-count lower bound; dependencies among vertex constraints can only increase the actual dimension.

## Distance theorem
Let lambda be an upper bound for the largest absolute nontrivial eigenvalue of G, and put rho=lambda/d.  The biadjacency matrix of B(G) is the adjacency matrix of G, so its second singular value is at most lambda.

Let z be a nonzero global codeword and S its nonzero edge support.  Let U subset L and W subset R be the vertices incident to S.  Because C0 has minimum distance Delta=d/3+1, every active local word has at least Delta nonzero coordinates.  Therefore

  |S| >= Delta |U|,   |S| >= Delta |W|,

and hence |S| >= Delta sqrt(|U||W|).  Since S is contained in E(U,W), expander mixing gives

  |S| <= e(U,W) <= d |U||W|/n + lambda sqrt(|U||W|).

Dividing by sqrt(|U||W|) yields

  sqrt(|U||W|)/n >= Delta/d - lambda/d.

Consequently

  |S|/(nd) >= delta0(delta0-rho),
  delta0 = Delta/d = 1/3 + 1/d.

The proof uses only the local MDS distance and the certified Wilson spectral bound.  It is unchanged by the Paley diagonal twists, because every Sigma_v is a monomial isometry and hence preserves local Hamming distance.

## Erasure stopping theorem
RS[d,k,Delta] corrects any Delta-1 erasures locally.  If an erasure pattern is a nonempty stopping set for the natural peeling decoder, every active vertex must meet at least Delta erased edges.  Repeating the distance proof gives the same lower bound

  |S_stop|/(nd) >= delta0(delta0-rho).

Therefore every erasure pattern smaller than the listed symbol-distance lower bound is decoded completely by iterative local erasure decoding.  This statement is algorithmic and monotone: every step recovers a locally solvable vertex and removes erasures, so no miscorrection issue occurs.

## Bounded-distance trapping theorem
The local RS unique-error radius is

  t=floor((Delta-1)/2)=d/6.

Call an edge set T a t-stall set when every incident vertex meets T in at least t+1 edges.  Put tau=(t+1)/d=1/6+1/d.  The same mixing argument gives

  |T|/(nd) >= tau(tau-rho)

whenever tau>rho.  This inequality is positive for all eight frozen Wilson graphs.  Thus a fail-only bounded-distance local decoder has no nonempty combinatorial fixed support below the certified stall threshold.  This is intentionally stated as a trapping/stall-set theorem, not as a claim that an arbitrary hard-decision schedule cannot miscorrect above local radius.

## Dual C3/C7 decoder
Unsigned mode runs the standard RS decoder on x_v.  Paley mode first multiplies by Sigma_v, runs exactly the same RS decoder, and multiplies back.  Thus the same local decoder core has identical local distance, error radius, erasure radius, global rate lower bound, global distance lower bound, stopping-set bound and t-stall bound in both modes.  The only difference is the Wilson normalizer-orientation sign frame on the C7 route blocks; the C3 block is untouched.

## Frozen parameter table

| Origin | d | N=7392d | dim >= | local RS | global d_min >= | unique global radius >= | t-stall size >= |
|---|---:|---:|---:|---|---:|---:|---:|
| Q182 | 180 | 1,330,560 | 443,520 | [180,120,61] | 86,147 | 43,073 | 5,588 |
| Q260 | 240 | 1,774,080 | 591,360 | [240,160,81] | 127,235 | 63,617 | 13,891 |
| Q262 | 240 | 1,774,080 | 591,360 | [240,160,81] | 127,235 | 63,617 | 13,891 |
| Q182 | 300 | 2,217,600 | 739,200 | [300,200,101] | 168,225 | 84,112 | 22,113 |
| Q191 | 300 | 2,217,600 | 739,200 | [300,200,101] | 168,815 | 84,407 | 22,411 |
| Q104 | 390 | 2,882,880 | 960,960 | [390,260,131] | 227,537 | 113,768 | 33,325 |
| Q173 | 390 | 2,882,880 | 960,960 | [390,260,131] | 228,120 | 114,059 | 33,619 |
| Q192 | 390 | 2,882,880 | 960,960 | [390,260,131] | 229,726 | 114,862 | 34,428 |

The global unique-error radius in the table is the information-theoretic radius floor((d_min_bound-1)/2), not a claim that the local iterative decoder achieves that radius in polynomial time.
