# Ramanujan Wilson orbital-union family

## Statement
Let V=C[M22/A5] be the 7,392-state Wilson cap permutation module and H=End_{M22}(V), with its 152 orbital basis matrices A_0,...,A_151.  The identity orbital is 151.  The involution on H is matrix transpose; in the frozen relation convention X=A_49 is self-adjoint and the Paley order-seven operator Y is skew-adjoint, so the unsigned support of Y is a union of transpose-paired orbitals.

For each row below, let A be the sum of the listed orbital adjacency matrices.  Each list is transpose-closed, excludes the identity orbital, and has coefficient one on every listed orbital.  Therefore A is the adjacency matrix of a simple undirected regular graph on 7,392 vertices.

| Origin | Orbitals | Degree d | Certified max nontrivial | 2 sqrt(d-1) |
|---|---|---:|---:|---:|
| Q182 | 53,70,75,110 | 180 | < 26.611018139 | 26.758176321 |
| Q260 | 29,38,52,87 | 240 | <= 30 | 30.919249667 |
| Q262 | 29,52,53,75 | 240 | <= 30 | 30.919249667 |
| Q182 | 11,53,70,75,110,129 | 300 | < 33.403124238 | 34.583232932 |
| Q191 | 12,45,88,102,125,137 | 300 | < 33.166010489 | 34.583232932 |
| Q104 | 3,26,48,49,96,116,127 | 390 | < 39.360442678 | 39.446165847 |
| Q173 | 11,29,49,52,90,113,129 | 390 | < 39.125857677 | 39.446165847 |
| Q192 | 12,48,49,59,95,116,125 | 390 | < 38.478919033 | 39.446165847 |

Hence all eight graphs are Ramanujan.

## Why the 152-dimensional certificate controls the 7,392-dimensional spectrum
Over C,

H ~= direct_sum_lambda M_{m_lambda}(C)

with Wilson multiplicities m_lambda=(1,3,3,2,5,5,5,3,3,6).  If a in H has block matrices a_lambda, then right multiplication by a on the regular H-module has characteristic polynomial

prod_lambda det(t I_{m_lambda}-a_lambda)^{m_lambda}.

The action of the same a on V has characteristic polynomial

prod_lambda det(t I_{m_lambda}-a_lambda)^{dim V_lambda}.

The multiplicities differ, but the root set is identical.  It is therefore sufficient to certify all roots of the 152x152 right-regular multiplication matrix.  This is exactly what the frozen certificates do.

For each graph, the recomputation script forms the integer right-multiplication matrix from `BASE/cap_hecke_152.npz`, computes its exact characteristic polynomial over ZZ, factors it, isolates every real root in rational intervals, removes the unique trivial root d, and checks b^2 <= 4(d-1) for the largest absolute endpoint b.  The complete polynomial factors and rational isolating intervals are stored in `DATA/ramanujan_family_exact.json`.

The best normalized radius in the certified family is Q192:

rho <= 38.478919032176 / 390 < 0.098663895.

The standard L2-to-total-variation bound for a regular graph then gives, from a point mass,

TV(t) <= (1/2) sqrt(7391) rho^t.

Using the certified upper bound, t=8 already gives TV < 3.87e-7.  This is a theorem about the random walk on the explicit Wilson orbital-union graph, not a simulation estimate.

## Signed/unsigned twin
For Q192 the signed Paley operator has support

- negative: 12,48,59;
- positive: 95,116,125;

with transpose pairs (12,125), (48,116), (59,95).  The unsigned operator U192 uses all six routes with coefficient +1, while Y192 uses the same six routes with one sign bit.  The Ramanujan graph is X+U192, adding the order-three route A49.  Thus the same routed edge fabric has an unsigned expander mode and a signed Fourier/Paley mode.  This is the central practical bridge in v0.2.

## Evidence boundary
The eight graphs above are exact certificates.  The accompanying search numerically sieved 1,708 distinct transpose-closed subunions generated from the 271 characteristic-zero transport representatives and found exactly these eight candidates.  The eight survivors are certified exactly; the non-survivor count is retained as a numerical exhaustive search result, not promoted to a theorem of uniqueness because the other 1,700 characteristic polynomials were not all root-isolated exactly.
