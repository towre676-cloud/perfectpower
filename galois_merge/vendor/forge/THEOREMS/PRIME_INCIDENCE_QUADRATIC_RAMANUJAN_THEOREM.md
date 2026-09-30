# Prime-Incidence Quadratic Ramanujan Theorem

## Purpose
v0.2 certified the eight Wilson graphs by exact characteristic-polynomial factorization and rational root isolation.  That proves the spectral statement but does not identify the local geometric mechanism.  v0.3 replaces the positive side of that proof by a uniform degree-two path-positivity theorem inside the orbital algebra.  No eigenvalue root isolation is used by this certificate.

## Orbital algebra and augmentation line
Let A_0,...,A_151 be the orbital basis, with A_151=I, subdegrees k_i, n=7,392 and structure constants p_{ij}^r.  For a transpose-closed support S let

  a = sum_{j in S} A_j,
  d = sum_{j in S} k_j.

Let e0=J/n be the trivial central idempotent.  In the orbital basis e0=(1/n)sum_i A_i.  If R_a is right multiplication by a and P is the integer matrix n R_{e0}, then P=k 1^T, P^2=nP and R_a P=P R_a=dP.

The natural trace form on orbital coefficients is diagonal with D=diag(k_i).  Self-adjoint orbital unions satisfy

  R_a D = D R_a^T.

The nontrivial regular spectrum of R_a is therefore real and equals the root set of the nontrivial spectrum on the 7,392-state permutation module.

## Ramanujan slack element
Define

  Omega(a)=4(d-1)(1-e0) - (a-d e0)^2.

On the trivial line Omega(a)=0.  On a nontrivial eigenvector of a with eigenvalue theta it acts by

  4(d-1)-theta^2.

Therefore the graph is Ramanujan if and only if Omega(a) is positive semidefinite in the finite star algebra; it is strictly positive on the augmentation complement exactly when every nontrivial eigenvalue lies strictly inside the threshold.

The key point is that Omega(a) is a degree-two incidence-path expression.  Its coefficients use only products A_i A_j and hence only the intersection numbers p_{ij}^r, i.e. counts of length-two prime-incidence paths.  The characteristic polynomial is not part of the criterion.

## Exact integral form
Set S0=P and write R=R_a.  Clearing the e0 denominators gives

  Qhat = 4(d-1)(n^2 I - n S0) - (nR-dS0)^2.

Then Qhat D is an integer symmetric matrix.  The augmentation complement is x k=0.  Since k_151=1, an integral basis is

  b_i=e_i-k_i e_151,  i=0,...,150.

Let B be the 151 x 152 matrix with these rows and set

  M_a = B Qhat D B^T.

The graph is strictly Ramanujan whenever M_a is positive definite.  This is a finite exact quadratic path certificate.

## Eight-support theorem
For each of the eight frozen Wilson supports, exact fraction-free Bareiss elimination of M_a produces 151 positive leading principal minors.  By Sylvester's criterion each M_a is positive definite.  Therefore all eight Wilson orbital unions are Ramanujan without invoking their characteristic polynomials.

The certificates are frozen in DATA/ramanujan_quadratic_path_certificates.json and independently recomputed by scripts/certify_quadratic_path_slack.py.  The largest Bareiss pivot sizes are only about 1,923--2,199 bits after removing a common integral gcd from each form, so the proof is compact enough to rerun directly.

## Prime-incidence interpretation
Every frozen support is assembled from transpose pairs inside one C7 Paley support, with the three degree-390 cases additionally using the self-adjoint C3 route X=A_49.  If S_r=A_j+A_{j*} denotes a normalizer-paired C7 route and X0,S_{r,0} denote their trivial-line-centered versions, then the slack expands into self terms and anticommutators,

  4(d-1)(1-e0)
  - X0^2 - sum_r S_{r,0}^2
  - sum_r {X0,S_{r,0}}
  - sum_{r<s}{S_{r,0},S_{s,0}}.

Thus the Ramanujan property is not caused by each individual route already being a strong expander.  It is a transversality property of the short C3/C7 path algebra: the cross-route anticommutators reduce the worst nontrivial direction enough that the quadratic slack becomes positive.  For Q192 this is especially visible numerically: X alone has normalized nontrivial radius 1; its three C7 transpose-pair sums have approximate normalized radii 0.4000, 0.3056 and 0.2760; after all four prime-local pieces are combined the exact-certified radius is below 0.098664.  Those diagnostic component radii are not needed for the proof; the proof is the exact positive path form.

## What this does and does not prove
This theorem explains the positive Ramanujan certificates at the level of two-step prime-incidence geometry and replaces eight unrelated root-isolation arguments by one uniform positivity criterion plus eight integral path forms.  It does not yet prove that the eight supports are the only Ramanujan supports in the 1,708-object discovery census, nor does it provide a closed combinatorial classification of which C7 normalizer-pair selections make the slack positive.  That sharper classification remains a natural next theorem.
