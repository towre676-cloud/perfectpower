# Certified period matrices of genus-two curves with complex branch points

The certified periods chapter covered split curves whose six branch points are real. Its scope statement left three things open: complex branch-point configurations, automatic cycle marking for general sextics, and quintic models. This chapter closes those three for curves y^2=f(x) where f has rational coefficients and degree 5 or 6, and the roots may be real, conjugate pairs, or anything else.

- **Periods.** Every period is an Arb ball with a proven radius.
- **Cycle basis.** The A/B basis is constructed from the branch-point configuration alone. Its intersection matrix is computed exactly.
- **Riemann relations.** These are certified for every curve treated.
- **Cross-checks.** Four independent cross-checks tie the new periods to the existing receipt, to two curves with extra automorphisms whose Omega is pinned down exactly, to a change of arc, and to Moebius changes of coordinate.

## Model and branch points

For a rational sextic f, `fmpz_poly.complex_roots` isolates the six simple roots. It is rigorous, and real roots come back with exactly zero imaginary part.

A quintic is first converted by a rational Moebius map x=(a t+b)/(c t+d) with f(a/c)≠0:

```text
Y^2 = g(t) = (c t+d)^6 f((a t+b)/(c t+d)),   Y = y (c t+d)^3,
(dx/y, x dx/y) = G (dt/Y, t dt/Y),  G = (ad-bc) [[d, c], [b, a]].
```

The conversion is exact, using Fractions. The point t=-d/c, the image of infinity, becomes a finite branch point. All periods are reported for the original forms dx/y and x dx/y by applying G.

## Arc, global branch and cycles

1. **Arc.** Order the roots e_1,...,e_6. The default is lexicographic by (Re, Im), which gives a monotone polyline; (Im, Re) is the alternative. Join consecutive roots by straight segments s_j=[e_j,e_{j+1}]. `simple_arc_certificate` proves in Arb that L=s_1∪...∪s_5 is a simple arc:
   - non-adjacent segments are disjoint, certified by separated bounding boxes or by strict orientation signs;
   - adjacent segments meet only at their common vertex, certified by a strict turn or a positive forward dot product.

   A self-crossing order is rejected, and a test covers this.
2. **Global branch.** With m_k and h_k the midpoint and half-vector of s_k, put

   ```text
   F_k(z) = h_k G((z-m_k)/h_k),  G(w) = w sqrt(1-1/w^2)  (principal),
   Y = sqrt(lc) F_1 F_3 F_5.
   ```

   F_k is analytic off s_k with F_k^2=(z-e_k)(z-e_{k+1}). So Y is a single-valued square root of f on the complement of L; infinity is not a branch point of a sextic.
3. **Cycles.** gamma_j is the closed lift of the loop around s_j that runs along the left side of s_j (left with respect to e_j→e_{j+1}) with y=Y_+. Its period is

   ```text
   P_j(omega) = 2 int_{s_j} omega / Y_+ .
   ```

   For real roots this is exactly the y_u convention of the earlier chapter.
4. **Local branch on a segment.** With z=m+h u and u=-cos t,

   ```text
   y_j = i h sqrt(1-u^2) S_j(u),
   S_j = sqrt(lc) h^2 prod_k sqrt(-d_k) sqrt((u-u_k)/(-d_k)),
   u_k = (e_k-m)/h,   d_k = u_k - (nearest point of [-1,1]).
   ```

   Each principal cut is the ray from u_k pointing away from the segment, so S_j is analytic on a neighbourhood of [-1,1]. Since dz/y_j=-i dt/S_j(u(t)) has no endpoint singularity, `acb.integral` (with analytic sqrt flags) returns rigorous enclosures.
5. **Sheet certificate.** Y_+ and y_j are continuous square roots of f along the open segment, so Y_+=s_j y_j with s_j=±1 constant. The sign s_j is certified at the midpoint. There Y_+(m) is explicit: the cut factor F_j contributes its left boundary value h G_+(0)=i h, and the other F_k are analytic at m. A sign is accepted only when the ratio ball contains exactly one of ±1.

## Theorem 1 (exact intersection matrix)

For any certified simple arc, gamma_j·gamma_{j+1}=+1 and all other gamma_i·gamma_k vanish (i<k).

Proof.
1. Schoenflies gives an orientation-preserving homeomorphism of the sphere that carries L onto [1,6], with e_j→j, the left side to the upper half plane, and Y to ± the branch whose cuts are [1,2], [3,4], [5,6]. Intersection numbers are invariant, and so is a global sign.
2. `model_intersection_matrix` evaluates the model exactly, in rational arithmetic:
   - gamma_j is the clockwise rectangle around [j,j+1], with heights alternating between 1/2 and 1/4 so that every crossing is transversal;
   - the sheet starts at + on the top edge and flips at each crossing of a cut, and the code checks that every lift closes;
   - two lifts meet only at planar crossings where their sheets agree, and each such meeting counts sign det(t_1,t_2).

The result is the chain matrix with sigma=+1. This exactly matches the earlier chapter's orientation, which there was fixed only indirectly by Riemann positivity.

A generic integral symplectic reduction (`symplectic_basis`, a Gram–Schmidt for alternating unimodular forms over Z) then produces

```text
a1 = gamma_1,  a2 = gamma_1 + gamma_3,  b1 = gamma_2,  b2 = gamma_4,
```

with T C T^t = J verified exactly. The relation gamma_1+gamma_3+gamma_5=0 (in homology) is certified on periods for every curve: the ball contains 0.

## Theorem 2 (certified Riemann relations)

For every curve below, with A and B the period matrices of (dx/y, x dx/y) over (a1, a2) and (b1, b2), Omega=A^{-1}B is computed in Arb. The ball Omega_12-Omega_21 contains 0, and tr Im Omega>0 and det Im Omega>0 hold rigorously. Hence Omega lies in the Siegel upper half space.

## Theorem 3 (Sp(4,Z) certificates)

Given two period packets Pi_1 and Pi_2 (2×4) that span the same lattice, `integral_relation` solves the real 4×4 ball system Pi_2=Pi_1 M. It then certifies that each entry interval has width less than 1 and contains exactly one integer, and checks M^t J M=J exactly. It also confirms that the Omega obtained from Pi_1 M overlaps Omega_2 entrywise. For an automorphism acting on the forms by a diagonal D, the same routine is applied to D·Pi.

## Results (200 bits; all Omega radii ≤ 2×10^-55; integer-entry radii ≤ 3×10^-55)

| check | curve | outcome |
|---|---|---|
| (a) reproduce real case | (x²-1)(x²-4)(x²-9), (x²-2)(x²-3)(x²-7) | all 10 cycle periods equal the existing ones within balls (difference ≤ 3.7×10^-58); Omega in the existing basis matches; auto basis ↔ existing basis by M=[[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,-1,1]], symplectic |
| (b) automorphism of order 6 | x⁶-1 | Omega=[[-1+i√3/2, 1/2],[1/2, -1+i√3/2]]; action of (x,y)→(ζ₆x,y): M=[[1,-1,-2,1],[-1,1,1,-2],[1,0,-1,0],[0,1,0,-1]], symplectic, charpoly x⁴+x²+1, M⁶=I |
| (b) automorphism of order 8 | x⁵-x (Bolza), via x=(2t+1)/t | Omega=[[1/2+i/√2, -1/2],[-1/2, 1/2+i/√2]]; action of (x,y)→(ix,ζ₈y): M=[[0,0,-1,0],[0,-1,1,-1],[1,0,1,-1],[0,1,-1,0]], symplectic, charpoly x⁴+1, M⁸=I |
| (c) two conjugate pairs + real pair | (x²-2)(x²+1)(x²+2x+5) | Omega≈[[-1.31446+0.75366i, 0.57704+0.01168i],[·, -0.71631+0.76577i]], tr Im=1.519439060709…, det Im=0.577000591754…; (Im,Re)-ordered arc gives an Sp(4,Z)-equivalent Omega |
| (d) Moebius x=(t+1)/(t-2) | curve (c) | M=[[0,1,2,-2],[0,0,-1,0],[0,1,1,-1],[1,1,0,0]], symplectic, Omega transforms correctly |
| (d) Moebius x=(t+2)/(3t+4) | x⁶-1 | M=[[-1,0,2,0],[0,1,0,-2],[-1,0,1,0],[0,1,0,-1]], symplectic |
| (d) two quintic charts x=1/t and x=(3t+1)/(t-1) | x⁵-x+1 | M=[[0,-2,1,-1],[1,1,0,0],[0,-1,1,-1],[0,0,1,0]], symplectic |

**Closed forms.** For x⁶-1 and the Bolza curve, sympy solves the fixed-point equations (M_11+W M_21)W=M_12+W M_22 for symmetric W exactly. Each system has four solutions, and exactly one of them lies in Siegel space: the closed form in the table. The certified Omega ball contains that algebraic point. Omega is itself a fixed point, because M is the action of a genuine automorphism and is the unique integer matrix inside the certified intervals. Hence Omega equals the closed form exactly, given sympy's complete solution of a zero-dimensional polynomial system.

**Negative control.** Deliberately flipping the certified sheet sign on a single segment of curve (c) breaks the certificates:
- On segments 1–4 the lattice stays integral, since a sign flip preserves the lattice, but M^t J M≠J and Riemann positivity is no longer certified.
- On segment 5, which is not in the basis, Omega is unchanged but gamma_1+gamma_3+gamma_5=0 fails.

The sheet bookkeeping is therefore load-bearing, not cosmetic.

## Scope and what is not claimed

- **Claimed:** the curves listed have certified periods, Omega with certified Riemann relations, and certified integral symplectic relations between the listed models and arcs.
- **Requirements:** coefficients must be rational. Degree-5 input needs a user-supplied Moebius map with f(a/c)≠0.
- **Not claimed:**
  - Arbitrary algebraic coefficients.
  - Robustness when a straight segment passes extremely close to another branch point. The certificate then fails or slows down; it never returns a wrong answer.
  - A machine-checked proof of the Schoenflies transport step in Theorem 1. It is a standard topological argument; the model computation itself is exact.
  - The literature normalisation of the Bolza or x⁶-1 period matrices. Only the forms above, in the bases constructed here, are claimed.
  - The exact closed forms rest on sympy's polynomial solver for the uniqueness step. Everything else in that argument is Arb-certified or exact integer arithmetic.
  - Siegel reduction and Abel–Jacobi maps.

## Reproduction

```sh
pip install python-flint sympy
export PYTHONPATH=python
python python/develop_genus2_complex_periods.py
python -m unittest discover -s python/tests -p 'test_genus2_*periods.py'
```

The receipt is receipts/curve_structure/genus2_complex_periods.json. It is byte-identical across runs and takes about 14 s on one core. Seven tests cover:

- the model intersection matrix and the symplectic reduction;
- the exact Moebius model;
- reproduction of the real case;
- the x⁶-1 closed form and its automorphism;
- the conjugate-pair curve with an arc change and the negative control;
- the quintic chart consistency;
- rejection of a self-crossing arc.

References: Molin and Neurohr, "Computing period matrices and the Abel–Jacobi map of superelliptic curves", Math. Comp. 88 (2019), the spanning-tree/segment approach in Arb; Bolza (1887) for y^2=x^5-x; Johansson, rigorous numerical integration in Arb (2018).
