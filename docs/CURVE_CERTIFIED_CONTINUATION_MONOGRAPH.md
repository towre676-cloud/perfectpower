# Certified continuation on curves: the 36 open boxes and the Legendre connection

This chapter closes two curve-geometry items left open by the connected-closures and curve-families chapters. The first is the line "108 closed metric boxes out of 144 leave 36 unresolved boxes". The second is "rigorous interval continuation" of family connections, together with the positive-resonance Legendre chart and its singular endpoints. Every result below is either an exact rational identity or an Arb ball with a proven radius. Nothing here is checked in Lean.

## Part A. The 36 unresolved boxes

### What the boxes are

The 144 cases are not tangent-metric density boxes. All eight `compare` packets in `develop_metric_boxes.py` (genus 1–4, branch and infinity charts) and the finite elliptic chart were already complete. The 144 count is the **affine-face corpus** that the same script builds and stores in `receipts/metric_boxes/affine_faces_corpus.json`:

```text
F = y^d - x^p = 0,   G = a*y - x = 0,   d in 2..7, p in 2..9, a in {1, 2, -1},
box [0,1] x [-10^100, 10^100].
```

`bernstein_boxes.solve_affine_faces` eliminates y through G. It computes the exact remainder R(x) = F(x, x/a) = (x/a)^d - x^p with Q*G + R = F. It then asks Bernstein zero-strata to certify the **face-only property**: R has one weak Bernstein sign on the box, and every zero lies on the faces x=0 or x=1. When the property holds, the integer models are read off the faces. The 36 incomplete cases are those where the strata were mixed-sign or included an interior stratum.

### Why they stayed open

The cause is structural, not a lack of subdivision depth. Every one of the 36 systems has a real zero in the open box, so no Bernstein refinement at any depth could certify the face-only property.

* 9 cases have R ≡ 0: a=1 with d=p, or a=-1 with d=p even. The whole graph y=x/a solves the system. The tensor is all zeros, so the "interior" stratum is present.
* 27 cases have a=2 and p>d. Then R = x^d(2^-d - x^(p-d)) changes sign at the interior root x* = 2^(-d/(p-d)), and the Bernstein coefficients are mixed.

### Refined method (`perfectpower/metric_boxes_refined.py`)

`refine(equations, box)` reuses the exact elimination identity and decides the property instead of refining tensors.

1. **R ≡ 0.** The exact rational point x0=(xa+xb)/2, y0=-B(x0)/a lies strictly inside the box and makes every equation vanish exactly. This counterexample needs no ball. The real zero set is the graph, and the integer models are enumerated over integer x in [xa,xb].
2. **R ≠ 0.** Take the squarefree part, its primitive-integer Sturm chain and bisection with exact rational endpoints. This finds every distinct real root in [xa,xb], either as an exact rational bisection point or in an isolating open interval of width ≤ 2^-40 with an exact sign change. The Sturm count gives existence, uniqueness and completeness. For each interior root, `newton_ball` runs Arb interval Newton at 192 bits. Proof holds when the Newton image falls strictly inside the iterate with p' excluding 0, and the resulting ball is about 10^-41 wide. The point (x*, x*/a) lies in the open box because the exact y-interval over the isolating interval does.
3. **Integer models.** These are the integer exact roots plus any integer k in an isolating interval with R(k)=0, checked against all equations.

The face-only property is unchanged. It is certified **false** whenever an interior real zero exists. It is certified **true** by the Sturm route when no interior root exists. A test covers x^2-x+3/10: its Bernstein coefficients are mixed, but it has no real root, so the property holds. `verify(packet)` recomputes the packet exactly, rechecks the identity Q*G+R=F, and rechecks the witness: the exact point, the exact rational root, or the sign change at the isolating endpoints.

### Results (receipt `receipts/curve_structure/affine_faces_refined.json`)

| outcome | cases | witness |
|---|---|---|
| originally complete (unchanged) | 108 | Bernstein face strata |
| face-only property certified FALSE, R ≡ 0 | 9 | exact rational interior point (1/2, ±1/2) |
| face-only property certified FALSE, exact rational interior root | 12 | e.g. x*=1/4 for (d,p,a)=(2,3,2), exact |
| face-only property certified FALSE, irrational interior root | 15 | Sturm interval + interval-Newton Arb ball |
| still unresolved | **0** | — |
| complete integer models, agreeing with brute force | 36/36 | Sturm / exact graph identity |

So all 36 boxes are resolved. None becomes a "closed box" in the original sense, because each provably violates the property the original 108 satisfy. All 36 now have a certified complete integer-model list ([[0,0],[1,1]] for a=1, [[0,0],[1,-1]] for a=-1 and [[0,0]] for a=2), matching the earlier brute-force check. As an independent algebraic identification, every isolated root satisfies lo^k < 2^-d < hi^k with k=p-d on its isolating interval, checked exactly.

## Part B. Certified continuation of the Legendre Gauss–Manin connection

### The system

Take y^2 = x(x-1)(x-t) with period vector Y = (∫_γ dx/y, ∫_γ x dx/y). `curve_families` gives the connection Y' = A(t)Y. `from_family` turns it into exact partial fractions and checks the identity at four rational points:

```text
A(t) = R0/t + R1/(t-1),
R0 = [[0,-1/2],[0,0]]          (nilpotent: exponents 0,0, logarithmic),
R1 = [[-1/2,1/2],[-1/2,1/2]]   (nilpotent: exponents 0,0, logarithmic),
R_inf = -(R0+R1) = [[1/2,0],[1/2,-1/2]]   (exponents +1/2,-1/2: POSITIVE RESONANCE, gap 1).
```

### Certified regular steps

`FuchsianSystem.taylor_step(c, h)` works at a Gaussian-rational centre c. It computes the Taylor coefficients of the fundamental matrix with Y(c)=I from q(c+z)Y' = M(c+z)Y, where q = ∏(t-a_k) and M = Σ R_k ∏_{l≠k}(t-a_l), using Arb matrices. Write ρ = min|c-a_k| and κ = Σ||R_k||∞ ≥ ρ·Σ||R_k||/|c-a_k|. Then A(c+z) is majorized by (κ/ρ)/(1-z/ρ). By the Cauchy majorant argument, ||Y_n|| ≤ (κ)_n/n! ρ^-n. With x = |h|/ρ ≤ 1/3, the tail from order N is bounded by

```text
T_N/(1-θ),   T_N = (κ)_N/N! x^N,   θ = max(1,(κ+N)/(N+1))·x < 1,
```

and this bound is added as a complex error disc to every entry. Each straight segment is cut into k equal steps with 9|h|^2 ≤ dist(segment, poles)^2, checked exactly in rationals. Orders are raised until the tail is below 2^-120. `certified_transport(family, path)` packages this as an Arb-certified analogue of `family_continuation.transport`, for any family whose connection has simple rational poles. On the loop around 0 it agrees with the numerical DOP853 transport to 1e-8, with ball radius 4.2e-28.

### Frobenius bases at 0, 1, ∞, including the positive resonance

In a chart s (s=t at 0, s=1-t at 1, s=1/t at ∞), the system reads sY' = (R + E s/(1-σs))Y, with σ=1 and E = -R1, -R0, -R1 respectively. Put F = E-σR. For Y = s^ρ Σ s^n(y_n + z_n log s), the exact block recurrence is

```text
((n+ρ)-R) z_n = (F+σ(n-1+ρ)) z_{n-1}
((n+ρ)-R) y_n = (F+σ(n-1+ρ)) y_{n-1} + σ z_{n-1} - z_n .
```

All coefficients are exact rationals. The cases are as follows.

* **Nilpotent residue (0 and 1).** Y1 has y_0 = R·w and no log; Y2 has y_0 = w and z_0 = R·w. The log series of Y2 equals Y1 exactly.
* **Positive resonance (∞, gap m=1).** Y1 = s^{1/2}Σ y_n s^n is seeded by the +1/2 eigenvector v. Y2 is seeded by the -1/2 eigenvector u. At n=m the block (1/2 - R) is singular. The right-hand side b is decomposed exactly as b = β_u u + β_v v. The log coefficient is c = β_v, and y_m = (β_u/m)u, with the v-component normalized to 0. The receipt gives **c = -1/2 ≠ 0**, so a log-free exponent -1/2 solution is impossible. The code checks that the whole log series equals c·Y1 shifted by m, and the tests replay the differential equation coefficient by coefficient. Up to the seed sign, the z-series equals the formal jet of `resonant_frobenius('infinity', exponent='-1/2', seed=[0,1])`.

**Tail bound.** For n ≥ N with n+ρ > ||R||, Neumann's lemma gives ||((n+ρ)-R)^-1|| ≤ d_n = 1/(n+ρ-||R||). Hence ||z_n|| ≤ q_n||z_{n-1}|| with q_n = (||F||+|σ|(n-1+ρ))·d_n. Also ||y_n|| ≤ q_n||y_{n-1}|| + d_n(|σ|+q_n)||z_{n-1}||. Because q_n is a Möbius function of n with limit |σ| ≤ 1, q_n ≤ q̄ = max(q_N,1). So w_n = ||y_n||+||z_n|| ≤ Q̄ w_{n-1} with Q̄ = q̄ + (1+q̄)·max(|σ|,1)·d_N, and

```text
Σ_{n≥N} w_n r^n ≤ w_{N-1} r^{N-1} Q̄r/(1-Q̄r)      (Q̄r < 1),
```

an exact rational. At s=1/2 and order 120, the tails are 2e-39 to 8e-39. Local monodromy for one counterclockwise turn of s is Φ → ΦK, with K = e^{2πiλ}[[1, 2πi c],[0,1]]. Here K = [[1,2πi],[0,1]] at 0 and 1, and K = -[[1, -πi],[0,1]] at ∞.

### Periods and integrality

At t0 = 1/2, Π = [P_A, P_B]. The first row is (2πF(t), 2πiF(1-t)) with F = ₂F₁(1/2,1/2;1;·), evaluated by Arb's rigorous `hypgeom_2f1`, using the classical Euler integrals. The second row is 2t(t-1)f' + tf, read from row 0 of the connection. Every loop transition T gives N = Π^{-1} T Π. **Integrality premise:** monodromy acts on H_1(E_t, Z), and (A,B) is a Z-basis; this is a topological fact, not inferred from closeness. Given the premise, a ball with every radius below 1/2 fixes the integer matrix uniquely, via `arb.unique_fmpz`.

### Results (receipt `receipts/curve_structure/legendre_certified_connection.json`, 192 bits)

| loop (base 1/2) | Taylor steps | max entry radius of N | N (cycle basis) | Frobenius certificate |
|---|---|---|---|---|
| γ0: square through ±1/2, ±i/2, ccw around 0 | 24 | 1.2e-33 | [[1,2],[0,1]] | Φ0 K Φ0^-1: same N, radius 6e-37 |
| γ1: square through 1/2, 1∓i/2, 3/2, ccw around 1 | 24 | 1.3e-32 | [[1,0],[-2,1]] | Φ1 K Φ1^-1: same N, radius 1.5e-36 |
| outer: up to 2, ccw square |t|=2, back | 60 | 6.8e-30 | [[1,2],[-2,-3]] | transported Φ∞ K^-1 Φ∞^-1 (positive-resonance chart): same N, radius 2.1e-31 |

* N0 and N1 are exactly the standard generators [[1,2],[0,1]] and [[1,0],[-2,1]] of Γ(2) (up to sign and inverse; Γ(2) = ±⟨N0, N1⟩ classically). All three matrices have determinant 1 and are ≡ I mod 2.
* The exact integer relation N_outer = N1·N0 holds: γ0 followed by γ1. N_outer has trace -2. This is the -1 times unipotent monodromy forced by the resonant chart at ∞, whose log coefficient c=-1/2 makes the Jordan block nontrivial.
* The Taylor-path and Frobenius certificates are computed independently and give the same integer matrix for all three loops.
* det Π(1/2) is a ball around 8πi of radius 4e-29. tr A = 0 makes det Π constant (Legendre's relation), so this checks the normalization.
* The period coordinates of the Frobenius bases are consistent with closed forms, checked by ball overlap only and not as a proof: C0 = [[-4π, -16i log 2],[0, 4i]], C1 = [[8-16 log 2, -4πi],[4,0]], C∞ = [[-2π-8i log 2, -8i log 2],[-4i,-4i]]. Certified connection matrices between the singular-point bases (0→1, 0→∞, 1→∞) are in the receipt. Their radii are below 1e-32.

For comparison, the earlier marked computation used 148 order-24 steps around 0, with a row enclosure of about 2e-9.

## Scope and not claimed

* Part A decides the face-only property and the integer models only for the stated systems and boxes. It is exact Python and Arb, with no Lean kernel replay. The interior zero sets are described as the graph or the isolated points; no Bernstein-tensor certificate is produced for them, because none can exist.
* Part B covers connections with simple rational poles for transport, and 2×2 residues with rational eigenvalues for Frobenius charts. Legendre's three charts are the executed instances. General higher-rank resonances, irregular singularities, algebraic poles and log degree above 1 are not implemented.
* These identifications are classical and not formalized: the Euler period integrals, the topological integrality premise, the Γ(2) generation theorem, and the closed forms for C0, C1, C∞ and 8πi. The closed forms are checked only by ball overlap.
* Precision is Arb's and the code is Python. No Lean statement and no physical interpretation is asserted. Higher-genus marked continuation and complex-branch-point markings remain open.

## Reproduction

```text
cd python
python3 develop_curve_certified_continuation.py      # ~2 s; byte-identical receipts
python3 -m unittest tests.test_curve_certified_continuation tests.test_metric_boxes \
        tests.test_legendre_endpoint tests.test_curve_families
```

The script writes `receipts/curve_structure/affine_faces_refined.json`, `legendre_certified_connection.json` and `certified_continuation_summary.json`, which records the sha256 of the first two. It needs python-flint (Arb). Two consecutive runs give identical hashes.
