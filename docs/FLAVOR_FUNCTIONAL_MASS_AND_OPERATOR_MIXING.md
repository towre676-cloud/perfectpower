# Functional heavy masses, hierarchical light quarks and exact operator mixing

## The new result

A single Hermitian source can control a nonuniversal heavy mass without losing the neutral-scalar first-order determinant-phase cancellation. A globally positive even quartic mass function gives three hierarchical light states and three separated heavy states even when the source is traceless. This extends the earlier universal-heavy-mass construction; it does not contradict the earlier hierarchy exclusion, whose universal-mass hypothesis has changed.

The operator audit also makes the protection requirement exact. For the original two source singlets and ordinary adjoint in each sector, there are 28 dimension-five quadratic-source heavy-mass contractions across the two quark sectors. A sufficient 22-dimensional linear slice retains the cancellation; six opposite-sector adjoint coefficients are excluded. An allowed ordinary-channel cross quartic generates one excluded coefficient through an exact scalar-loop mixing tensor. With the normalization specified below, its contribution is 16 pi squared beta(kappa_cross) = 10 kappa lambda / 3. An independent 80-digit calculation confirms a finite first-order phase from a permitted opposite-sector operator.

The calculation constructs a larger protected interaction class and identifies its radiative boundary. It does not derive the source eigenvalues, Wilson coefficients, relative up/down frame, golden CKM relation, physical 66-degree angle or Sommerfeld constant.

## A canonical functional mass theorem

Let C be a Hermitian n-by-n source and let f be a real polynomial positive on its spectrum. Use canonical fermion metrics and the triangular Dirac matrix D = [[a I, 0], [C, f(C)]], with real a > 0. The full tree determinant is a to the power n times det f(C), which is positive. If f is even, the original shaping transformation C to minus C leaves the heavy mass unchanged and preserves the forbidden upper-right Higgs vertex. The photon determinant sum rule from a universal heavy mass changes: det f(C) now depends on the source eigenvalues.

Diagonalize C = U diag(h_i) U-dagger. Both fermion blocks are diagonalized by the same family matrix U. Each family then has the real two-state block [[a, 0], [h_i, f(h_i)]], so its left and right singular vectors are real. The exact squared masses are the two positive roots of z squared - [a squared + h_i squared + f(h_i) squared] z + a squared f(h_i) squared = 0. The smaller singular value is evaluated as a f(h_i) divided by the larger, avoiding hierarchical subtraction.

For a Hermitian scalar variation H = delta C, the derivative has entries delta f(C)_ij = d_ij H_ij in the source eigenbasis. For unequal h_i,h_j, d_ij = [f(h_i)-f(h_j)]/[h_i-h_j]; for coincident eigenvalues it is f-prime(h_i). Every d_ij is real and symmetric. The executable derivative uses the exact sum of words C to the power r, H, C to the power k-1-r, so no eigenvalue division occurs in the implementation.

After real two-state diagonalization, every off-family mass-basis vertex has the form G_IJ = b_IJ H_ij with real b_IJ. Its reverse vertex is b_JI times the conjugate H_ij. Therefore G_IJ G_JI is real. Diagonal entries are real as well. Adding the family-diagonal real Higgs vertex and mixing all real scalar coordinates by any real orthogonal mass-eigenmode transformation preserves these statements. Every neutral-scalar chirality-flipping first-order determinant-phase term vanishes separately, for arbitrary real spectral weights. In particular the finite B0 matching phase and its divergent coefficient vanish.

Polynomial interactions also have two-scalar/two-fermion seagull vertices. The mixed second derivative of a real Hermitian polynomial is Hermitian; contracting it with a real symmetric scalar covariance remains Hermitian. Its determinant trace is Tr[f(C) inverse delta M], which is real for Hermitian delta M. Hermitian source tadpole shifts leave the positive tree determinant real. These statements include the neutral one-loop seagull contribution to the first-order phase; the spectral receipt does not compute its real mass shift.

This is a neutral-scalar first-order theorem with canonical metrics and a shared source. It is not a theorem about arbitrary field-dependent kinetic operators, independent heavy-mass fields, genuine two-loop diagrams, the resummed determinant of a one-loop matrix or the full electroweak EFT anomalous dimension. The earlier higher determinant-phase counterexample continues to apply to claims extending first-order protection.

## An exact hierarchical spectrum with a traceless source

Take a = 1, C = diag(-10,-20,30) and f(C) = I/1000 + (C squared - 100 I) squared / 100000. The source trace is exactly zero. The heavy mass is bounded below by I/1000 for every Hermitian C, with no restriction to the benchmark eigenvalues. Expanded coefficients are 101/1000, -1/500 for C squared and 1/100000 for C to the fourth. The highest fermion operator has scalar degree four and mass dimension seven. The dimensional coefficients and all source centers are declared model inputs.

At the three source eigenvalues the heavy mass entries are 1/1000, 901/1000 and 6401/1000. Rational sign checks on each characteristic polynomial isolate the light masses in (0.00009,0.00010), (0.044,0.046) and (0.208,0.210). The heavy roots are strictly above 10, using the exact trace minus the upper light-root bound. Consequently there are exactly three states below 1 and three above 10, and the two successive light-mass ratios exceed 440 and 104/23. Numerical diagonalization gives light masses 0.0000995037185333, 0.0449484312553 and 0.208563676322, with heavy masses 10.0498756704, 20.0451934548 and 30.6908667553. The light ordinary-doublet weights squared are 0.990099010095, 0.997516275848 and 0.998984482843.

The finite-mass first-order test uses all nine Hermitian source directions and one Higgs direction, an explicitly seeded positive real scalar Hessian and source-variation coupling 0.001. The correction norm is below 0.001; the determinant trace vanishes to numerical precision, in agreement with the exact theorem. This avoids interpreting a large mass correction as a controlled perturbative benchmark. The scalar Hessian is a spectral test input, not a newly solved complete scalar vacuum. The positive polynomial is an EFT construction, not a supplied renormalizable UV completion or a naturalness estimate. Higher operators and matching coefficients require their own completion.

## Why the linear heavy-source coupling is unavailable

The original ordinary quarks are even and both heavy chiralities odd under the sector shaping sign. The real nonet and eta are odd. Their heavy-to-ordinary mixing is allowed, their insertion in the heavy mass is forbidden, and the Higgs coupling to the heavy right-handed triplet is forbidden. The tempting replacement f(C) = m I + k C violates this charge assignment.

There is a general ordinary-phase-charge implication. A constant heavy mass makes the two heavy chiralities have equal charge. A same-source heavy Yukawa then forces that source to have zero charge. Allowing its heavy-to-ordinary mixing makes the ordinary right-handed charge equal to the heavy one. The ordinary Higgs Yukawa therefore also permits the Higgs-heavy Yukawa. This implication is for additive Abelian phase charges and the displayed interactions. It is not an impossibility theorem for additional fields, a non-Abelian chiral assignment or a different interaction graph. Even functions of the odd source avoid this particular implication.

## The complete quadratic-source heavy-mass space on these fields

Each sector has two odd real singlets eta,s and one odd real ordinary adjoint A. A heavy triplet bilinear transforms as 1 plus ordinary 8. An exact character average over all 1,080 elements gives singlet multiplicity four and ordinary-adjoint multiplicity three in Sym squared of (2 times 1 plus 8). The seven independent CP-even contractions are eta squared I, s squared I, eta s I, Tr(A squared) I, eta A, s A and q(A) = A squared - Tr(A squared) I/3. Their explicit CP covariance with real coefficients saturates the unitary count.

Both a same-sector square and an opposite-sector square are even under both shaping signs. Mixed up/down degree-two products are odd under each and are forbidden. There are therefore 14 contractions for each heavy quark sector, or 28 across the two. This is the complete quadratic-source heavy-mass count for these original source fields and bilinears, not a census including all mediator fields, Higgs covariants, kinetic terms or higher scalar degrees.

The seven same-sector contractions give a heavy matrix m0 I + m1 A + k A squared, with real singlet-dependent m0,m1. It commutes with C = z I + g A. Its adjoint off-diagonal derivatives have the same real factor for all scalar directions. The four opposite-sector singlet contractions add a real scalar multiple of I and retain the theorem. Thus setting the three opposite-sector adjoint coefficients per heavy sector to zero gives a sufficient 22-dimensional linear protected slice, conditional on positive heavy masses. This is not a classification of all exceptional nonlinear cancellations or aligned backgrounds outside that slice.

The opposite-sector eta A, s A and q(A) contractions are permitted and generically do not commute with the local source. Ordinary phase charges on the real sources cannot forbid q(A_down) while permitting the same-sector source square. The earlier finite representation projectors do not by themselves remove this ordinary-adjoint fermion operator.

## An exact scalar-loop generation test

Normalize eight canonical adjoint generators by Tr(B_a B_b) = delta_ab. Define the cross interaction Vcross = lambda Tr[q(A_up) q(A_down)] and the dimension-five mass insertion kappa bar(U_up,L) A_up squared U_up,R / Lambda plus its Hermitian conjugate. Treat the external fermion bilinear as one insertion in the scalar Hessian. The cross term of the scalar potential beta functional beta V = Tr(H squared)/(32 pi squared) then contracts the two adjoint indices through

S(X) = sum_ab {B_a,B_b} Tr[{B_a,B_b} X] = (10/3) X + (22/9) Tr(X) I.

The implementation proves this identity for a general Hermitian three-by-three X with nine real symbolic coordinates, using an unnormalized rational/imaginary basis and exact inverse norm factors. Its traceless eigenvalue is 10/3; its singlet eigenvalue is 32/3. No rational reconstruction from floating-point samples is used.

Since q(A_down) is traceless, the generated operator is kappa_cross bar(U_up,L) q(A_down) U_up,R / Lambda plus its Hermitian conjugate, with scalar-loop contribution 16 pi squared beta(kappa_cross) = 10 kappa lambda / 3. Nonzero kappa and this ordinary-channel lambda therefore regenerate an excluded coefficient even when it vanishes at the matching boundary. A pure singlet portal generates only a scalar multiple of I in this contraction and does not produce this adjoint obstruction. The finite channels require their own running and matching; the existing quartic closure census must still be imposed on a proposed restriction of lambda.

This is an exact one-loop scalar insertion tensor and a nonzero contribution to operator mixing. Fermion, gauge, wavefunction and other dimension-five diagrams have not been summed into a full EFT anomalous-dimension matrix. An enlarged completion might cancel the contribution through independently justified relations. Merely setting the generated operator to zero supplies no such relation.

## A permitted opposite-source threshold

The deterministic example has C_up = diag(0.4,0.7,1.1), a = 0.2, and M_up = I + 0.07 B_down squared. The traceless Hermitian B has diagonal (0.2,0.5,-0.7), upper entries (0.13 i,0.1,0.17) and conjugate lower entries. Its invariant cycle has imaginary part 0.00221. The heavy mass is positive with minimum eigenvalue above 1.0018, while the commutator of C_up and M_up is nonzero.

The real scalar modes contain a Higgs vertex, a same-sector real off-diagonal source variation and the opposite-sector heavy-mass derivative 0.07 {B,T}, with T = diag(1,-1,0). The stated positive three-mode scalar Hessian has eigenvalues 0.7261692150, 0.8980019338 and 1.4758288512. The tree determinant phase is zero, but the maximum imaginary paired vertex product is approximately 0.000640094. The physical finite B0 first-order determinant phase is 6.61324288010 times ten to the minus eight, with correction norm 0.000324364. An independent 80-digit weak-basis DD-dagger functional-calculus trace reproduces it without the numpy Dirac SVD. Its divergent phase coefficient vanishes; the obstruction here is a finite threshold.

An additional exact rational resolvent calculation gives a nonzero first-order trace for the same source/operator data and explicitly specified rational scalar mixing. That is a kernel-independent failure of termwise paired reality, not a replacement of B0 by a physical propagator. This example does not claim a solved CP-even invariant scalar vacuum or an all-diagram strong-CP threshold. It establishes why the shared-source theorem cannot be applied to the complete permitted operator space without an additional mechanism.

## What remains free at fixed full fermion spectra

For each sector, unitary conjugation of C conjugates f(C) and preserves all six fermion masses and their ordinary-doublet weights. The light charged current is diag(q_up) U_up-dagger U_down diag(q_down). Varying the relative source eigenframe therefore varies physical mixing without changing either full spectrum. The executable four-angle chart has rank-four response for the observables absolute Vus, absolute Vcb, absolute Vub and the quartet CP invariant, with Jacobian determinant approximately 1.14172 times ten to the minus five. The chosen chart point is only a freedom test.

The constructive hierarchy and phase theorem supply an attainable protected EFT slice. They do not select its relative frame. A successful next interaction must justify the absence or correlation of opposite-sector adjoint insertions and their scalar-loop regeneration, while selecting the two source eigenframes and retaining canonical matching. The exact mixing tensor is a direct test for such a claim; the current calculation does not assert that the task is completed by polynomial functional alignment alone.

## Reproduction

Run PYTHONPATH=python OPENBLAS_NUM_THREADS=1 python python/develop_flavor_functional_mass.py. The deterministic JSON receipt includes exact rational root intervals, the full character average, the exact tensor identity, complete six-state matching, neutral-scalar thresholds, the independent high-precision trace and the fixed-spectrum orientation response. Focused tests cover complex noncommuting derivatives, degenerate source eigenvalues, positive heavy spectra, shaping charges, seagull reality, the permitted opposite-source threshold and exact scalar operator mixing. The validation receipt records adjacent flavor tests, a fresh extraction and byte-identical scientific replay. The cumulative flavor monograph incorporates this chapter and the concurrently merged continuous polynomial decay bounds.
