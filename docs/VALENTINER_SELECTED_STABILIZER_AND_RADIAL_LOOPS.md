# Complete selected Valentiner stabilizer and the one-loop radial calibration

## Abstract

The positive norm/Gram completion selects exactly 1,080 global link vacua, rather than merely a finite set containing the previously enumerated group. The missing upper bound follows by applying Harui's smooth-plane-sextic automorphism theorem to the exact source polynomial. Separately, an explicitly specified nine-chiral-field effective theory yields closed off-shell scalar and fermion spectra and an exact one-loop supertrace. The supersymmetric selected tadpole cancels; the hard scalar interactions used for frame selection regenerate a radial calibration counterterm. Exact massive-coordinate elimination also extends three specified null-ray checks through degree twelve in the effective superpotential. These results close the selected-frame census and calculate a quantum stability boundary. They do not derive a CKM relation or physical CP selection.

## Complete selected global vacuum set

Use the previous superpotential W=a det K+b I6bar(K)+c(det K)^2 and selector V=VF+lambda(N-3v^2)^2+eta G, where N=Tr(Kdagger K), G=Tr((Kdagger K-NI/3)^2), lambda,eta>0, bc>0 and a is real and nonzero. Set D0=-a/(32b+2c), r^3=D0 and v=|r|. The established tensor Cauchy-Schwarz equality argument identifies every zero-energy global minimum as K=rU with U in the SU(3) stabilizer of the conjugate sextic tensor. All terms are nonnegative, and known group elements attain zero.

The source-critical-locus calculation is replayed exactly over Q(sqrt(5),sqrt(-3)). Cyclic reduction covers all coordinate supports: the full-support gradient ideal has Groebner basis [1], the two-support resultant is nonzero, and the one-support derivative is 3. Consequently the projective sextic is smooth, of genus ten. Euler's identity identifies projective singularities with nonzero simultaneous gradient zeros.

Harui, Theorem 2.5, bounds the automorphism group of any smooth complex plane sextic by 360. The exceptional maximal curve is the smooth Wiman sextic with group A6; the ordinary bound is 216. Our exactly generated subgroup has order 1,080 and precisely three scalar elements. Exact central cosets give a faithful projective image of order 360. Every SU(3) tensor stabilizer element induces a projective curve automorphism, with kernel contained in the three scalar cube roots of unity. Therefore its order is at most 3*360=1,080. The known subgroup attains this bound, so the full stabilizer equals that subgroup, and the selected global minimum set has exactly 1,080 elements. Harui's uniqueness statement also identifies the projective source curve with the smooth Wiman sextic up to projective equivalence, without requiring a coordinate transformation.

This proof explicitly invokes a published classification theorem. The new receipt checks smoothness, group closure and central cosets; it does not computationally reprove that classification. The count is a count of matrices before quotienting by any physically declared symmetry equivalence. It does not make the original 130,681-vacuum lower bound into a complete unperturbed F-flat census.

## A specified quantum model

Take nine canonical chiral multiplets Kij with the stated W. Add the norm and Gram interactions only to the scalar potential. They are explicit hard supersymmetry-breaking scalar interactions, not a derived gauge D-term completion. Real coefficients and the real ray K=rI are used. No gauge, quark, Higgs, gravitational or mediator determinants are included. The sextic superpotential is a nonrenormalizable EFT interaction; powers and parameters in the numerical example are measured in the chosen cutoff units. Matching and kinetic running remain separate calculations.

Define d=32b+2c, f=a r^2+d r^5, hs=2a r+5d r^4, ha=-a r+(40b-2c)r^4, and g=6lambda(r^2-v^2). With canonical real fluctuations K=rI+(q+ip)E/sqrt(2), Tr(E^2)=1, the four scalar squared masses are

$$q_{sR}=h_s^2+fh_s'+g+12\lambda r^2,$$

$$q_{sI}=h_s^2-fh_s'+g,$$

$$q_{aR}=h_a^2+fh_a'+g+4\eta r^2,$$

$$q_{aI}=h_a^2-fh_a'+g.$$

Their multiplicities are 1,1,8,8. The singlet and adjoint Weyl squared masses are hs^2 and ha^2, with determinant weights -2 and -16. These off-shell formulas retain the F-dependent holomorphic scalar splitting; using only squared fermion masses away from the F-flat point would miss it. An independent finite-difference Hessian of the original 252-term tensor potential checks all eighteen scalar eigenvalues both on and off the selected ray point.

At r0^3=-a/d and v^2=r0^2, f=0, hs=(96b+6c)r0^4 and ha=72b r0^4. The scalar selector shifts only the real singlet and real adjoint masses by 12lambda r0^2 and 4eta r0^2. All remain positive in the stated regime.

## Exact one-loop response and counterterm

In the local positive-mass patch, the MS-bar chiral determinant is

$$V_1=\frac{1}{64\pi^2}\sum_j n_j q_j^2[\log(q_j/\mu^2)-3/2].$$

Differentiate with a,b,c,lambda,eta,v held fixed before substituting the selected-radius relation. The receipt gives the full polynomial Str M^4(r) and its selected derivative, with no rational reconstruction. At lambda=eta=0, both the selected V1 and its radial tadpole cancel exactly. For the exact benchmark a=b=c=1, lambda=1/100, eta=1/50, r0^3=-1/34, the selected derivative of Str M^4 is -11499421/3070625, which is strictly nonzero. The resulting scale dependence is

$$\mu\frac{dV_1'}{d\mu}=-\frac{(\operatorname{Str}M^4)'}{32\pi^2}.$$

Thus a scale-independent unrenormalized radial calibration is not protected by the finite frame symmetry. This is a counterterm requirement, not evidence that a properly renormalized observable must depend on the arbitrary subtraction scale. A full EFT renormalization must include the permitted operators and their running. The polynomial receipt exposes their radial restriction; it is not a complete off-ray counterterm basis.

The tree radial curvature is exactly 6 q_sR(r0), hence the leading local displacement is delta r=-V1'(r0)/(6q_sR(r0)). If the chosen renormalization condition keeps r0 fixed using delta V=-delta m^2 N, it requires delta m^2=V1'(r0)/(6r0). This condition is an additional input, not a symmetry prediction.

A perturbative example uses a=b=c=0.1, lambda=0.0001 and eta=0.0002, with r0=-0.308678959499304. At mu=0.1 the leading displacement is -9.978489604e-6, and direct minimization of the tree plus one-loop local potential gives r=-0.308688960495578. Scales 0.05 and 0.2 are included in the receipt, alongside the required calibration counterterms. These are local stationary continuations; a one-loop EFT determinant at arbitrarily large fields does not establish global vacuum ordering or two-loop accuracy.

## Massless branch: exact three-ray extension

At the separate normalized benchmark a=-5,b=1,c=0 and K0=diag(1,omega,omega^2), retain the original three Hessian null vectors and invert the six-coordinate massive Hessian. Along each specified null direction (1,0,0), (1,1,0) and (1,1,1), recursively solve the six massive F equations through order eleven in the ray parameter over the exact algebraic field. Substitution into the original W verifies that every effective-W coefficient of degrees three through twelve vanishes on those rays. The receipt and replay test check the solved equations, rather than setting the massive coordinates to zero.

Three ray restrictions do not determine a three-variable homogeneous polynomial and do not prove a moduli space. The previous complete multivariate cancellation through degree six remains the applicable general result. The subsequent complete [multivariate elimination](VALENTINER_MULTIVARIATE_FLATNESS.md) closes this ray-only gap through effective-W degree twelve and moves the first possible effective F-energy degree to twenty-four. It also gives an exact all-orders determinant criterion; an all-orders parametrized family is not claimed.

## Reproduction and prediction boundary

Run python python/develop_valentiner_selected_quantum.py and python python/develop_valentiner_massless_rays.py with PYTHONPATH=python, then python -m pytest -q python/tests/test_valentiner_selected_quantum.py. Receipts are committed under receipts/m22_interactions. No CKM observable, 66-degree angle, golden coefficient or electromagnetic fine-structure constant is an input to these calculations. The selected finite frame is complete; the physical identification of source labels, their quark contractions and CP selection is still a distinct interaction problem.

## Reference

Takeshi Harui, Automorphism groups of smooth plane curves, Kodai Mathematical Journal 42 (2019), 308-331, Theorem 2.5. DOI: 10.2996/kmj/1562032832. Official full text: https://www.jstage.jst.go.jp/article/kodaimath/42/2/42_308/_pdf/-char/en.
