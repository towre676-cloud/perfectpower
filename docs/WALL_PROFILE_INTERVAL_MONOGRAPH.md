# A certified whole-line wall from a compact trial profile

The five wall-profile hypotheses are now certified for an exact continuous static wall, including its infinite asymptotic domain. The proof does not extrapolate sampled signs, fit linear tail coefficients, or treat a discretized root as a differential-equation solution. It constructs a compact C2 trial profile, encloses its continuous residual with Arb, proves uniform coercivity in a function-space neighborhood and minimizes the actual wall energy in that neighborhood. Maximum principles and a cooperative-system argument then prove the signs everywhere.

This is a computer-assisted analytic certificate, not a Lean theorem. The interval arithmetic is performed by python-flint/Arb. The mathematical argument below specifies how those inequalities establish existence and signs. SciPy supplies an untrusted initial proposal; checking the committed seed does not rerun SciPy. Ten independent SymPy identities check the potential gradients, clipping decompositions, Hessians and scalar reference gap. Neither the original floating profile nor its fitted exponential tail is assumed exact.

## Inputs and coordinate conventions

Use x = sqrt(lambda/2) rho, rho = v z, v = 30000 GeV, and fields u = phi/v, y = S/v and h = H_radial/v. The rational inputs are alpha = g_source/v = 1/10, mu = M_heavy/v = 10, lambda_H = 13/100, h0 = 41/5000 and kappa = 1/10000000. The source quartic has midpoint lambda = 0.0000176188164948 and a certified radius 0.000000000000001. Thus the certificate covers every lambda in [0.0000176188164938, 0.0000176188164958], including the previously reported rounded calibration. Arb may enlarge the parameter enclosure slightly through outward rounding; every displayed declared parameter value remains covered.

With k2 = lambda/2, the potential and static equations are

\[
\Phi=\frac\lambda4(u^2-1)^2+\frac{\mu^2}{2}\left(y+\frac{\alpha u^2}{\mu^2}\right)^2+
\frac{\lambda_H}{4}\left(h^2-h_0^2+\frac\kappa{\lambda_H}(u^2-1)\right)^2,
\qquad w''=\frac{\nabla\Phi(w)}{k2}.
\]

Primes in this monograph mean x derivatives. The source is odd, the singlet and Higgs are even, and the wall is pinned at u(0)=0. On the positive half-line the boundary conditions are u(0)=0, y'(0)=h'(0)=0 and w(infinity)=(1,-alpha/mu^2,h0). The whole-line wall is obtained by reflection. Uniqueness is local in this pinned reflection sector; translation of the full wall remains a genuine zero mode.

## The continuous approximation

The committed seed contains exact hexadecimal floating-point data at 4097 nodes from x=0 to x=22. Each hexadecimal value is converted to its exact dyadic rational. The checker replaces the center source value and the two center Neumann values by zero, and replaces the right field values by the exact vacuum. All three right derivatives are set to zero. Second derivatives at the nodes are defined by the exact static force, not by differentiating noisy sampled values.

On each of 4096 cells a quintic Hermite polynomial matches the two field values, first derivatives and prescribed second derivatives. The polynomials therefore join C2. At x=22, the field is the vacuum, its first derivative is zero and its second derivative is exactly zero because the force vanishes there. Extend this trial profile a(x) by the exact constant vacuum for x>=22. This extension is C2 and has exactly zero residual beyond its support. The nearby certified solution is not assumed constant beyond x=22.

All polynomial residuals a''-grad(Phi)(a)/k2 are bounded on whole cells. For p(t)=sum_i c_i t^i, t in [0,1], the checker converts to Bernstein coefficients b_j=sum_{i<=j} c_i binom(j,i)/binom(n,i). The convex hull of the outward-rounded b_j encloses p throughout the cell. Residual polynomials have degree at most fifteen. Parameters, polynomial coefficients, force evaluations, conversions and strict comparisons use 160-bit Arb arithmetic. The same seed passes an independent 192-bit check.

The source comparison with tanh(x) uses conservative interval ranges on each cell. Its certified difference bound is approximately 0.00537105, much larger than its typical actual error. Beyond x=22 the comparison is bounded by 1-tanh(22), which is smaller than the accumulated core bound. Every bound used in the coercivity argument consequently covers the entire half-line.

## Coercivity in a continuous energy ball

Let e=w-a, with e_u(0)=0 and e in H1(0,infinity)^3. Define

\[
\|e\|_Q^2=d\int|e'|^2+c\int|e|^2,
\qquad d=\frac14,\quad c=\frac12.
\]

The one-dimensional embedding gives |e_i(x)|^2 <= 2 ||e_i||_2 ||e_i'||_2 <= ||e||_Q^2/sqrt(dc). Thus an energy ball of radius r(dc)^(1/4), r=10^(-5), lies in a uniform field neighborhood of radius r. H1 corrections tend to zero at infinity: (|e_i|^2)' is integrable, so |e_i|^2 has a limit, and its L2 integrability forces that limit to vanish. The asymptotic vacuum condition is therefore part of the function space, not a numerical tail approximation.

For the scalar reference, the odd half-line operator L_ref=-d_x^2+6 tanh(x)^2-2 has positive ground state sech(x)tanh(x), with eigenvalue 3. Its ground-state identity yields q_ref(f)>=3||f||_2^2 for f(0)=0. Since the potential is at least -2, reserving d=1/4 of the gradient gives

\[
q_{\rm ref}(f)\ge\frac14\|f'\|_2^2+\frac74\|f\|_2^2.
\]

The full Hessian has source-singlet coupling 2 alpha u/k2 and source-Higgs coupling 2 kappa u h/k2. Young's inequality consumes a fraction 1-tau of the singlet mass, tau=1/1000. The leading source correction 4 alpha^2 u^2/(mu^2 k2) cancels the consumed Schur contribution, leaving a penalty 4 alpha^2 u^2 tau/(mu^2 k2(1-tau)) and a retained singlet floor tau mu^2/k2. This cancellation is essential; treating the large singlet coupling without its matching source Hessian would give a useless bound.

If h_a,min is the enclosed trial minimum, the Higgs Hessian floor in the uniform ball is B_H=[lambda_H(3(h_a,min-r)^2-h0^2)-kappa]/k2. Half of this floor absorbs the Higgs cross term and half is retained. The source penalty is (2 kappa B_u B_h/k2)^2/(B_H/2). Polynomial enclosures of r_S=y+alpha u^2/mu^2, r_H=h^2-h0^2+(kappa/lambda_H)(u^2-1), and u-tanh(x) bound the remaining source perturbation. Its positive 2 kappa^2 u^2/(lambda_H k2) term is discarded conservatively.

The outward-rounded retained source, singlet and Higgs L2 floors are approximately 1.41231, 11351.5 and 0.982954, all strictly greater than c=1/2. Therefore, throughout the uniform ball, the actual continuous Hessian quadratic form satisfies

\[
\langle f,D^2E(w)f\rangle\ge\frac14\|f'\|_2^2+\frac12\|f\|_2^2=\|f\|_Q^2.
\]

The proof uses the continuous operator and an analytic scalar gap. It does not rely on an inverse of a finite matrix, a floating eigenvalue or a sampled Hessian. The natural center boundary conditions for singlet and Higgs are Neumann; the inequality is established for the larger variational space with only the source trace fixed at zero. It therefore also holds on the Dirichlet subspace later used for negative-part tests.

## Whole-line existence, uniqueness and error

Let b=a''-grad(Phi)(a)/k2. Its L2 norm is bounded by sqrt(22 sum_i ||b_i||_infinity^2), since its support is [0,22]. The dual norm of the energy residual is at most eta=||b||_2/sqrt(c). There are no center boundary residuals because the exact Neumann conditions have been enforced.

Minimize E(w)=integral_0^infinity [|w'|^2/2+Phi(w)/k2] over the closed Q-ball around a. This ball is weakly compact in H1. The nonnegative square potential and weak gradient lower semicontinuity give a minimizer: local compactness supplies pointwise convergence on finite intervals, and Fatou handles the infinite domain. The trial has finite energy because it is the exact vacuum outside a compact interval. Every H1 correction has finite energy in the uniform neighborhood because the vacuum is stationary and the potential is quadratic to leading order.

On the boundary of the ball, the energy derivative in the outward radial direction is at least ||e||_Q^2-eta||e||_Q. If eta<r(dc)^(1/4), moving inward lowers energy; the minimizer cannot lie on the boundary. The interior minimizer solves the full continuous Euler-Lagrange equations, and its natural center conditions are y'(0)=h'(0)=0. Polynomial forces bootstrap it to a smooth classical solution. Coercivity also gives uniqueness among stationary solutions in this convex pinned energy ball.

The accepted residual bound is approximately 3.38235e-7 in L2. The existence-boundary ratio eta/[r(dc)^(1/4)] is about 0.0804463. Stationarity sharpens the solution error to ||e||_Q<=eta, hence

\[
\|w-a\|_\infty\le\frac{\eta}{(dc)^{1/4}}<8.05\times10^{-7}.
\]

In particular h>0 everywhere, with the enclosed lower bound above 0.00819919. The singlet's linear positive Green operator sharpens its individual error to approximately 1.609e-9. These are dimensionless field bounds; multiplying by v=30000 GeV gives the physical field scales. The certificate is uniform over the declared source-quartic interval.

## Source positivity near the pinned center

Uniform closeness alone does not give a sign where u vanishes at x=0. The checker bounds the source second-derivative error by Hessian row bounds and the sharpened singlet error. For e_u(0)=0,

\[
e_u'(0)=e_u(1)-\int_0^1(1-s)e_u''(s)\,ds,
\]

so |e_u'(0)|<=||e_u||_infinity+||e_u''||_infinity/2. The certified center slope is greater than 0.999959. The equation u''=A(x)u has |A|<4.228 in the enclosing neighborhood. Sturm comparison with sin(sqrt(A_max)x) then gives positivity up to x=0.01; the checker conservatively verifies 0.01 sqrt(A_max)<1. For x>=0.01, comparison with tanh(x) and the global trial-difference bound gives a strictly positive margin above 0.0046278. Thus u>0 on the entire positive half-line without sampling a neighborhood of its zero.

## Joint maximum principles: source range and Higgs barrier

The positive Higgs profile allows a joint argument that is stronger than separately assuming the source never overshoots. Suppose U=max |u|>1. The singlet equation (-d_rho^2+mu^2)y=-alpha u^2 gives y>=-alpha U^2/mu^2. At a positive global Higgs minimum, its static equation gives h_min^2-h0^2>=-(kappa/lambda_H)(U^2-1). If the minimum is the asymptotic value h0, the same lower bound holds trivially.

At a source extremum with |u|=U, both r_S=y+alpha U^2/mu^2 and r_H=h^2-h0^2+(kappa/lambda_H)(U^2-1) are consequently nonnegative. The source equation implies u''/u>=lambda(U^2-1)>0 in rho coordinates, contradicting the second-derivative sign at that extremum. Therefore |u|<=1 globally. Nonconstancy and the strict positive singlet Green function exclude an interior equality |u|=1.

Now set s=y+alpha/mu^2 and t=h-h0. Their equations are

\[
(-d_\rho^2+\mu^2)s=\alpha(1-u^2),
\qquad (-d_\rho^2+\lambda_H h(h+h_0))t=\kappa h(1-u^2).
\]

Both right-hand sides are positive for every finite point. The operators have positive zeroth-order coefficients and the functions tend to zero at infinity, so s>0 and t>0 everywhere finite. Thus 0<u<1 for x>0 and h>h0 for all finite x, with h approaching h0 at infinity. A strict positive Higgs barrier is proved, rather than inferred from a tiny sampled excess that might be below floating-point precision.

## The derivative signs and continuous linear stability

Differentiate the field equations and flip singlet and Higgs signs. The vector W=(u',-y',-h') obeys a symmetric cooperative operator L_tilde W=0 with off-diagonal entries -2 alpha u/k2 and -2 kappa u h/k2 on x>0. Its center traces are (u'(0),0,0), with the first strictly positive. The derivatives belong to H1: in the tail, the force is Lipschitz in the H1 correction around its stationary vacuum, so second derivatives are L2 as well.

Test the equation against the negative parts of W. Those negative parts have zero source trace at the center and lie in the previously certified variational space. Cooperative off-diagonal signs give q(W_negative)<=0, whereas continuous coercivity gives q(W_negative)>=||W_negative||_Q^2. The negative parts vanish. Strict irreducibility for alpha>0 and kappa>0, together with the nonzero center source trace, yields u'>0, y'<0 and h'<0 for every x>0. This proves all five hypotheses on the whole line after reflection.

The pinned opposite reflection sector already has the certified spectral bound L/k2>=1/2. In the translation reflection sector, the positive weights (u',-y',-h') give the cooperative ground-state identity: its quadratic form is a sum of weighted gradient squares and nonnegative coupling squares. The form is nonnegative and its only L2 kernel is the translation vector Phi'. The angular Goldstone operator retains its exact factorization using h''/h. These are classical continuous linear-stability results for the certified wall; they do not assert nonlinear or quantum longevity of the localized massive mode.

## Consequences for the vector and thermal calculations

The gauge couplings do not enter this classical background. For any positive declared vector coupling, m_V(x)^2>=m_V,vacuum^2 follows from h>=h0. Both the transverse and factorized physical longitudinal Proca operators therefore have the previously stated vacuum-threshold lower bounds. The transverse potential is a strictly positive nontrivial barrier above its vacuum value.

The positive vacuum Hessian makes the asymptotic equilibrium hyperbolic. Standard autonomous-ODE stable-manifold theory then gives exponential approach for this exact solution; no numerical stable-manifold matching is used to establish its existence. The certificate does not provide explicit interval constants for those exponential tails. With an integrable positive transverse barrier, a bounded zero-energy resonance is excluded by integrating |f'|^2+U_TE|f|^2. This supplies the profile hypotheses used in the cubic pair-threshold law, provided the particular leading pair overlap is nonzero. The numerical coefficient of that overlap is not enclosed by this certificate.

For the computed TE thermal channel, the exact wall operator differs from the vacuum operator by nonnegative multiplication. On any identical finite Dirichlet box this raises each eigenvalue. Since the planar thermal function has positive derivative with respect to normal mass squared, its relative thermal free energy is nonnegative. The profile-dependent sign is now supported by a certified exact wall. The result applies to the computed TE sector; a longitudinal thermal determinant has a different operator and is not assigned this sign by the present argument.

The previous 154.225 GeV mode, its calibrated eigenvalue, normalized vertices, continuum widths and thermal numerical values have not themselves received interval error enclosures here. This certificate establishes the nearby exact background and its structural signs over a small parameter interval. It does not turn the many-digit floating results into rigorous width bounds, recompute nucleation, add the missing vector polarizations or establish a nonlinear lifetime.

## Reproduction

Install the optional research dependencies with `python -m pip install -r python/requirements-wall-intervals.txt`. Run `PYTHONPATH=python python python/develop_wall_profile_intervals.py` from the repository root. When the committed seed exists, this command checks it directly and writes the certificate; removing the seed causes an untrusted SciPy proposal to be generated first. The checker reconstructs the exact dyadic data and all polynomial enclosures from scratch. Run `PYTHONPATH=python python -m unittest discover -s python/tests -p test_wall_profile_intervals.py` for the independent identities, polynomial tests, precision replay and deliberately rejected examples.

The machine-readable proof data are `receipts/flavor_cosmology/wall_profile_interval_seed.json` and `receipts/flavor_cosmology/wall_profile_intervals.json`. The seed's SHA-256 is embedded in the certificate. The decimal float display is for reading only; the proof uses the outward Arb bounds and strict comparisons regenerated from the seed. The release includes checks that an undersized existence ball and a deliberately damaged profile are rejected. The Python checker, analytic proof and Arb implementation form the trust base; no Lean kernel check is claimed.

For the interval-number representation and outward endpoint operations, see the [official python-flint Arb documentation](https://python-flint.readthedocs.io/en/latest/arb.html). This release's continuous variational argument is given explicitly above; it does not require a third-party BVP solver's success flag as evidence of existence.
