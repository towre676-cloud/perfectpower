# From exact chart metrics to differential dynamics and continuous distances

PerfectPower differential geometry release, October 2026.

## Purpose and mathematical source

Peter W. Michor's *Topics in Differential Geometry*, available from the author's University of Vienna website at https://www.mat.univie.ac.at/~michor/dgbook.pdf, supplies a useful next direction for the repository. The relevant subjects are Riemannian metrics, geodesics, connections, parallel transport, curvature, Jacobi fields, and symplectic geometry. In the author's 2008 PDF these begin near printed pages 275, 291, 300, 347, and 413. This release builds original executable constructions around those subjects; it does not reproduce the book or claim to formalize its general theory.

The previous geometry releases established exact chart densities, rational geometry, Bernstein positivity witnesses, and finite graph-distance certificates. Their decisive limitation was the missing connection between local smooth metric bounds and continuous path distances. A shortest path on a finite graph is a graph result. A bound at selected vertices does not imply a bound at every point in a rectangle. A chart rectangle also cannot stand in for the entire compact surface. This release advances the smooth side while retaining those distinctions in its data contracts.

The additions are a conformal metric compiler, exact connections and curvature, geodesic and Hamiltonian dynamics, parallel transport, linearized trajectory equations, rational conformal coordinate changes, continuous chart-domain distance comparisons, a global smooth-plane example, short-time interval flow tubes, generated Lean identities, and an interactive trajectory viewer. Their value is that the earlier metric calculations now drive inspectable geometric behavior and continuous-distance statements on explicit domains.

## Exact metric representation

Every admitted metric has the form g = rho(dx² + dy²), with rho = N/sqrt(D). Both N and D are rational polynomials in two real coordinates. The admitted domain requires N > 0 and D > 0. This convention represents a positive metric tensor, so the corresponding length density is sqrt(rho), not rho. Mixing the two would produce incorrect length comparison exponents.

The source packet stores N, D, rho², the logarithmic gradient, its Hessian, the connection coefficients, and curvature times density. The compiler uses SymPy 1.14 to simplify rational expressions. Exact evaluation, polynomial arithmetic, and interval operations use rational arithmetic. Inputs reject floating-point coefficients. Degree and monomial limits make excessive symbolic work an explicit work-limit result rather than an unbounded promise of completion.

For the existing hyperelliptic family the source remains the repository's actual chart-density constructor. The genus-two example is y² = x⁵ - x. Its metric comes from the explicitly chosen monic holomorphic differentials. No period matrix is computed, so this release does not call the metric a period-normalized Bergman metric. Finite, branch-root, and infinity charts retain their original polynomial provenance. Rechecking a metric reconstructs its complete symbolic packet and, when curve provenance is supplied, reconstructs the original chart density as well.

## Connections, acceleration, and curvature

Write gx and gy for the two components of grad(log rho). The standard Levi-Civita coefficients are Gamma[k,i,j] = (delta[k,j]g[i] + delta[k,i]g[j] - delta[i,j]g[k])/2. With velocity (u,v), the geodesic equation uses q'' = -Gamma(q',q'). Its acceleration is ((v²-u²)gx/2 - uv gy, (u²-v²)gy/2 - uv gx). This sign convention is documented explicitly because connection symbols in different texts can follow different conventions.

The Gaussian curvature satisfies K rho = -Delta(log rho)/2. Although rho can involve a square root, its logarithmic derivatives and K rho are rational functions. Exact square-root brackets then enclose rho and K at an admitted rational point. Perfect rational squares are recognized directly, avoiding an unnecessary dyadic widening of exact sphere and hyperbolic values. Non-square values receive outward dyadic bounds.

Three independent reference metrics anchor these formulas. The flat plane has K = 0. The unit sphere in stereographic coordinates has rho = 4/(1+x²+y²)² and K = 1. The upper half-plane has rho = 1/y² and K = -1 for y > 0. The polynomial representation also admits the lower half-plane component where appropriate; it does not silently identify that disconnected component with the selected example trajectory. At the genus-two finite-chart point (2,0), exact evaluation gives K = -12/25. A dedicated Lean point certificate checks the actual packet density and curvature-formula values there. Sphere and hyperbolic examples also have universal polynomial coefficient identities. The finite-curve dynamics are validated by complete symbolic replay and independent arithmetic and trajectory tests; its retained Lean arithmetic certificate concerns the stated point. Those identities use shared polynomial cofactors to check the gradient, Hessian, connection, and curvature expressions efficiently, while their interpretation as analytic derivatives remains an explicit classical-calculus step. Regular branch and infinity chart origins have density 4 in the retained example.

## Conservation and parallel transport

For a tangent vector z along a trajectory with velocity v, parallel transport solves z' = -Gamma(v,z). The algebraic identity d(rho |z|²)/dt = 0 follows from the metric gradient and this transport equation. The same construction yields conservation of geodesic energy E = rho |v|²/2. The generic Lean foundation proves the corresponding algebraic cancellation identities over real numbers.

These are useful checks with different purposes. Exact algebra proves the cancellation for arbitrary real coordinate values supplied to the formulas. Independent tests evaluate the formulas at many rational points and compare against their analytic reference trajectories. Numerical diagnostics measure drift produced by the discretization. Small numerical drift alone is not a proof of exact conservation, and the receipts keep numerical trajectories explicitly uncertified.

The sphere reference geodesic in the viewer is the stereographic unit circle q(t) = (cos t, sin t). The transported radial coordinate vector rotates with that path and preserves its metric norm. Hyperbolic tests compare against a vertical geodesic y = exp(t) and a semicircle parametrized by x = tanh(t), y = sech(t). These analytic solutions were chosen independently of the numerical integrator and catch sign or density errors that a self-consistency test could miss.

## Hamiltonian and linearized equations

The cotangent formulation uses H(q,p) = |p|²/(2 rho). Its position rate is p/rho and its momentum rate is H grad(log rho). At a rational point these can involve the same enclosed density as curvature. The implementation returns exact rational intervals and tests the Legendre relation p = rho v where the reference density is exact. A generic Lean identity checks the cancellation of Hamiltonian energy rates.

The coordinate variation equation is obtained from the Jacobian of the first-order geodesic vector field on (x,y,u,v). This is the linearized coordinate equation corresponding to a family of geodesics. Its distinction from a fully intrinsic covariant Jacobi-field development is intentional. The implementation checks its Jacobian against central finite differences and checks integrated variations against two nearby numerical geodesics. It supplies a practical foundation for sensitivity and conjugate-point work without claiming that the latter is already certified.

## Coordinate changes and retained domain exclusions

The chart transport compiler accepts rational two-coordinate maps and requires J-transpose J = lambda I. It permits either orientation, so the stereographic sphere overlap can be represented by planar inversion. A zero conformal factor or constant map is rejected. The pulled metric density is rho composed with the map, multiplied by lambda. The compiler verifies the second-order geodesic chain rule symbolically, including the coordinate-map Hessian term.

Cancellation of a rational expression does not remove an original chart exclusion. The returned transport packet retains the original map denominators, Jacobian determinant, and mapped metric positivity requirements. Planar inversion is undefined at the origin even when the simplified pulled sphere density extends smoothly there. The branch map x = t² is likewise a valid overlap only at nonzero t. Its pulled density matches the independently constructed regular branch-chart metric on the overlap, while the branch origin is handled by the regular chart itself.

This is a concrete improvement over treating a simplified expression as its own complete domain description. It also identifies the next global requirement: chart changes and regular charts must be assembled into an atlas with certified coverage and overlap conditions before claiming unrestricted compact-surface results. This release does not infer such coverage from the few retained examples.

## Continuous rectangles and common path families

A continuous chart bridge proves l² < rho < u² throughout a closed rational rectangle. It requires strict Bernstein certificates for four source polynomials: N, D, N² - l⁴D, and u⁴D - N². Those polynomial conditions imply the density bounds at every real point in the rectangle, including its boundary. They are not just checks at a mesh or a list of samples.

The retained genus-two finite rectangle is [2,9/4] × [0,1/4], with length scales l = 1/4 and u = 1. Its branch and infinity examples use [-1/4,1/4]² with scales 1 and 3. Independent Lean sources prove the actual pointwise inequalities for these complete rectangles through complex-norm bounds on the curve polynomial. This supplies a separate mathematical check of the retained Bernstein witnesses and avoids an expensive high-degree tensor expansion. The general emitter also retains a row-factored Bernstein fallback for other domains. The source hash binds each validation receipt to the checked theorem text.

For a path contained in such a rectangle, pointwise speed comparison gives l times Euclidean length ≤ metric length ≤ u times Euclidean length. The new Lean foundation proves the integration step under explicit integrability hypotheses. It then proves the infimum step for one common nonempty family of paths with nonnegative lengths. This last condition is the central bridge: both distance infima must range over the same admissible family.

Since the rectangle is convex, the straight segment belongs to the contained path family, and its Euclidean length equals the ordinary Euclidean endpoint distance. Thus the bridge encloses the continuous intrinsic distance obtained by restricting paths to that rectangle. An endpoint outside the rectangle is rejected. Paths leaving the rectangle are outside this certificate, so this result does not establish the unrestricted distance on the whole compact curve. Generated coefficient proofs, pointwise density proofs, and generic integration theorems also retain the distinction between polynomial identities checked in Lean and the analytic interpretation supplied by classical calculus.

## A genuinely global smooth example

The release includes the whole-plane metric rho = (1 + 2r²)/(1+r²), where r² = x²+y². Its density lies between 1 and 2 at every real point. Lean proves these universal inequalities and the conservative rational length scales 1 and 3/2. The generated theorem also identifies the actual compiler density N/sqrt(D) with this rational expression, using the positive denominator to simplify the square root. There is no chart boundary in this example, so its comparison applies to all piecewise-smooth paths in the entire coordinate plane.

For endpoints (0,0) and (3,4), the resulting distance enclosure is [5,15/2]. The global packet also proves a strict nearest-site region using metric-distance comparison and triangle inequalities. With one site at the origin and another at (3,4), the Euclidean disk of radius 1 about the origin has a strict comparison margin of 2. This is a continuous smooth-metric result; it requires no claim that a finite graph has become the smooth plane.

The plane example demonstrates that the common-path bridge can produce an unrestricted global result when its domain hypotheses really are global. The higher-genus chart examples demonstrate what remains valid when the hypotheses are only local. Keeping both is more informative than presenting a conditional theorem without any instantiated continuous domain.

## Exact short-time flow tubes

A second certification route addresses time evolution. The rational interval engine bounds the four-dimensional geodesic vector field and its Jacobian on a proposed tube. It checks initial-box containment, positive metric domain, a Picard self-mapping inequality, and hL < 1 for a row-sum Lipschitz bound L over time h. Failure of any condition produces an explicit rejection. Refined whole-time boxes and endpoint boxes use outward rational operations.

These conditions support classical Picard existence and uniqueness for the local autonomous flow. The retained flat example has an exact endpoint. The sphere example encloses a time interval of 1/100 and is tested against the independent cosine/sine reference solution. The checker reconstructs the packet and interval computation rather than trusting serialized bounds.

The interval algorithm is exact arithmetic, but the continuous ODE theorem has not been formalized in Lean here. Its receipts therefore retain kernel_checked = false. Neither that limitation nor the uncertified status of RK4 traces is hidden by a generic certificate label. The next useful formal extension would encode the vector field's analytic interpretation and prove a reusable interval-Picard theorem that these rational witnesses can instantiate.

## Reproduction and inspection

Install the optional dependency with `python -m pip install '.[differential]'`. Generate the retained examples with `PYTHONPATH=python python3 python/develop_michor_geometry.py`. The CLI adds `python -m perfectpower differential-geometry OP input.json`, with compile, point, dynamics, bridge, distance, winner, pullback, tube, trace, and plane operations. Example JSON inputs are in `examples/michor_geometry`.

Run the dedicated tests with `PYTHONPATH=python python3 -m unittest discover -s python/tests -p 'test_michor_geometry.py' -v`. With the pinned Lean 4.20.0 toolchain and Mathlib dependencies available, run `lake env python3 scripts/check_michor_geometry_kernel.py`. That script compiles the generic foundations and each generated source, prints theorem axioms, rejects sorryAx, and requires four deliberately false claims to fail: a wrong gradient factor, a wrong energy factor, a false global density upper bound, and a false continuous curve scale. Missing imports do not count as successful negative tests.

The reproducible proof packets do not modify their kernel_checked flag simply because a separate checker ran. Instead, `kernel-validation.json` records the accepted source hashes, Lean version, rejected mutations, and exact formal scope. The test logs provide executable evidence alongside the generated source. Numerical trajectory receipts retain their observed energy and transport drift independently.

Open `web/michor_geometry/index.html` to inspect the sphere, hyperbolic, and genus-two trajectories with their transported vectors and conservation diagnostics. The curve view shades the actual certified rectangle. This viewer is an inspection aid, not an additional proof mechanism. It reads retained data locally and requires no service connection.

## Next mathematical work

The main remaining geometry objective is an atlas-level global comparison for a specified compact curve. It needs complete chart coverage, validated transitions, and path-family treatment across chart boundaries. Intrinsic Jacobi equations, certified transport tubes, and chart-switching trajectory enclosures are further concrete extensions. A global shortest-path claim would additionally require lower bounds against every admissible competing path, rather than merely a locally solved geodesic equation.

This release strengthens the repository by closing a real continuous-domain gap, adding executable differential structure to its existing metric source, and making the remaining analytic and global hypotheses explicit. Its strongest fully formal achievements are the polynomial coefficient identities, complete rectangle inequalities, generic conservation algebra, integration and infimum transfer, and universal smooth-plane density bounds. Its exact interval dynamics and numerical explorations extend that foundation with clearly stated validation levels.

## Retained validation result

The release passes 97 geometry and metric tests: 81 in the geometry suite, including 24 new differential-geometry tests, and 16 existing metric-box tests. Nine Lean sources pass the kernel audit using only standard axioms, and four false arithmetic claims are rejected. Thirty-nine generated files reproduce byte-for-byte. Complete symbolic transport and exact interval-flow replay pass for four retained receipts, and the installed wheel exercises the two new differential CLI reference routes. The viewer JavaScript passes syntax checks; it remains a numerical inspection aid. These counts describe the retained release examples and their explicit formal scope, rather than a full formalization of differential geometry.
