# Exact metric energy and coordinate connection jets

Sigmundur Gudmundsson's *An Introduction to Riemannian Geometry* helps PerfectPower distinguish metric cost from graph admission and polygon coverage. This extension implements reusable metric and connection algebra, including a sharp finite-path energy theorem. It leaves the existing Manhattan objective in place. Neither a new metric nor the coordinate connection formula supplies the missing polygon-topology arguments.

## Source and extraction

The source reviewed is the author's official Lund PDF, version 1.438, 6 May 2026, 159 pages: <https://www.matematik.lu.se/matematiklu/personal/sigma/Riemann.pdf>. The university catalogue is <https://portal.research.lu.se/en/publications/an-introduction-to-riemannian-geometry-lecture-notes-in-mathemati/>. `receipts/riemannian_energy/source.json` pins the downloaded bytes by SHA-256. The full PDF and extracted book text are not redistributed in this repository. The following targeted mathematical extraction is paraphrased; implementation and proofs are original.

Definition 5.5 (p. 63) makes the metric a positive scalar product at every tangent space. Definition 5.17 (p. 67) describes metric preservation by a differential. Example 6.13 (pp. 82-83) obtains coordinate connection coefficients from the metric and its first derivatives. Example 7.12 (p. 97) gives straight geodesics for the Euclidean metric. Definition 7.19 and Theorem 7.20 (pp. 99-100) relate the integral energy, with its factor of one half, to the geodesic equation. These are distinct inputs: positivity, metric transport, local derivative data, and variational analysis. This implementation formalizes the algebraic parts and a finite constant-metric energy specialization; it does not formalize Theorem 7.20.

## Generic metric algebra

`PerfectPower/RiemannianEnergy.lean` works over any ordered field. Consequently its universal theorems apply to rational and real coordinates. The certificate emitter uses rationals for exact kernel evaluation. A metric is the symmetric matrix

\[
G=\begin{pmatrix}a&b\\b&c\end{pmatrix},\qquad
Q_G(x,y)=ax^2+2bxy+cy^2.
\]

The admitted criterion is \(a>0\) and \(ac-b^2>0\). `square_decomposition` proves

\[
aQ_G(x,y)=(ax+by)^2+(ac-b^2)y^2.
\]

`q_nonneg` and `q_zero_iff` prove nonnegativity for every vector and that zero energy occurs only at the zero vector. Positive definiteness is therefore a proved consequence of the admitted finite conditions, rather than an unchecked label. Singular, indefinite and negative forms are rejected. Very small positive determinants remain admissible because no floating-point tolerance participates.

For a two by two matrix \(A\), `pullback_quadratic` and `pullback_bilinear` prove preservation of the quadratic and bilinear forms under \(G=A^T H A\), for arbitrary vectors. `pullback_determinant` proves \(\det G=\det H(\det A)^2\); `pullback_positive` proves positivity when the target metric is positive and \(A\) is invertible. `inverse_apply`, `apply_inverse` and `linear_bijective` prove the explicit linear inverse. `action_transport` extends metric transport to every finite timed sequence.

The affine certificate records both the linear part and translation. Lean derives the transformed vertices from these source values and checks that their consecutive displacements equal `mapSteps linear steps`. Thus translation cancellation is independently checked for the supplied path. The general linear metric preservation and bijectivity theorems are algebraic; no manifold atlas or differentiability theorem is hidden in the word transport.

## Energy, optimality and rigidity

A step consists of a displacement \(v_i\) and a positive duration \(t_i\). Define \(T=\sum_i t_i\), \(d=\sum_i v_i\), and the action

\[
\mathcal A_G=\sum_i Q_G(v_i)/t_i.
\]

For any chosen mean velocity \(u\) with \(d=Tu\), `energy_excess` proves the exact identity

\[
\mathcal A_G=TQ_G(u)+\sum_i Q_G(v_i-t_i u)/t_i.
\]

`energy_lower_bound` proves

\[
E_G=\mathcal A_G/2\ \ge\ TQ_G(u)/2.
\]

`gap_zero_iff` proves equality precisely when every displacement is \(t_i u\). These results quantify over every finite list, not a fixed census of examples. For positive total time, the bound is \(Q_G(d)/(2T)\). A straight, constant-velocity timed path attains it. Stationary segments with positive duration are supported; zero and negative durations are rejected.

The finite quantity agrees with the usual integral energy of a piecewise affine path in a constant metric by integrating its constant velocity on each interval. The subsequent `FlatRiemannian.lean` layer now proves this identification as a sum of actual real interval integrals, together with the analytic lower bound; a single concatenated-curve integral theorem is still separate. The generic ordered-field inequality itself is kernel checked, including its real specialization, without using an integration or ODE axiom.

An emitted packet derives steps inside Lean by zipping the actual source vertices, their tail, and the durations. It proves the lengths match, all durations are positive, total time is positive, summed displacement equals the source endpoints' difference, and the numerical energy and excess agree with the definitions. Its `all_timed_paths` theorem bounds every competitor with the same summed displacement and total time. If the supplied path has zero excess, `source_attained` and `source_minimal` additionally prove that this path attains the bound and minimizes finite timed energy. A detour packet only gets the lower bound and its own excess; it is not called an optimal route.

This is a different optimization problem from the obstacle graph's Manhattan shortest walk. Squared displacement energy depends on durations. Optimizing durations, taking square roots for length, imposing obstacle constraints, proving existence, and reconstructing geodesics in a varying metric each require additional mathematics. A geodesic is not automatically a global minimum. This extension never replaces graph weights with squared lengths and then calls the result a Riemannian shortest path.

## Coordinate first jets

Let \(D_{ijk}\) represent the supplied coordinate derivatives \(\partial_i g_{jk}\), symmetric in \(j,k\). The lowered coefficients are

\[
L_{ijk}=\tfrac12(D_{ijk}+D_{jik}-D_{kij}).
\]

For any index type, `koszul_torsion` proves \(L_{ijk}=L_{jik}\), and `koszul_compatible` proves \(L_{ijk}+L_{ikj}=D_{ijk}\). `koszul_unique` proves that every lowered array with these two properties equals this formula. This is reusable coordinate algebra, with no dimension-specific examples in the theorem.

For planar source packets, Python solves the positive metric's inverse system to emit the raised coefficients \(\Gamma^k_{ij}\). Lean independently checks the finite identity \(\sum_k g_{kl}\Gamma^k_{ij}=L_{ijl}\), derivative symmetry, and raised torsion symmetry. It then applies the generic compatibility and uniqueness results. Zero first derivatives produce zero connection coefficients. Altering a derivative or coefficient without changing the corresponding proofs is rejected.

The original emitter supplies first-jet data. The subsequent `MetricJetRealization.lean` and `MetricJetConnection.lean` modules now realize them as actual derivatives of a smooth affine metric field, prove positivity in a source neighborhood, and interpret the raised connection there. They do not assert global positivity, chart transition laws or nonflat geodesic ODE existence. Curvature needs second derivative data and its own source interpretation. The smooth Levi-Civita existence and uniqueness theorem remains outside the claimed result.

## Interface and reproducibility

A packet uses `metric: [a,b,c]`, `vertices`, and one strictly positive `duration` per segment in `durations`. Integers, rational strings and Python `Fraction` values are exact; floats and booleans are rejected. Optional `transport` contains a target metric, `linear: [p,q,r,s]`, and translation. Optional `derivatives` contains the symmetric metric-entry triples in the x and y directions. The default limit is 256 steps; budget exhaustion raises and never produces a truncated theorem.

```sh
PYTHONPATH=python python3 -m perfectpower geometry-foundations metric-energy-proof examples/riemannian_energy/straight.json
make riemannian-energy
make riemannian-energy-kernel
```

The JSON command returns `certificate` and `lean_source`. Emission always says `kernel_checked: false`: generating text cannot establish acceptance. The independent kernel script records the exact accepted source hashes, the Lean version, and deliberate mathematical rejection hashes in `kernel-validation.json`. Successful receipts apply only to those bytes. Compilation failures, missing imports, resource failures and stale hashes cannot be reclassified as a successful rejection campaign.

The retained examples cover a detour, a constant-velocity path, a stationary path, a rational nearly singular metric, a shear, a reflection, a nonconstant first jet, and a flat jet. The Python suite also checks 100 seeded rational variance/rigidity instances and 80 seeded connection systems, alongside invalid metrics, durations, transport, shape, and work limits. The retained adjacent regression campaign passes 97 Python tests, including the 11 new metric test methods. The kernel campaign checks the generic library and eight emitted sources, and rejects nine corruptions. It prints the axioms of the central generic and instance results; no `sorryAx`, custom axiom or native decision shortcut is admitted. Full source and validation receipts accompany the change.

## Relationship to the geometry certificates

The original geometry admission library proves exact rational winding visibility, complete reconstruction of the finite source graph, all-walk Manhattan optimality in that graph, and pointwise triangular-source refinement coverage. The newer real-geometry layer strengthens these with all-real segment interpretation and universal real-point mesh coverage. This metric extension can evaluate an already supplied path under an independently admitted constant metric. Its energy theorem does not certify that a competitor avoids obstacles or that a triangulation covers an arbitrary concave polygon.

The subsequent [real-geometry closure](PLANAR_CLOSURE_MONOGRAPH.md) proves real-parameter winding admission, complete finite source-graph reconstruction for that predicate, and arbitrary supplied-mesh pointwise coverage through universal certificates. It also proves flat analytic geodesic uniqueness, actual segment energy integrals and local smooth first-jet realization. General Jordan/topology arguments, continuous-path graph completeness, nonflat geodesic existence, curvature, positive clearance and physical rope dynamics remain separate work. Gudmundsson supplies a sound mathematical vocabulary for those future layers; it does not erase their hypotheses.
