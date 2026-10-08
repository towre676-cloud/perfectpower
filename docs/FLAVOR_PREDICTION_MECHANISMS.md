# From fitted flavor to mechanisms that can predict

PerfectPower now has a source-derived coupling-reduction calculation, an exact weak-basis mixing interface, a conditional gauge-unification compiler, and four compiled Lean modules. No CKM angle, CKM magnitude, golden coefficient or electromagnetic coupling enters the new candidate discovery. The result is a concrete test of a proposed route to prediction: could radiatively preserved coefficient ratios remove the freedom in the existing scalar action? In the fully classified exchange-symmetric SU(3) scalar sector, they do not. The calculation identifies exactly why and provides machinery for testing the interactions that must replace that failed route.

This release does not derive observed CKM values or alpha(0). The gauge designs introduce a new UV unification hypothesis; they are separate extensions of the existing gauge-running model, not a consequence of its finite flavor symmetry. Their retained anchors are illustrative rational inputs, not measured electroweak inputs. Stating this distinction is essential to using the outputs as prospective model calculations.

## Coupling ratios derived from the actual scalar-loop tensor

The input is the committed, coefficientwise-proved 61-operator scalar-loop tensor in `receipts/m22_interactions/nonet_higgs_exact_loop_algebra.json`. The new extraction retains the nine adjoint-pair operators with source indices 10, 11, 22, 23, 39, 48, 49, 50 and 51. It checks that no product leaks into an omitted operator and that exchange of the up and down sectors preserves the restriction. The retained action has seven independent coefficients: a common radial self coupling, a common finite self coupling, a norm cross coupling, an ordinary-adjoint cross coupling and three finite cross couplings. All 45 symmetric products in this nine-operator restriction are replayed directly against the original exact Q(sqrt(5)) polynomial tensors. The trace decomposition below is also checked coefficient by coefficient against those tensors.

For a quadratic beta map B, a normalized ray r satisfies B(r,r)=r. Along that ray a coupling vector lambda(t)=f(t)r remains on the same line; only its overall amplitude runs. This makes the ratios a plausible source of constraints, rather than coefficients chosen to match mixing. It is not an interacting fixed point. For the canonical pure-scalar one-loop contraction, a fixed point is much more restrictive than a ray. The new Lean module proves the homogeneity identity and the radial positivity obstruction in the declared restriction.

In the SU(3)-invariant subspace the finite self coefficient vanishes and the three finite cross coefficients coincide. Write the four remaining coefficients as (a,c,d,h), in the source operator normalization. Exact beta restriction gives

\[
\begin{aligned}
B_a&=128a^2+16c^2+\frac5{18}d^2+\frac{27}{20}h^2,\\
B_c&=160ac+16c^2+\frac{25}{18}d^2+\frac{27}{4}h^2,\\
B_d&=32ad+32cd+\frac65d^2+\frac{108}{25}dh+\frac{4536}{125}h^2,\\
B_h&=32ah+32ch+\frac49d^2+\frac{224}{15}dh+\frac{436}{25}h^2.
\end{aligned}
\]

The rational Groebner computation checks both ideal inclusions and obtains a univariate eliminant with unique back substitution for the other three coordinates. Exact real-root isolation establishes that there are five nonzero real solutions. The full basis, factorization and root intervals are retained in the receipt. The five rays, in the order (a,c,d,h), are

\[
\left(\frac1{128},0,0,0\right),\quad
\left(\frac1{144},-\frac1{144},0,0\right),\quad
\left(\frac1{192},\frac1{96},0,0\right),\quad
\left(\frac1{256},\frac5{512},\frac3{160},\frac1{64}\right),\quad
\left(\frac1{576},\frac7{1152},\frac1{40},\frac1{48}\right).
\]

All five satisfy the literal polynomial equations in Lean. Completeness of this real list is currently an exact Python/SymPy elimination result, not a Lean real-algebraic classification theorem. The larger seven-dimensional finite-channel restriction has a separately labeled numerical discovery search, with a fixed seed and 512 random starts, followed by exact rational reconstruction and equation checks. It finds the same five rays. That search is not a complete classification of finite-channel rays and does not exclude additional algebraic or undiscovered solutions.

## Why these rays cannot select the four mixing observables

Let A and B be traceless Hermitian source matrices, with Nu=Tr(A²) and Nd=Tr(B²). In the exact normalization of the source operators, their SU(3) cross potential is

\[
V_4=a(N_u^2+N_d^2)+\left(c-\frac d3+\frac{11h}{40}\right)N_uN_d
+h(\operatorname{Tr}AB)^2+\left(d-\frac65h\right)\operatorname{Tr}(A^2B^2).
\]

Every one of the five rays has d=6h/5. Consequently the independent Tr(A²B²) force cancels. Three rays have no orientation dependence at all. The other two have a positive coefficient multiplying only (Tr AB)². All five are coercive in the radial directions, so the alignment failure cannot be dismissed as a trivial runaway. On a fixed-spectrum orbit, however, one trace cannot determine four independent mixing probabilities.

The calculation uses the four independent entries of a doubly stochastic three-by-three probability matrix as a local chart. For distinct source spectra, the gradients of Tr AB and Tr(A²B²) in that chart are linearly independent. At an interior stationary point of a potential h(Tr AB)²+L Tr(A²B²), stationarity therefore requires L=0. The remaining Hessian is an outer product of one moment gradient with itself and has rank at most one. It leaves at least three directions free. When J² is strictly positive, the unistochastic probability region is locally open, so these are genuine local mixing directions. This excludes an isolated CP-violating alignment in this declared quartic model; it does not classify all boundary vacua or every higher-degree invariant potential.

This narrows the next dynamics problem. A model must supply correlated noncentral interactions with enough independent invariant forces to isolate the frame. Merely selecting one of these scalar rays, or choosing a central phase, cannot accomplish it. Gauge, Yukawa and threshold terms must be included before extending this conclusion to the full quantum theory. The new scalar-ray calculation does not substitute for that work.

## Mixing recovered from weak-basis invariants

For Hermitian sources H_u and H_d with distinct eigenvalues u_i and d_j, define P_ij=|V_ij|² and mixed moments M_rs=Tr(H_u^r H_d^s), for r,s=0,1,2. The spectral theorem gives M_rs=sum_ij u_i^r d_j^s P_ij. Writing V(u) for the constant-first Vandermonde matrix, this becomes M=V(u)P V(d)^T. Lagrange interpolation supplies an explicit inverse, giving

\[
P=L(u)M L(d)^T.
\]

The implementation uses exact rational arithmetic for rational spectra and moments. The Lean proof is more general: it proves the explicit Lagrange/Vandermonde identity and matrix recovery over any field with three pairwise distinct spectral values in each sector. It proves injectivity of the moment map as well. The physical diagonalization-to-trace identity is explained here; it is not asserted to have been formalized by the matrix inversion theorem alone. Degenerate spectra are rejected because they retain frame freedom. Using squared Hermitian sources makes these moments compatible with separate sign shaping, provided their squared spectra are distinct.

An exact CP boundary calculation accompanies the probability interface. For the first two rows set x=P11 P21, y=P12 P22 and z=P13 P23. Then J²=xy-(z-x-y)²/4. A negative result excludes a unitary realization of that doubly stochastic matrix; a positive result retains the two CP-conjugate possibilities. Probabilities and these CP-even moments do not choose the sign of J. That sign remains a vacuum-selection question.

The retained example has rational spectra and a rational interior probability matrix. It tests exact inversion and positive J² without using a measured CKM matrix. This provides a direct interface between an interaction's invariant equations and its observable consequences. Supplying desired moments by hand would still be fitting; the new machinery does not disguise such supplied targets as a prediction.

## A conditional route to electromagnetic normalization

The minimal model's one-loop gauge coefficients above all six vectorlike-quark thresholds are b3=-3, b2=-19/6 and bY=27/2. In GUT-normalized hypercharge, b1=81/10. Positive hypercharge has no nonzero one-loop fixed point, and its running cannot share a positive common gauge ray with the negative non-Abelian beta coefficient. Those elementary polynomial obstructions are now compiled Lean theorems.

A different hypothesis is UV equality of the three GUT-normalized gauge couplings. Let x_i be inverse alpha_i at an anchor scale, U the unified inverse coupling and L=log(Lambda/mu)/(2 pi). With explicitly supplied threshold offsets o_i, the one-loop equations are x_i=U+b_i L+o_i. Two independent non-Abelian anchors determine U and L when b2 differs from b3. The code then derives x1 and alpha_em(mu)^(-1)=x2+5x1/3, accepting no electromagnetic anchor. Lean proves uniqueness of that linear determination. For the minimal coefficients and x2>x3, L is negative, so that action does not unify above the anchor at this order.

The new design atlas enumerates a frozen menu of 35 extensions: zero through six Majorana SU(2) adjoint fermions and zero through four real SU(2) adjoint scalars, all with Y=0. Their exact contributions to b2 are 4/3 and 1/3 respectively; they leave b1 and b3 unchanged. These real representations are anomaly-safe. The atlas publishes every menu entry without ranking against measured alpha. It distinguishes positive-scale, positive-coupling solutions, inconsistent cases and underdetermined cases. Its menu completeness does not mean completeness over arbitrary matter content.

The illustrative anchors x2=30 and x3=9 are explicitly synthetic. For three Majorana triplets and two real scalar triplets, the conditional result is alpha_em(mu)^(-1)=394/3. This is a worked model calculation, not a prediction of the measured fine-structure constant. A physical version needs an independently justified unification action and hypercharge normalization, allowed interactions of the added matter, thresholds, higher-loop running and low-energy matching to alpha(0). The compiler now makes that proposed correlation executable; it does not establish the UV hypothesis.

## Lean work completed and remaining

`PerfectPower/FactorAddresses.lean` supplies an executable equivalence between a typed tuple of finite child indices and Fin(product of child counts). It proves rank/select inverses, cardinality, completeness, safe rejection, zero-factor emptiness and the one-leaf empty product. The rank formula is the same mixed-radix formula used by factored traversals. This closes the typed addressing core of N11. Normalized CRT/chart traversal, weighted variable-size block offsets and generic JSON execution refinement remain separate obligations; the theorem is not a proof of the entire Python atlas interpreter.

`PerfectPower/WeilOldLevel.lean` proves the old-level lift's Gram matrix on literal fibre digits, the square-root normalization, its isometry, and the induced projector's idempotence and symmetry for arbitrary p>0 and m. This closes the old-level isometry part of W1. Literal Fourier/chirp intertwining, the dyadic trace and all-level orbit upper bounds remain open. The result is a real normalized embedding; it is not a new proof of every recursive spectral-plan node.

`PerfectPower/FlavorRG.lean` proves homogeneous ray scaling, the five literal scalar-ray identities, their force cancellation, the radial fixed-point obstruction, gauge fixed-point/ray obstructions, a restricted adjoint-Yukawa reduction ratio, and uniqueness of the conditional unification solution. `PerfectPower/SpectralMoments.lean` proves the explicit spectral interpolation inverse, moment recovery, injectivity and the outer-product Hessian's vanishing on moment-preserving directions. These modules are imported by the main Lean library. The focused compilation and axiom report are retained in the release receipt; no whole-repository build is claimed.

Other pending formalization fronts remain substantial: efficient Sturm checking, generic compiler and parser semantics, Matveev premises, all-level Weil orbit classification and Brainpool/good-reduction field instantiations. The present release advances specific reusable pieces rather than labeling those research fronts closed.

## Reproduction

Run `PYTHONPATH=python python python/develop_flavor_prediction_mechanisms.py` from the repository root. It regenerates `receipts/m22_interactions/flavor_prediction_mechanisms.json`, including the exact tensor replay, complete SU(3) elimination, finite-channel search, orientation ranks, moment example and all gauge-menu entries. The research calculation uses NumPy, SciPy and SymPy; the exact moment and gauge interfaces themselves use the standard library. `PYTHONPATH=python python python/tests/test_flavor_rg_prediction.py` runs the seven focused tests.

With the pinned Lean 4.20.0 toolchain and Mathlib cache installed, run `make prediction-mechanisms-lean` to compile and audit the four new modules. In the managed PID-namespace environment, Lean's numeric `/proc/PID/exe` lookup needed a compatibility shim that substitutes the equivalent `/proc/self/exe` lookup. The shim changes executable-location discovery, not theorem elaboration or kernel checking, and is unnecessary on ordinary Linux installations. Its source is included for reproduction.

The coupling-algebra direction is motivated by Flodgren and Sundborg, *One-loop algebras and fixed flow trajectories in adjoint multi-scalar gauge theory*, https://arxiv.org/abs/2303.13884, and by Haber and Ferreira, *RG-stable parameter relations of a scalar field theory in absence of a symmetry*, https://arxiv.org/abs/2502.11011. The source-derived ray census, trace cancellation and compiled interfaces here apply to the repository's declared model. They do not establish a new universal particle-physics theory or mathematical priority.
