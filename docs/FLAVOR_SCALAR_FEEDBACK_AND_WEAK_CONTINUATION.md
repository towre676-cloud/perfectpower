# Scalar quantum frame forces and a stable weak continuation

## The highest-value calculation

The complete singlet/finite-mediator action now has a calculated 49-field scalar quantum force, a twelve-dimensional fixed-spectrum angular response, and a solved local stationary branch of its neutral-scalar-plus-quark one-loop potential. This addresses the quantum-vacuum calculation absent from the preceding protected interaction. It includes the non-Gaussian singlet self and portal extension, all 28 mediator modes and the full quark spectrum. The relative frame force is supplied by scalar fluctuations; the quark determinant remains exactly orientation independent at fixed source spectra.

The original coupling point does not admit a small-displacement interpretation: the linear scalar-plus-quark shift has norm approximately 7.2965 times the full tree vacuum norm. A constructive weak-coupling continuation preserves every tree scalar and Dirac mass matrix, pole residue and charged-current frame while suppressing the relative loop shift. At r=10 to the minus six the specified neutral-loop potential has a converged local stationary point, positive corrected curvature and nonzero physical weak CP. This is a conditional quantum local branch, rather than a prediction of observed mixing or a full gauge-inclusive vacuum.

## Full scalar Hessians and quantum derivatives

For the 21 source/Higgs coordinates z and 28 mediator coordinates sigma, retain the complete Gaussian squares M squared norm[sigma+J(z)/M squared] squared/2 and their source contacts. The currents are quadratic, with constant Hessians Q_i and linear Jacobian D. Away from the source-profiled surface the source-source Hessian is H_source+D-transpose D/M squared+sum_i [sigma_i+J_i/M squared]Q_i. The source-mediator block is D-transpose, and the mediator block is M squared I. Omitting the sum of current Hessians gives the wrong off-surface derivatives.

The non-Gaussian extension adds r3 t cubed/3+r4 t fourth/4+t squared[K(z)-K(z0)]/2, where t is the singlet displacement. Its value, gradient and Hessian vanish at the retained tree vacuum, but its third derivatives do not. The calculation includes its source/singlet mixed derivatives, the derivative of the singlet curvature and the cubic contribution. Thus it tests interactions that cannot be distinguished by the preceding tree spectrum alone.

For a positive scalar Hessian H, the finite MS potential is Tr[H squared(log(H/mu squared)-3/2)]/(64 pi squared). Its force is Tr[H(log(H/mu squared)-1) partial_i H]/(32 pi squared). Spectral functional calculus evaluates this trace directly without subtracting large mediator vacuum energies. The driver calculates all 49 canonical force components, rather than differentiating a mass-only low-energy truncation.

The quantum curvature uses divided differences of x[log(x/mu squared)-1], with the logarithmic derivative on repeated eigenvalues. Its fourth-derivative contraction is evaluated by polynomial polarization. Since the Hessian is quadratic and quartic interactions live in the 21 source coordinates plus the singlet, diagonalizing the corresponding 22-dimensional block of the spectral weight reduces the contraction to Hessians at opposite eigen-directions. Full fourth-tensor permutation symmetry makes this an exact polynomial identity. It avoids a four-index tensor and avoids taking loop differences at displaced backgrounds with tachyonic bare spectra. Independent finite-gradient checks test the resulting curvature.

## What supplies the frame force

Each nondegenerate Hermitian adjoint has a six-dimensional unitary conjugacy orbit. Orthonormal tangent bases for both sectors give twelve canonical isospectral directions. Fixing the source singlets and Higgs coordinate on these orbits also fixes the singlet current and the six signed source eigenvalues. Quark masses and doublet weights consequently remain fixed. The finite family-group scalar potential has positive curvature in this angular subspace at the retained tree vacuum.

After eliminating the mediator displacement in the force, the scalar orientation-force norm is approximately 0.00371446 at mu=1. The corresponding quark orientation force is approximately 5.3 times ten to the minus seventeen, in agreement with the exact fermion determinant theorem. Four independent direct differences of the full 49-scalar potential agree with the spectral-trace force to about 1.1 times ten to the minus eight in absolute error. The constrained angular linear displacement is approximately 0.2621 times the source norm at the original coupling point.

The centered non-Gaussian extension changes the full radial force while preserving the angular force. Its invariant K and singlet displacement remain constant along the exact isospectral orbits, so the extra local scalar Hessian vanishes there. This is a property of this specified extension, not a theorem that general non-Gaussian interactions cannot change frame selection. Neither the scalar force nor the retained frame is fixed to the golden CKM relation.

## An exact weak-coupling family with unchanged tree physics

For any positive r define V_r(X)=V_1(sqrt(r)X)/r and D_r(X)=D_1(sqrt(r)X). The vacuum is X_r=X_1/sqrt(r). A degree-d scalar coefficient scales as r to the power d/2-1: quadratic masses remain fixed, cubic couplings scale as sqrt(r), and quartics scale as r. All dimensionless quark Yukawas scale as sqrt(r); bare quark masses remain fixed. The dimension-one mediator-current coefficients therefore scale as sqrt(r), while the matched quadratic mass-insertion coefficients scale as r. Their cross-sector row ratio remains unchanged.

At the scaled tree vacuum every scalar Hessian, Dirac matrix, canonical pole residue and charged-current frame is exactly unchanged. The one-loop scalar and quark potential values are unchanged there, their canonical gradients scale as sqrt(r), and the relative linear vacuum shift scales as r. Neutral-scalar quark mass corrections scale as r because both vertices scale as sqrt(r). Six executed continuation points check the full matrices and corrections; their tree-matrix errors are at floating-point precision. The first-order neutral determinant-phase cancellation remains protected by the same Hermitian/singlet vertex structure.

This continuation does not hold measured gauge couplings fixed. Gauge masses and analogous gauge-loop scaling would remain unchanged only if those couplings also scale as sqrt(r). The construction therefore establishes a controlled local interaction family; it does not turn the retained conditional spectrum into a Standard Model fit.

## The soft-mode condition and solved local branch

A small displacement relative to the whole vacuum is insufficient to control a soft scalar mode. At r=0.001 the relative linear shift is only about 0.00730, yet the bare Hessian at that displaced background has a negative eigenvalue near -0.001013. Even r=0.00001 crosses the positive bare-spectrum domain. The driver records these spectral checks rather than evaluating a real logarithm on tachyonic eigenvalues or presenting the displacement as a new vacuum.

At r=0.000001 the positive-spectrum domain survives. In coordinates Y=sqrt(r)X, solve grad[V_tree(Y)+r V_CW,neutral+quarks(Y)]=0. The iteration converges in two updates, with maximum canonical rescaled tadpole residual approximately 1.3 times ten to the minus fifteen. The corrected scalar curvature has smallest eigenvalue approximately 1.12549 times ten to the minus five. The relative displacement is approximately 7.2973 times ten to the minus six. These are numerical local checks, not interval-certified existence or global-minimum results.

Canonical quark matching at the loop-selected background gives a nonzero quartet J approximately 0.000262009. These masses and currents are tree quantities evaluated at that background. The calculation separately evaluates the first-order neutral-scalar quark correction with the scaled vertices; it does not replace complete finite wavefunction and gauge matching. The three Higgs Goldstones give zero first-gradient contribution at the tree vacuum by the zero-mass limit. Their resummation away from that vacuum, gauge diagrams and higher-loop effects remain outside the solved neutral-loop subsystem.

## Reproduction and implication

Run PYTHONPATH=python OPENBLAS_NUM_THREADS=1 python python/develop_flavor_scalar_feedback.py. The receipt contains both Gaussian and non-Gaussian forces, two MS scales, angular checks, six weak-continuation points, explicit soft-spectrum failures and the positive local stationary branch. Tests independently check polynomial Hessians, third tensors, the spectral force and scale convention, canonical-coordinate scaling, matrix and mass-correction identities, angular neutrality of the fermions and the stationary residual.

The substantive advance is a quantum-tested local protected interaction family with a quantified scalar frame force and a constructive way to enter its controlled regime. It establishes which sector can select the frame and how soft modes constrain that calculation. A representation-derived correlation selecting the golden relation, the full physical gauge-coupling vacuum and global CP selection remain distinct requirements.
