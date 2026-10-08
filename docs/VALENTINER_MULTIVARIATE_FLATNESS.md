# Complete multivariate massless elimination and an all-orders determinant criterion

## Abstract

At the normalized link benchmark W=I6bar(K)-5 det K and K0=diag(1,omega,omega^2), the entire three-variable effective superpotential has zero homogeneous terms of degrees three through twelve. This closes the previously possible mixed degree-seven obstruction. Unlike three isolated null-ray checks, the new result uses an exact unisolvent interpolation grid that determines every coefficient. All six massive equations are solved through degree eleven, and the original tensor verifies the local implicit chart. The first possible effective F-energy term is therefore degree twenty-four. An exact Euler identity further reduces all-orders F-flatness to constancy of a single scalar: the determinant of the relaxed matrix. The finite-order cancellation is proved; an exact parametrized F-flat family is not asserted.

## The original nine-field chart

The polynomial is the original 252-term rank-six tensor contraction, with no fitted coefficients. Work over Q(sqrt(5),sqrt(-3)). The base matrix has determinant one and W(K0)=-5/2. Its nine F terms vanish exactly. Its holomorphic Hessian has rank six: the six-coordinate massive block has a verified exact inverse, and three independent null vectors annihilate the full Hessian. The massive indices in row-major order are (0,4,8,1,2,5); the free lower-entry indices are (3,6,7). The null vectors have the identity matrix in these three free coordinates.

Let u=(u0,u1,u2) be these free entries. Write the remaining coordinates as the base matrix, the prescribed null-linear part and six corrections y(u). The holomorphic implicit function theorem gives a unique analytic local graph solving the six massive F equations. The corrections start at total degree two. They are functions of all three coordinates; the graph exists whether or not the remaining three F equations vanish. It should not be confused with an already established F-flat moduli space.

At each degree n, the recurrence takes the degree-n massive residual from the original W, then multiplies it by the negative inverse massive Hessian to determine y_n. Because this inverse is constant and the lower terms are already fixed, y_n is a homogeneous polynomial of degree n in u. Substitution and differentiation commute with restriction to any ray u=t(1,i,j). Thus the exact univariate recurrence computes the value of each full multivariate homogeneous coefficient at (1,i,j), rather than an independent fitted curve.

## A complete exact interpolation calculation

For maximum degree twelve, use every integer node (i,j) with i,j>=0 and i+j<=12. There are 91 nodes, exactly the dimension of two-variable polynomials of total degree at most twelve. At each node solve all six massive equations through degree eleven and substitute into W through degree twelve. Arithmetic, inverses and vanishing tests are exact in the algebraic number field.

The Newton basis is B_ab(x,y)=binom(x,a)binom(y,b), a+b<=12. In increasing total-degree order its evaluation matrix on the same integer nodes is unit lower triangular: a basis element vanishes on earlier total degrees, and within an equal-degree block its value is one only at its own node. The exact determinant is one. This establishes unisolvence without a numerical rank threshold.

For a homogeneous degree-n term W_n(u), the restriction Q_n(x,y)=W_n(1,x,y) has total degree at most n. Its Newton coefficients are exact finite differences. The code reconstructs them and checks the reconstructed values on the entire supplied grid, including nodes beyond the minimal degree-n subset. Every coefficient is zero for n=3,...,12. Homogeneous lifting proves W_n=0 as a three-variable polynomial: vanishing on the dense chart u0!=0 implies polynomial vanishing everywhere, including u0=0.

$$W_{\mathrm{eff}}(u)=-\frac{5}{2}+O(\|u\|^{13}).$$

The linear and quadratic terms vanish by exact stationarity and the Hessian null directions. No mixed degree-seven, eight, nine, ten, eleven or twelve term survives. A deliberately mixed degree-seven test polynomial vanishes on all three older rays but is recovered as nonzero by the new grid; this tests precisely the distinction between sampled-ray evidence and complete coefficient determination.

## Consequence for canonical F energy

Differentiating the effective superpotential gives first possible effective F terms at degree twelve in u. The canonical kinetic metric restricted to the analytic graph is positive and nonsingular at the base, because the three null vectors are independent. Integrating out the massive sector can change the positive metric and higher-order coefficients, but cannot lower this leading-order bound.

$$V_{F,\mathrm{eff}}(u)=O(\|u\|^{24}).$$

Degree twenty-four is the first possible energy degree, not a demonstrated nonzero term. The calculation concerns the specified holomorphic link sector at a=-5,b=1,c=0. Additional scalar selectors, gauge D terms, source couplings, kinetic corrections and quantum effects need their own analysis and are not declared flat by this result.

## Exact all-orders reduction to determinant constancy

The original W has only cubic and sextic homogeneous pieces. Euler's identity holds as an exact polynomial identity in all nine entries:

$$\sum_{i=0}^{8}K_i\frac{\partial W}{\partial K_i}=6W+15\det K.$$

On the implicit massive graph, the six massive derivatives vanish. The three remaining entries are exactly u0,u1,u2, and the chain-rule contributions from the massive coordinates vanish. Defining E=sum u_i partial/partial u_i and D_eff(u)=det K(u), the identity becomes

$$(E-6)W_{\mathrm{eff}}=15D_{\mathrm{eff}}.$$

For homogeneous coefficients this is (n-6)W_n=15D_n. At degree zero it gives W0=-5/2 since D0=1. Degree six is the only resonance: determinant constancy would allow an arbitrary degree-six W term, but that term has already been proved zero by the complete multivariate elimination.

Consequently, on this particular implicit chart with W6=0, the following equivalence is exact: D_eff is identically one if and only if W_eff is identically -5/2, if and only if all nine original F terms vanish throughout the graph. For the reverse direction, all nine F terms make W constant, and Euler then makes D constant. For the forward direction, coefficientwise solution of the Euler equation eliminates every W term except the degree-six resonance; the known W6=0 removes that exception. The invertible nine-coordinate chart then turns the zero effective derivatives and six solved massive derivatives into zero original derivatives.

This is a necessary and sufficient local criterion, not a proof that its condition holds. The complete degree-twelve result already implies D_eff=1 through degree twelve. An all-orders determinant identity on the massive graph would settle the exact-family question without evaluating infinitely many jets.

## Reproduction

Run PYTHONPATH=python python python/develop_valentiner_multivariate_flatness.py. The default degree-twelve calculation uses six independent worker processes and writes receipts/m22_interactions/valentiner_multivariate_flatness.json. The receipt contains all 91 node calculations, every reconstructed homogeneous coefficient, the exact chart check and the Euler criterion. Worker count changes scheduling, not mathematical output. The command accepts --order and --workers for other finite orders; a nonzero reconstructed coefficient is retained rather than replaced by a zero claim.

Run PYTHONPATH=python python -m pytest -q python/tests/test_valentiner_multivariate_flatness.py python/tests/test_valentiner_selected_quantum.py. The focused checks cover unisolvence, reconstruction of nonzero algebraic coefficients, an obstruction missed by the old rays, complete grid coverage, original-tensor replays at interior and boundary nodes, the exact chart and Euler identity, and regression checks of the preceding radial quantum calculation. A fresh archive extraction repeats the entire grid and reproduces the receipt byte for byte.

## Result and boundary

The candidate degree-seven obstruction and its degree-twelve energy consequence are closed. The full effective superpotential is constant through degree twelve, and the energy bound holds in every null direction. Exact all-orders flatness has been reduced to one determinant identity. No claim of a complete global F-flat census, a CKM prediction or an exact all-orders parametrization follows from a finite jet.
