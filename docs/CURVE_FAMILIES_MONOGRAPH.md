# From polynomial families to differential execution

## A reusable bridge

CurveFamily takes y^2=P(x,t) and derives an exact differential system for its periods from polynomial identities. It also derives a selected observable's differential equation, initializes a marked closed-contour period numerically, and continues it along a declared parameter path. Exact parameter domains and bounded integer specializations connect this object to the existing arithmetic catalogue. Eleven persistent object kinds are supported.

P must be monic in x, have x degree 3, 5 or 7, and have rational polynomial parameter coefficients of degree at most four. Smooth fibres have genera one, two or three. Generically singular families are rejected. Explicit algebra, degree and coefficient-size budgets bound the implementation. The exact core uses only the Python standard library; numerical periods use the existing optional NumPy/SciPy backend.

Algebraic de Rham reduction, Gauss-Manin connections, Picard-Fuchs equations and period integration have substantial mathematical precedents. This implementation establishes no worldwide novelty claim. Its direct new capability in PerfectPower is that one family definition supplies the equation, singular fibres, period connection, selected-output operator, integer parameter population and marked continuation.

## Two differential bridges

The algebraic function y obeys 2P D_x y-P_x y=0 and 2P D_t y-P_t y=0 away from P=0. These operators are first order even when the curve has high genus. Their packet retains y^2=P: either differential equation alone permits arbitrary constant multiples, whereas the polynomial relation fixes the sheets. No arbitrary differential equation is asserted to have an algebraic solution.

For monic odd degree m=2g+1, use the 2g differential classes omega_i=x^i dx/y for i=0 through m-2. The first g are holomorphic; the others are differentials of the second kind, with zero residue at infinity, completing a de Rham basis. They are not all called holomorphic.

Differentiation gives partial_t omega_i=-x^i P_t dx/(2y^3). Reduction solves the exact polynomial identity

```text
-x^i P_t/2 = B_i P + R_i' P - R_i P_x/2,
B_i = sum_j A_ij(t) x^j,
degree_x B_i <= m-2, degree_x R_i <= m-1.
```

The final two terms give d_x(R_i/y). After integration on a transported closed cycle, the exact derivative vanishes and the period column satisfies Pi'=A(t) Pi. Every stored identity is replayed. The interpretation uses the classical de Rham basis and transported-cycle construction; Python replay is not a new Lean proof of those analytic statements.

## Exact algebra and singular fibres

RationalFunction implements Q(t) with canonical monic denominators. Addition uses a common denominator, multiplication cancels common factors, and differentiation applies the quotient rule. Structured coefficient arrays are parsed as exact rationals, without expression evaluation or a symbolic-expression parser. Field elimination solves all reduction right-hand sides together.

The discriminant is a Sylvester determinant over Q(t). Monicity makes its result a polynomial. An identically zero result rejects a generically singular family; a zero at specialization rejects that fibre. Budgets check algebraic work, intermediate polynomial degrees and coefficient bits. The work counter is not a CPU-time bound.

For y^2=x^3+k, the short Weierstrass discriminant is sixteen times the polynomial discriminant of x^3+k. Sourced comparisons retain that convention rather than identifying the two values.

## The derived genus-two system

For P=x^5-x+t, the compiler derives Delta=3125t^4-256 and a four-dimensional system. Its first row is

```text
Pi_0' = (-1875 t^3 Pi_0/2 -250 t^2 Pi_1
         +200 t Pi_2 +480 Pi_3)/(3125t^4-256).
```

All four rows and exact derivative numerators are stored. For F=Pi_0 the derived scalar equation is

```text
(50000 t^4-4096) F'''' +600000 t^3 F'''
  +1845000 t^2 F'' +1380000 t F' +84645 F = 0.
```

A marked counterclockwise x-circle centered at 1/2 with radius 13/20 encloses the pair originating at zero and one. The solution is continued from t=0 to t=1/5. Matrix continuation, scalar continuation and a fresh endpoint contour agree to below 1e-8 in the builder. The recorded comparisons are much smaller on this execution, but remain numerical consistency checks rather than certified error bounds.

## Compiling only the requested observable

For F=c(t) Pi, the next differential row is c'+cA. Repeating this rule generates v_0,v_1,... until the first dependency v_r=sum_j a_j v_j. The scalar operator is D_t^r-sum_j a_j D_t^j. Independent preceding rows establish its minimum universal order on the full period module. A particular cycle may have an additional relation and lower order; that stronger statement is not made.

Packets retain derivative rows, the terminal row, monic rational coefficients, a primitive integer polynomial operator and Weyl terms. Coefficients are ordered by derivative degree and ascending parameter power. Denominators are cleared, common polynomial factors and integer content removed, and the highest-derivative coefficient has positive leading term. A formal-series test consumes the derived Legendre operator through the existing Weyl class.

For the genus-two family y^2=x^5+t, the first observable automatically reduces from four period coordinates to order one: 10t F'+3F=0. This matches x=t^(1/5)u, y=t^(1/2)v, under which dx/y scales as t^(-3/10) along consistently transported branches. The release also derives an order-six observable for y^2=x^7-x+t. Reduction does not promise every requested observable a smaller order than the full state.

## Genuine and additional scalar singularities

The discriminant identifies singular fibres. A scalar leading coefficient can have additional zeros at smooth parameters. The packet reports a squarefree polynomial for zeros outside the discriminant. Observable coefficients may themselves have poles, so additional zeros are not automatically asserted removable.

For t Pi_0 on y^2=x^5-x+t, the scalar equation is singular at t=0 although the curve is smooth. Matrix continuation computes that observable at zero and beyond. Scalar continuation rejects a path through its singularity and succeeds from t=1/10 to t=1/5. Both routes agree where applicable. This distinction is executable behavior, not an ambiguous scalar failure treated as a singular curve.

## Exact exclusion on whole parameter segments

Paths contain two through 256 rational complex vertices. Floats are interpreted by their decimal representation for the exact path calculation. On each straight segment t=a+s(b-a), s in [0,1], the backend pulls every excluded polynomial back to exact real and imaginary polynomials in s.

A complex polynomial vanishes there exactly when both real polynomials vanish together. Their rational polynomial gcd describes those common real zeros. Endpoint evaluations and a Sturm count reject every zero on the closed segment. The transcript stores both pullbacks, their gcd, the Sturm chain and interior count. Irrational real collision parameters and poles on purely imaginary paths are detected between samples.

Matrix transport excludes the discriminant and connection denominators. Observable evaluation also excludes its coefficient denominators. Scalar continuation additionally excludes its operator denominators and leading coefficient. A complex detour around the genus-two real collision is recorded. The exact calculation proves absence of the declared polynomial zeros on the rational path; it gives no quantitative pole clearance or certified numerical ODE enclosure.

## Marked numerical periods and transport

Initialization specifies an x-circle, sheet zero or one, and optionally one through eight turns. Numerical roots determine the enclosed roots and separation diagnostics. Turns must close the lift. Continuous logarithms implement the sheet, starting from principal sqrt(P) at the positive-radius point times the declared sheet sign. Independent pointwise square-root choices are not used.

Vector quadrature integrates all de Rham forms. DOP853 transports the period column, a fundamental transfer matrix or the scalar derivative state. Continuation has an evaluation budget. Root diagnostics, quadrature and ODE accuracy remain numerical, with certified_error_bound=false.

The Legendre endpoint check deforms its circle to enclose the same transported pair. Holding the original circle fixed after the moving branch point leaves it would select a different cycle and invalidate the comparison. Both endpoint marks are retained. A square parameter loop around the Legendre degeneration produces a nontrivial numerical transfer with trace two and determinant one. It is monodromy in de Rham coordinates, not an asserted integral symplectic homology matrix.

## Arithmetic, persistence and the workbench

parameter_domain gives the complete semilinear set of integer t satisfying a supplied polynomial/modular predicate and Delta(t)!=0. parameter_population adds bounds and returns an ordinary ExactPopulation specification. Fields retain the parameter and discriminant multiplied by its positive common denominator. A Legendre population on [-10^50,10^50] has 2x10^50-1 members, excluding zero and one without scanning that interval.

integer_points returns every integer point in a declared closed x interval of at most one million steps. Rational polynomial values with noninteger denominators cannot be integer squares. This method has no global completeness claim. The builder hashes the committed 20,000-record Mordell census and compares six specializations on x in [-50,50]. Those bounded comparisons do not inherit or establish global arithmetic theorems.

The persistent catalogue kind curve_family exposes summary, evidence, specialize, observable, parameter_domain, parameter_population, integer_points, marked_period, transport and period_path. Private methods are not exposed. Restart reconstructs the exact connection from its polynomial definition. Derived parameter populations register as ordinary population objects. The service transcript demonstrates differential compilation, exact specialization, bounded arithmetic and marked continuation from one registered object.

Open receipts/curve_families/family_workbench.html locally. It displays recorded Legendre, generic genus-two and isotrivial genus-two trajectories, operators and endpoint comparisons. The slider selects one of 63 recorded samples; it does not execute a new numerical continuation or make the plotted values exact.

## Reproduction and evidence

```sh
export PYTHONPATH=python
python python/develop_curve_families.py --output /tmp/families
python -m unittest discover -s python/tests -p test_curve_families.py
python -m perfectpower service --database /tmp/families.sqlite \
  < receipts/curve_families/service_requests.jsonl
make test
```

Fifteen focused tests cover field laws, classical operators, observable rank and compression, genuine/apparent singularities, exact complex segment exclusion, integer populations, SQLite persistence, numerical sheets and transport composition. Six dense random families in genera one, two and three are compared against independent rational linear systems at eighteen smooth specializations. Optional numerical tests require NumPy/SciPy. The release includes five compiled definitions and three independent matrix/scalar/contour endpoint comparisons.

General cyclic powers, even-degree residue removal, arbitrary degrees, nonmonic leading-coefficient changes, multiple deformation parameters, local Frobenius execution through degeneration, rigorous interval continuation and exact integral homology monodromy remain further work. No new Lean proof or physical interaction is asserted. The complete uncapped archive preserves the previous arithmetic, geometry and physics content.

## Mathematical precedents

Hossein Movasati, Calculation of mixed Hodge structures, Gauss-Manin connections and Picard-Fuchs equations, https://arxiv.org/abs/math/0412235.

Pierre Lairez, Computing periods of rational integrals, https://arxiv.org/abs/1404.5069.

Pascal Molin and Christian Neurohr, Computing period matrices and the Abel-Jacobi map of superelliptic curves, https://arxiv.org/abs/1707.07249.

Manuel Kauers and collaborators, ore_algebra, https://github.com/mkauers/ore_algebra.
