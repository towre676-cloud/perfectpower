# Semilinear capacity: queryable equations and exact integer dynamics

PerfectPower now exposes supported equations as reusable solution spaces. A caller can restrict a family by polynomial inequalities and congruences, count its solutions, select admissible parameters at enormous ranks, and find every global optimizer in the original coordinates. Complete generators can pass through polynomial compositions and content scalings. Some apparently infinite power-curve charts are refined into complete finite lists by solving their nonlinear integer images.

This is a structural expansion of the previous polynomial and Gamma machinery. The new arithmetic core uses Python integers and rational numbers, with no runtime dependency beyond the standard library. It preserves the concurrent Lean transport and tied-optimizer formalization. Exact replay checks the supplied evidence; the new Python producer and its general domain interpretation are not Lean-verified.

## Boolean polynomial and modular domains

The one-variable input language accepts Boolean combinations of integer polynomial sign comparisons and comparisons of a polynomial remainder with an integer value. A sign atom compares an ascending-coefficient polynomial with zero. A modular atom has a positive constant modulus and uses the ordinary nonnegative remainder. Thus inequalities on remainders, values outside the remainder range, negation, and disconnected domains have their literal meanings.

Polynomial signs change only at finitely many real roots. The existing exact root transcripts partition the integer line into sign cells. Modular atoms are periodic: if every modulus divides M, polynomial evaluation at n+M has the same remainder as evaluation at n. Crossing the root-free sign cells with a finite residue truth table therefore produces disjoint cells of the form

$$
\{n\in\mathbb{Z}:a\leq n\leq b,\ n\equiv r\ \mathrm{mod}\ m,\ r\in R\}.
$$

An endpoint may be infinite. The residue truth pattern is reduced to its least period on each sign cell; the original least common multiple need not remain the execution period. Empty bounded residue cells are removed and compatible adjacent cells merge. This preserves every admissible integer, including negative coordinates and isolated roots.

For a bounded interval the count is a sum of floor differences:

$$
\sum_{r\in R}\left(\left\lfloor\frac{b-r}{m}\right\rfloor-\left\lfloor\frac{a-1-r}{m}\right\rfloor\right).
$$

Rank selection uses these exact counts with doubling and binary search. It never scans all preceding integers. The rank is zero-based among admissible integers at or above the requested start, defaulting to zero. A rank beyond a finite domain returns no selected value. The reported nonnegative density is the exact limiting density in the positive tail; it is not a density of arbitrary perfect-power values or a symmetric density over both tails.

Default limits are degree 64, 16,384 coefficient bits, 128 atoms, Boolean depth 64, 2,048 Boolean nodes, residue period 65,536, one million residue/Boolean work units and 100,000 root nodes. A limit stops the exact construction rather than returning a partial domain as complete.

## Optimization follows the admissible step

On a residue class with period m, consecutive admissible coordinates differ by m. The relevant descent polynomial is consequently

$$
\Delta_m G(n)=G(n+m)-G(n).
$$

Using only the unit forward difference would miss behavior on sparse arithmetic progressions. The implementation isolates the period difference once per distinct reduced cell period. Each residue class contributes its first and last admissible endpoints where these exist, plus the nearest admissible predecessors and successors around the critical integer cells and their step successors. Exact evaluation of this finite candidate set retains every tie.

Objective tail signs detect an unbounded minimum or maximum. An empty feasible domain returns EMPTY. For a constant objective the optimizer set is the entire feasible domain, which may be infinite. Shared root budgets cover the feasible-domain and objective-difference evidence together. A test translates a sparse lattice to a coordinate of size 10^60 and retains both nearest ties without traversing the intervening range.

## Complete signed power-curve charts

The relation recognizer searches expanded polynomials for identities L(x)=A(x)^p+k and R(y)=B(y)^q+k with integral root polynomials and a shared constant offset. It checks the reconstructed identities exactly. For p,q at least two, let g be their greatest common divisor, u=p/g and v=q/g. Every solution of the reduced power relation belongs to a chart

$$
A(x)=\epsilon_A t^v,\qquad B(y)=\epsilon_B t^u,\qquad t\geq0,
$$

where each epsilon is either sign and their original powers agree. Coprimality of u and v gives completeness through prime exponents. There are two or four sign charts. Exactly one chart owns t=0; all others start at one. In particular x²=y² includes both diagonal and antidiagonal solutions. Equality of a shared nonlinear outer polynomial never justifies cancelling that outer polynomial without injectivity.

For affine A(x)=a*x+b, the original coordinate is (epsilon*t^v-b)/a. Normalize the denominator to be positive and retain its exact divisibility condition. The resulting parameter image is a semilinear domain. Affine translations, negative slopes, nonunit slopes and all witness signs survive the transport.

For nonlinear A, the chart instead retains the complete integer fibre equation A(x)=epsilon*t^v. Evaluating one parameter isolates every integer root and forms the full Cartesian product of both coordinate fibres. The evaluator checks the original equation and records the root evidence under a shared work budget. It does not assume that a nonlinear polynomial image is periodic or injective.

A GENERATOR describes exact coverage by a structured parameter family. Its original image may still be finite, empty or unclassified; this status alone is not a proof of infinitely many distinct original points.

## Solving the nonlinear image

When a nonlinear chart fibre reduces to an already supported finite power equation, its complete parameter set can be recovered. Every admitted parameter is then evaluated through both original coordinate fibres, with all signs and divisibility conditions retained. A finite answer is returned only when every nonempty chart closes. An unresolved chart leaves the complete source generator available.

The recursive finite-image route reduces the sum of the original polynomial degrees before reusing existing arithmetic leaves. It can thus use a proved Mordell packet inside a higher-degree power relation. For example,

$$
(x^2-1)^2=y^3
$$

has exactly the five points (-3,4), (-1,0), (0,1), (1,0) and (3,4). Minimizing x²+y² gives value one at the three points (-1,0), (0,1) and (1,0). A chart that initially presents this as a power family is refined into the complete finite answer.

A separate broad finite class is F(x)=y^d with even d and a negative leading coefficient in an even-degree F. The necessary domain F(x)>=0 is bounded. Exact sign cells give its complete integer argument set, and residue filters precede the surviving power checks. Work is charged to actual candidates and root evidence. For F(x)=1-(x-H)², even an H of size 10^60 leaves only three argument checks and four signed square solutions.

## Querying equations in original coordinates

The curve-query interface accepts Boolean polynomial predicates in x and y, optional constant-modulus comparisons, and a polynomial objective in the original coordinates. Explicit charts substitute rational polynomial coordinates into those expressions. Positive denominator clearing preserves sign comparisons. If an integer-valued chart expression is N/D, its modular comparison can be translated exactly to the corresponding comparison of N modulo D*m with D times the original remainder threshold. Coordinate integrality is retained before this translation is used.

The reduced parameter predicates feed the same semilinear domain and discrete optimizer. Chart sign branches are disjoint, including ownership of zero, so counts add without double-counting original solutions. Global optimum values are compared as exact rational numbers across charts. Every original-coordinate tie is retained. Large finite answers remain structured when they exceed the requested materialization limit; constant objectives can retain an infinite optimizer family.

Finite nonlinear-image curves use their complete original point lists for predicate evaluation and optimization. A nonlinear image that cannot be classified does not receive an unsupported global count or optimum.

For x²=y³ with both coordinates between zero and 10^90, the count is 10^30+1. Over the full integer curve, minimizing (y-10^60)² gives value zero at both original points (minus 10^90,10^60) and (10^90,10^60). Neither query enumerates the huge box or parameter range.

## Composed generators and solver transport

The arithmetic family evaluator interprets exact-power, constant-coordinate, power-chart, content-scaled and polynomial-pullback generators. A polynomial pullback evaluates every integer inner fibre; content scaling restores the witness coordinate. Nested generators keep their source evidence and use a shared root budget. A complete generator is never converted into a finite answer by sampling it.

The SMT simplifier now recognizes a supported separated relation in two original integer variables, folds its polynomial and constant-modulus side conditions into the charts, and emits one fresh parameter with an exact interval/congruence disjunction in QF_LIA. Reverse lifting produces original coordinates satisfying the original assertions. The existing multivariate normalizer has degree-eight scope; the final one-variable polynomial/modular domain pass has degree-64 scope. Residual operations outside those parsers remain for the downstream solver. Branch expansion has its own bound.

## Gamma as a domain-aware input boundary

Fixed-shift Gamma quotients, finite products and fixed-width binomials normalize into a polynomial numerator over a positive constant denominator. The Gamma domain and optimization interfaces now accept the modular domain machinery while retaining the natural-index restrictions and normalization evidence. A growing factorial ratio keeps its valuation and recurrence representation rather than being expanded into a fictitious fixed polynomial.

For a polynomial-coefficient recurrence Q(n)*a(n+1)=P(n)*a(n), the simultaneous nonvanishing of P and Q modulo a prime is an exact periodic query. It identifies indices where the original recurrence coefficients are units. This statement concerns those coefficients; it does not classify the factorial ratio itself as a perfect power, and it uses the original coefficients rather than cancelling modular factors.

## Stored experiments and independent references

The source quartic ledger contains 3,080 previously complete quartic packets. Every quartic receives a constrained global minimum query using two residue classes modulo seven and a polynomial nonvanishing condition modulo five. An independent exhaustive reference scans a Cauchy bound derived from the ordinary derivative with a residue margin. All 3,080 optimum values and complete tie sets agree.

Every quartic also yields the negative-leading square equation -F(x)=y². An independent Cauchy-bound scan and integer square-root calculation checks every signed point. All 3,080 complete finite answers agree. These are new query workloads constructed from existing mathematical data, not additional independently sourced quartic equations.

The independently sourced table of 52 Bober factorial-ratio families supplies the original hypergeometric recurrence coefficients. Thirteen primes from five through 47 give 676 modular domains. Independent literal affine-factor evaluation checks each residue set, its exact density, its count through 10^100 and its selected coordinate at rank 10^100. Every result agrees.

All 131 available unconditional nonzero Mordell targets between -100 and 100 supply two finite-image presentations each: ((a*x+b)²-k)²=y³, with (a,b)=(1,0) or (3,k mod 7 minus 3). The reference maps every original complete Mordell point through signed coordinates and exact divisibility, independently of the new chart refinement. All 262 equations now return COMPLETE. Running the same inputs against the preceding polynomial engine gives 24 complete answers, so the expansion adds 238 complete answers on this defined set.

The baseline code is the Python subtree 55cbceb7afcdc73601932a246d8df0e3a4f60d9b, present in published commit 5cdb3dd1039c0db9d89ba0c03bc0acc0827c26f0 and unchanged by the subsequent Lean-only commit c4593987a9a43484156af5e6a7e7e78baee7593c. The receipts record the comparison inputs and statuses, source hashes and exact answers. The new corpus has zero disagreements.

Another 128 constructed boxed curve queries compare complete point sets and bivariate-objective ties against all integer pairs in a 61-by-61 box. Separate enormous-coordinate examples check structured counting and both original optimizers. The previous 6,422-equation, 3,080-objective corpus is rerun as a regression. These coverage results establish neither an industrial speed advantage nor a comparison with every competing polynomial solver.

## Proof scope and the next mathematical frontier

The prior thirteen Lean laws for polynomial transport, Boolean cells and tied optimizer certificates are preserved. The earlier coprime-power parameter theorem supplies a relevant formal mathematical building block. This expansion introduces no new Lean module. The semilinear producer, generic residue interpretation, period-step candidate assembly and arbitrary nonlinear root transcript remain exact Python evidence with execution_verified set to false.

A generic Lean interpreter for interval/residue cells and period differences would make the new receipts reusable formal input. A separate arithmetic frontier is coefficient-bearing power relations such as c*A(x)^p=d*B(y)^q, using prime-exponent compatibility to build finitely many primitive charts. General nonlinear parameter images and broader separated-polynomial classification require additional mathematics. The current implementation claims its explicit classes and preserves unresolved scope.

## Reproduction and public interfaces

Run from the repository root with Python 3.10 or later. The monograph renderer separately requires ReportLab, Matplotlib and DejaVu fonts. Coefficient lists are ascending, and curve expressions use the names x and y.

```sh
PYTHONPATH=python python -m perfectpower semilinear-domain --predicate '{"poly":[0,1],"modulus":7,"relation":"=","value":3}' --interval '[0,1000000]' --select 1000000 --verify
PYTHONPATH=python python -m perfectpower polynomial-charts --left '[0,0,1]' --right '[0,0,0,1]' --parameter 2 --verify
PYTHONPATH=python python -m perfectpower curve-query --left '[1,0,-2,0,1]' --right '[0,0,0,1]' --objective 'x*x+y*y' --verify
PYTHONPATH=python python -m perfectpower family-evaluate --coeff '[1,2,1,0,2,2,0,0,1]' --d 3 --parameter 1 --verify
PYTHONPATH=python python -m unittest discover -s python/tests -p test_semilinear_capacity.py
PYTHONPATH=python python python/develop_semilinear_capacity.py
PYTHONPATH=python python python/develop_polynomial_capacity.py --output /tmp/polynomial-regression
make test
python python/render_polynomial_monograph.py --edition semilinear --output /tmp/Semilinear_Capacity_Monograph.pdf
```

The finite-image curve example returns the three tied optimizers described above. The family example is (x⁴+x+1)²=y³; its complete fibre at parameter one contains (-1,1) and (0,1). To reproduce the baseline comparison, add --baseline-python pointing to the prior checkout's python directory. Saved new receipts are under receipts/semilinear_capacity, with final test logs and a regression summary. The four final Python suites ran 822 tests: 818 passed and four were skipped. The focused module contains 34 tests, including randomized independent references, negative slopes, all sign branches, nonlinear fibres, tampering, work limits, empty sets, constant objectives and huge coordinates.
