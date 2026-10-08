# Arithmetic charts, singular blowups and unordered determinants

## One equation through several arithmetic worlds

The starting problem is Q(x)+k=y^d, where Q is a rational-coefficient polynomial, k is an integer, d is at least two, and x and y are signed integers. A rational polynomial can be integral everywhere, integral only on a union of residue classes, or integral nowhere. These possibilities are part of the equation's domain. The new pipeline retains that domain while passing through integer-coefficient charts, complete prime-power residue covers, CRT combinations and content-normalized singular branches. It then returns every bounded exact solution in the original coordinates. The determinant machinery uses the same chart coordinates to derive divisibility and auxiliary relations.

The push covers the mathematical and executable cores of work items 6, 7 and 8 in the revised frontier. It uses the shared-factor intersection work already on the shared branch. It does not reopen the wall-decay or flavor lanes. All finite searches have explicit bounds and all local covers have explicit budgets; none of those bounds is presented as a global Diophantine height theorem.

## Denominator-aware power transport

Normalize Q to F/L, with F an integer polynomial and L a positive integer. The original equation is equivalent to F(x)+L*k=L*y^d. The reverse implication is important: the cleared equation itself forces L to divide F(x), so the denominator domain is recovered, not merely assumed. The generic Lean theorem rational_power_iff proves the equivalence from the exact polynomial identity Q*C(L)=map(F). The theorem cleared_power_iff supplies the corresponding integer quotient statement.

The integral input domain is periodic modulo L. Let R contain precisely the residues r from 0 through L-1 for which L divides F(r). Every signed integer input in the domain has exactly one representation x=r+L*n with r in R and n an integer. Define G_r(n)=F(r+L*n)/L. These charts have integer coefficients: the constant is divisible by L because r is admissible, while every positive-degree coefficient in the substituted numerator contains a factor L. Thus Q(x)+k=y^d becomes G_r(n)+k=y^d without division in the chart equation.

A globally integer-valued polynomial can still require several charts. For Q=x(x-1)/2, both parity classes are integral, but Q has rational monomial coefficients. Splitting x into 2*n and 1+2*n produces integer-coefficient polynomials 2*n^2-n and 2*n^2+n. The pipeline deliberately keeps both charts. It does not silently replace a rational polynomial by a polynomial with integer coefficients on all original inputs.

## Exact signed bounds and local covers

A source interval lo<=x<=hi pulls back under x=r+L*n to the exact parameter interval from -floor((r-lo)/L) through floor((hi-r)/L). This formula works for negative endpoints and handles a narrow source interval containing no member of a particular chart. The generic chart_interval theorem proves the equivalence. Empty chart intervals remain visible but contribute no bounded candidates.

For each chart form the integer bivariate polynomial H_r(n,y)=G_r(n)+k-y^d. Existing complete Hensel atlases retain every root at the specified prime powers. Shared primes are joined at their strongest local exponent, and distinct primes retain a factored CRT product. The source-coordinate map x=r+L*n is injective within a chart, and different source residues are disjoint. Therefore modular populations, rank and selection remain exact when transported back to x and signed y.

A candidate is a modularly admissible point, not necessarily an exact zero. The scan first counts the complete candidate population, refuses an exhausted budget, evaluates the original integer chart equation exactly and maps successful points back to source coordinates. No nonintegral rational value can pass through this route. The denominator limit is 64, source degree and power exponent are at most twelve, and each retained prime-power atlas has period at most 256. These are operational limits, rather than mathematical assumptions in the generic theorems.

## Why a singular blowup is a real chart switch

Ordinary Hensel lifting at one fixed prime does not change the derivative residues of a smooth branch: reducing a higher lift gives the same base point, and polynomial derivatives reduce compatibly. Therefore merely relabeling ordinary Hensel nodes would not resolve the missing chart-switching problem.

Instead start with a local equation H and every root (a,b) modulo p. Substitute u=a+p*s and v=b+p*t. Every coefficient of H(a+p*s,b+p*t) is divisible by p. Remove the largest common prime power p^e from all coefficients, obtaining H(a+p*s,b+p*t)=p^e*K(s,t). Since the removed content is nonzero, H vanishes exactly when K vanishes. Classify the roots of K modulo p afresh. A singular parent can now produce vertical children, horizontal children, further singular children or a normalized local obstruction.

The implementation retains every residue root. A child is excluded only when its source cell misses the declared rectangle; a normalized node with no residue root excludes all exact zeros in that node. Smooth children are recognized by a unit derivative in their own normalized equation. Singular intersection branches are retained alongside smooth branches. No choice of a preferred smooth component can erase the remaining source solutions.

## Recursive affine semantics

Every node records an exact identity F(a+m*u,b+m*v)=C*H(u,v), with m positive and C nonzero. The node also records its source residue, normalized sparse polynomial, roots, removed prime exponent and child links. Composition sends the source offsets to a+m*a_child and b+m*b_child, the step to m*m_child, and the content to C*C_child. The generic Chart.compose construction proves that these data form another valid chart of the original source.

The Lean theorem split_zero_cover proves that every exact source zero belongs to one of the complete modular-root charts, including negative coordinates. Chart.zero_iff proves that removing nonzero content preserves exact zero sets. The emitted programs prove every retained node's polynomial identity in the original coordinates, rather than trusting an accumulated floating-point approximation. For the small worked boxes, independent kernel reduction also proves the literal complete source point set.

The Python recursive interpreter is not itself proved to execute these generic semantics for all inputs. The typed chart laws and the emitted source identities are formal; the arbitrary-input traversal refinement remains item 27. This distinction does not weaken the emitted complete finite point certificates, whose source census is checked directly in the kernel.

## Blowup leaves meet shared-factor CRT

At depth e, normalized leaves occupy disjoint source residue cells modulo p^e. They may impose stronger conditions than the ordinary original-polynomial congruence because content removal exposes additional local obstructions. The power-equation route intersects those cells with its existing factored Hensel/CRT cover. Compatibility is tested modulo the gcd of the leaf step and the CRT period, and the surviving cells reconstruct modulo their lcm. This uses the exact shared-factor reconstruction already available in the repository.

Consequently the combined candidate population is no larger than the initial CRT candidate population, while every exact source solution remains. For Q=(x^2+7)/2 and d=2, the box [-20,20] in both coordinates has 32 CRT candidates. Three dyadic normalized blowups reduce the combined cover to 16 candidates and preserve all twelve signed solutions. Their x coordinates are -11, -5, -1, 1, 5 and 11, with the corresponding positive and negative y values 8, 4, 2, 2, 4 and 8. This is a bounded result on a Pell-type equation, not a claim that its global solution set is finite.

For x*y=0 in [-8,8]^2, the blowup tree has 26 nodes, 15 leaves and four genuine chart switches. Both horizontal and vertical children emerge from singular parents. Its 93 candidates yield all 33 exact source zeros. For y^2=x^3 in the same box, thirteen nodes and six leaves yield 31 candidates and five exact zeros. The cusp does not make the same smooth switch as the transverse crossing; the algorithm records that difference.

## The unordered weighted determinant identity

Let C be an n-by-h coefficient matrix, let V be an h-by-n local-vector matrix, and assign a nonnegative integer weight w_a to each local vector. Form A=C*diag(q^w)*V. Multilinearity expands det(A) over choices of h local labels for each row. Repeated labels contribute zero by alternation. Group the injective choices by their unordered label set S; each remaining S has exactly n elements.

The resulting identity is det(A)=sum over |S|=n of q to the sum of the weights in S, multiplied by K_S. Here K_S is the order-free alternating coefficient: the sum over bijections from the row labels to S of the product of their C coefficients times the determinant of the selected V rows. If an ordering of S is chosen, K_S equals det(C_S)*det(V_S). Changing that ordering changes both determinant signs and leaves their product invariant. There is no extra factorial.

The generic Lean powerset_expansion theorem proves the order-free identity over any commutative ring and arbitrary finite index types. It proves that the image sets of injective selections are exactly the subsets of cardinality n. The theorem unordered_divisibility also removes zero alternating coefficients from the weight requirement. If every nonzero K_S has weight sum at least M, then q^M divides det(A), even when smaller-weight subsets exist but their coefficients vanish.

The exact Python producer computes one term per unordered subset using canonical minors, with no repeated ordered selections. It records both minors, their product, the total weight and the weighted term. Native programs prove the literal coefficient/vector minors, assembly identity, full unordered sum and divisor. A general Lean identification of K_S with canonically enumerated minor products remains a separate useful extension; the order-free general identity and the retained finite minor certificates are already kernel-proved.

## Weights derived from actual chart coordinates

For a source chart x=a+m*u and y=b+m*v, expand each chosen source monomial by the binomial theorem. A local monomial u^i*v^j carries the factor m^(i+j). Those total degrees provide the weights automatically. Coefficient matrix C records the center-dependent binomial coefficients, and V evaluates the local monomials at the parameter points. Thus the weighted assembly is the original source-coordinate evaluation matrix, not an unrelated surrogate.

The bridge checks that every supplied point is an actual source zero in the selected bounded leaf. For the crossing chart of step 8, the three points (0,0), (8,0) and (0,8), evaluated against 1, x and y, give determinant 64 and guaranteed divisor 64. This recovers the chart scale 8^2 directly. With three points on one axis, the matrix is singular and the bridge returns the repository's exact auxiliary-relation packet. The packet proves relations on the supplied point set; it does not claim a relation covers every unsupplied source point in the rectangle.

A separate sparse-weight example has nominal weights 0, 2 and 3. Every lower-weight minor coefficient vanishes, so the guaranteed divisor is 2^5=32 rather than the weaker minimum obtained by ignoring coefficient zeros. The retained three-by-five example has ten unordered terms, determinant -101142 and guaranteed divisor 9. A rank-deficient coefficient matrix gives an exact structural-zero example.

## Validation, interfaces and next mathematical avenues

The focused and neighboring suite passes 123 tests. Independent cross-checks compare 36 rational-power boxes covering 10,368 signed source points, another 8,000 points across normalized branching examples at primes 2, 3, 5 and 7, and 96 weighted determinants against direct Leibniz permutation sums. There are ten generated native programs. They cover rational-source identities and all-integer equation transport, genuine chart switches and complete small-box point sets, structural-zero and sparse-weight determinants, and an actual chart-derived evaluation matrix.

The JSONL service exposes integer_power_charts and its population, rank, selection, scan, replay and native operations. branch_integer_power_charts composes blowups with the retained CRT cover, and scan_branch_integer_power_charts returns complete original-coordinate solutions. branching_residue_patch supports direct bivariate integer sources. unordered_weighted_determinant and chart_weighted_determinant expose the determinant calculations and their certificate producers. Run make arithmetic-chart-check to reproduce the corpus, tests, independent censuses and native proof audit.

The most direct continuation is the universal interpreter refinement from item 27: turn every recorded residue split, nonzero content removal, box prune and CRT cell join into one formally evaluated traversal. Another continuation is the all-index canonical-minor identification, so that the executable support-sensitive weight minimum is linked directly to the general powerset theorem. Stronger local geometric weight schedules can then provide determinant-method covers of larger source boxes. Global height bounds, arbitrary maximal-order extraction, elliptic saturation and analytic period continuation remain independent research avenues.
