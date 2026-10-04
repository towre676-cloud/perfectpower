# August 2025 recovered: multiplicative equations as integer exponent geometry

This release goes back to the August 17, 2025 binomial and exponent-lattice discussion, well before the current integer repository. It recovers four explicitly recorded equations, recomputes their elimination and lattice data, corrects a missed factor of three, and builds reusable exact solvers. The resulting module computes complete positive-rational solution families and, when a checked weighted product bounds all variables, complete positive-integer lists. A whole-query route substitutes such finite lists into remaining constraints. The calculations use standard-library Python and existing exact arithmetic. They do not establish an empirical Standard Model law, a Weyl symmetry, or a newly compiled Lean theorem.

The point in plain words is that multiplication hides addition. A number has a whole-number exponent for each prime dividing it. Multiplying numbers adds those exponents; taking powers multiplies them. Instead of guessing large candidate numbers or taking approximate logarithms, the program works with these exact prime exponents, solves the resulting integer equations, and puts the numbers back together. It also keeps the restrictions that make that reconstruction lawful: positivity, denominators, prime support and whole-number coordinates.

## The recovered equations and their actual arithmetic

The recorded variable order is `(T,K,P,tau,R,E,g,a,zeta)`. The four original homogeneous equations are

\[
T^6K^3=P^4,\qquad K^{18}\tau=R^9,\qquad
E^{60}=\tau^5g^{24},\qquad a^5=\zeta E^2.
\]

Their integer exponent matrix is

\[
A=\begin{pmatrix}
6&3&-4&0&0&0&0&0&0\\
0&18&0&1&-9&0&0&0&0\\
0&0&0&-5&0&60&-24&0&0\\
0&0&0&0&0&-2&0&5&-1
\end{pmatrix}.
\]

These equations and the original Smith claim were recovered from the August 17 conversation. The old freeze manifest was mentioned in history, but its primary contents were not recovered here. The reproducible input is the explicit matrix above; this release does not claim to reproduce the historical empirical dataset or its freeze.

The historical claim was four unit Smith factors and five free coordinates. The recomputation gives **Smith factors `(1,1,1,3)`**. The constructive unimodular transcript and the separate exhaustive-minor routine agree: the determinantal divisors are `(1,1,1,1,3)`, with all 714 requested minors computed. The rank is still four and the saturated integer kernel still has rank five. The image of `A : Z⁹ → Z⁴`, however, has index three, and its cokernel is `Z/3`. That is a real compatibility condition that the historical unit-factor claim omitted.

To see the condition directly, replace the four unit right sides by positive rational constants `c₁,c₂,c₃,c₄`, so that `x^{A_i}=c_i`. For each prime, write `b_i=v_p(c_i)`. The row combination `h=(0,-5,-1,0)` satisfies

\[
hA=(0,-90,0,0,45,-60,24,0,0),
\]

whose entries are divisible by three. Therefore `-5b₂-b₃ ≡ 0 mod 3`, or `b₃-b₂ ≡ 0 mod 3`. The ratio **`c₃/c₂` must be a rational cube**. The Smith reduction proves that this is also sufficient for a positive-rational lift: there are no other invariant factors or missing rational-span conditions. The runner rejects `(c₁,c₂,c₃,c₄)=(1,1,2,1)` at prime two with an explicit modulus-three row witness, and constructs a complete five-parameter positive-rational family for `(1,1,8,1)`.

Five free exponent directions alone do not imply a `B₅` root system or Weyl action. Such an interpretation needs an actual metric, root configuration, and action preserving the relevant objects. The older physical and symmetry suggestions remain suggestions; the new computation retains exactly the integer data that can be reproduced.

## Hidden-variable elimination

`eliminate_exponents(A, columns)` computes the complete integer module of row combinations cancelling the selected exponents. It constructs the saturated kernel of the transposed selected-column matrix, then applies each returned row combination to the full presentation. Eliminating `K` and `E` returns two independent relations. The historical combinations `(6,-1,0,0)` and `(0,0,1,30)` give

\[
T^{36}R^9=P^{24}\tau,\qquad
 a^{150}=\zeta^{30}\tau^5g^{24}.
\]

These are recomputed in the original nine-variable coordinates. General Laurent consequences require nonzero variables; cancellation cannot silently erase a zero fibre. The result also distinguishes a complete row-combination module from complete existential elimination of integer variables. For example, eliminating `x` from `x²=y` yields no surviving row-combination equation, yet `y` must still be an integer square. The eliminated equations alone do not supply that lifting condition. The finite positive-integer query route below performs the complete reconstruction rather than promoting these necessary consequences into a sufficient answer.

## Every positive-rational solution

`solve_rational_monomial(A,c)` factors the positive rational constants exactly under a trial-division budget, then solves `A e_p=b_p` over the integers at every prime occurring in those constants. A failed fibre returns a prime and a concrete integer image/divisibility witness. For surviving fibres, the particular prime exponents reconstruct a positive-rational point `x₀`.

Let `k₁,…,k_s` be the saturated integer kernel basis returned by the existing unimodular solver. Every positive-rational solution is exactly

\[
x_i=(x_0)_i\prod_{j=1}^s t_j^{(k_j)_i},\qquad t_j\in\mathbb Q_{>0}.
\]

This includes arbitrary new primes in the parameters. It does not restrict solutions to the primes in the original constants. To prove completeness, take the prime valuations of `x/x₀`. Each lies in the integer kernel and has unique integer kernel coordinates. Only finitely many primes occur in these ratios, so those coordinates assemble into rational parameters `t_j`. Conversely, substituting any positive rational parameters annihilates every kernel exponent and reproduces the input constants. Signed kernel exponents correctly carry denominators. No floating logarithm or separately denominator-cleared rational basis is used.

## Complete positive-integer lists from a checked product

For positive integers, a rational family still needs integrality conditions and may be infinite. `solve_monomial` instead requires a checked integer row combination `w` such that every entry of `c=wA` is strictly positive. The input equations then imply

\[
\prod_j x_j^{c_j}=C,\qquad C=\prod_i \mathrm{rhs}_i^{w_i}.
\]

If `C` is not an integer, there is no positive-integer solution. If it is an integer, every prime of every `x_j` divides `C`, and each valuation obeys `0≤v_p(x_j)≤v_p(C)/c_j`. Thus the program has a finite, complete cover. It enumerates the bounded nonnegative valuation fibres, checks all original exponent equations, combines their independent prime profiles, and substitutes every resulting point into the original rational products.

The automatic detector first tries the sum of the rows. If that is not positive in every coordinate, it tries an exact rational solution of `Aᵗw=1` and clears its denominators. Users can supply another integer row combination. Failure to find one means this detector found no bounding certificate; it does not prove that the solution set is infinite. Operation, point-list, dimension and intermediate-bit limits stop with an exception, without returning a truncated complete list. Trial division establishes primality of each factor; a probable-prime label is insufficient for this valuation coverage argument.

When there is only one variable, the checked equation `x^c=C` pins it uniquely. The solver extracts that exact positive integer root rather than factoring a huge known power. It rejects an exponent larger than the value's bit length immediately when the value is greater than one. The example `x³=(10¹⁰⁰+37)³` reconstructs the unique 101-digit integer through this route.

For a genuine multivariable example, `x²y³=2²⁰3¹²` has four compatible exponent profiles at two and three profiles at three, giving exactly twelve positive integer pairs. The signed-exponent system `x²/y³=4/27` and `xy=6` has exactly `(x,y)=(2,3)`. Both results are global within the stated positive-integer domain.

## Whole queries and current corpus replay

`project_monomial_query` recognizes direct multiplicative equalities in one existential QF_NIA query. It selects equations only when every variable involved has an explicit direct positivity assertion. A positivity statement inside an `or` does not authorize global cancellation or the positive-domain solver. Equalities inside disjunctions and negations likewise remain residual constraints.

The complete finite relation is substituted into every assertion, while all remaining integer variables retain their declarations and constraints. A failed integer fibre gives `false`; remaining nonlinear products keep QF_NIA. The existing sort checker selects QF_LIA only when the full reduced query is linear. This route is existentially equivalent because the point list covers every permitted assignment of the eliminated positive variables. It is separate from the finite theorem registry: these computations do not pretend that newly produced point lists have already acquired Lean completeness proofs.

The recovery runner replays all **1,344** actual prime-power rows in `receipts/divisor_sum/prime_power_grid.json`, reconstructing each base from its power equation, and all **218** stored square-product joins, reconstructing each exact root from its divisor-sum value. Those are complete replays of the supplied finite corpus; they do not enlarge its bounded sigma classification into a global one.

Four original/projected SMT examples cover a product with an unrestricted residual variable, a conflicting residual inequality, a square/cube valuation obstruction, and a surviving nonlinear residual. All four agree with Z3, and both SAT models are lifted back and replayed against the original formulas. This is a correctness demonstration, not an industrial speedup benchmark.

## Reproduction and checks

Run `python python/recover_monomial.py` from the repository root to rebuild the historical arithmetic packet, current corpus replay and eight SMT files. Add `--z3` for the optional solver comparisons and model replay. The core runner uses only the standard library. The console provides `monomial-recovery`, `monomial-eliminate`, `monomial-rational`, `monomial-solve` and `monomial-project`.

The fourteen new tests compare the historical Smith result with the independent exhaustive-minor routine, check the two elimination identities, exercise fifty random reconstructed positive-rational families, independently enumerate all small positive solutions for 125 two-variable systems, check domain and budget failures, and preserve the residual query semantics. The full Python suite and fresh-archive replay are recorded beside the results. Existing compiled proofs retain their status. The new source-equation recovery, constructive solvers and query execution remain explicitly exact Python calculations.
