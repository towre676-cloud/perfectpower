# Divisor coordinates and the recovered occupancy operator

This release recovers the January 8, 2026 construction `w(gcd(i,j))/max(i,j)`, its divisor decomposition and its cumulative-sum implementation. It also turns the unnormalized GCD matrix into a complete exact rational/integer linear solver, connects the construction to the present divisor-sum corpus, and derives an integral tridiagonal inverse for constant normalized weights. These are classical arithmetic and elementary matrix identities assembled into executable machinery. They are not a new perfect-power classification, an industrial solver speedup, or a reproduction of the old spectral experiments.

The branch was caught up through `eb096b3`, including all 3,080 quartic proof lists, native higher-power Runge recognition, rational Voronoi enclosures, integral symplectic surface bases, actual numerical cycle integration and canonical curve metrics. The earlier monomial recovery is present and its concrete arithmetic has received Lean proofs in parallel work. This release adds Python operators and mathematical derivations; it does not claim a new Lean compilation.

For an outsider, the point is that an enormous table of pairwise number relationships need not be constructed to use it. Every relationship in this table comes from shared divisors. We compute those contributions and combine them. For one version, the same coordinates solve every linear equation exactly and say why an integer answer is impossible. For the normalized version, prefix and suffix sums multiply by the table without storing it. We apply these operators to the actual arithmetic census in this repository.

## Recovery and corrections

The older conversations state both `gcd(i,j)^alpha` and the normalized kernel. The current files `Occupancy-Kernel-M29 Dashboard.pptx` and `occupancy_kernel_m29_presentation.pptx.html`, created April 19, 2026, preserve the normalized construction, the correct Dirichlet-convolution identity and prefix-sum idea. This later presentation is not a January experiment freeze. Its historical timings, spectral bands, lead times, liability statements and application outcomes are not adopted as reproduced results. The source receipt records the relevant formulas and correction decisions.

One old conversational formula summed upward over multiples. The required inversion sums downward over divisors:

\[
g(n)=(\mu*w)(n)=\sum_{d\mid n}\mu(n/d)w(d),
\qquad w(n)=\sum_{d\mid n}g(d).
\]

The presentation also claimed positive semidefiniteness for arbitrary positive weights. That is false. For `w(1)=1,w(2)=1/10`, the normalized matrix and a negative-energy vector are

\[
K=\begin{pmatrix}1&1/2\\1/2&1/20\end{pmatrix},
\qquad (1,-2)K(1,-2)^T=-4/5.
\]

The old non-normal interpretation cannot apply to either real kernel in the ordinary Euclidean inner product: both are symmetric, so their commutator with their adjoint is exactly zero. A different weighted adjoint would be a different setting. Solver effort can vary without establishing Euclidean non-normality. The claimed spectral bands and large-parameter limits remain unreproduced hypotheses.

## Exact divisor coordinates

On indices `1..N`, let `D[i,d]=1` when `d` divides `i`, and zero otherwise. This lower triangular integer matrix has diagonal one, so its inverse also preserves the integer lattice. Divisor summation is `D`, and summation over multiples is `D^T`. Their inverses are Möbius transformations, implemented by triangular subtraction without constructing a matrix.

For the raw matrix `G[i,j]=w(gcd(i,j))`, the divisor identity gives

\[
G=D\operatorname{diag}(g(1),\ldots,g(N))D^T,
\qquad x^TGx=\sum_dg(d)\left(\sum_{d\mid j}x_j\right)^2.
\]

Its determinant is the product of the coefficients. Congruence by invertible `D` proves that positive, negative and zero inertia counts equal the corresponding sign counts of `g`. Raw positive semidefiniteness is therefore equivalent to nonnegative coefficients; its rank is the number of nonzero coefficients. Explicit determinants are included through dimension 64, with the product formula retained at every supported dimension.

This belongs to classical GCD-matrix determinant theory. A primary reference is Ercan Altinisik, Bruce E. Sagan and Naim Tuglu, [GCD matrices, posets, and nonintersecting paths](https://arxiv.org/abs/math/0406155). The displayed factorization supplies the argument needed here. No priority claim is made.

To solve `Gx=b`, compute `z=D^{-1}b` and put `u=D^Tx`. The whole system becomes `g(d)u_d=z_d`. A zero coefficient paired with nonzero `z_d` gives an image obstruction. Each nonzero coefficient fixes `u_d=z_d/g(d)`, while each zero coefficient supplies an arbitrary parameter. Applying `D^{-T}` reconstructs every solution, with unique parameters.

This is complete over the rationals. With integral coefficients and right side, an integer family exists exactly when every fixed quotient is integral, because `D^T` is unimodular. A failed quotient returns its modulus and nonzero residue. A successful family has arbitrary integer parameters at the zero-coefficient coordinates. The compressed representation avoids a dimension-by-nullity basis allocation. `lift` evaluates that family. One chosen rational solution is never treated as an integer existence test.

For `w(n)=n^r`, nonnegative integer `r` gives Jordan coefficients `J_r(n)`. Degree zero has only `g(1)=1`, so the raw matrix has rank one. Positive degrees have positive coefficients. The exact preset supports degrees zero through eight; arbitrary exact weight vectors are accepted. Explicit floating mode accepts finite numerical vectors but returns no exact inertia or positivity certificate.

## Normalized blocks and threshold Gram factors

For `K[i,j]=w(gcd(i,j))/max(i,j)`, fix a divisor `d` and write indices as `dk`, with `1<=k<=L=floor(N/d)`. Its block is `g(d)/d` times `H_L[k,l]=1/max(k,l)`. For `v_k=x_{dk}`,

\[
(H_Lv)_k=\frac1k\sum_{l\le k}v_l+\sum_{l>k}\frac{v_l}{l}.
\]

Prefix sums give the first term and backward suffix sums give the second. The backward array avoids subtracting nearly equal floating totals. Summing the blocks gives the entire action. Total divisor visits are `V_N=sum_d floor(N/d)<=N(1+log N)`. Construction, action and raw solving require `O(V_N)` arithmetic operations and `O(N)` storage. Exact bit costs depend on the supplied numbers; these are not constant-time rational operations. Explicit size and visit budgets reject oversized work before returning a result. Exact normalized fractions may become large, and the separate floating route does not certify error bounds.

There is also an exact Gram factorization. Let `U[k,t]=1` for `k<=t`, and set `delta_t=1/(t(t+1))` for `t<L`, with `delta_L=1/L`. Telescoping from `max(k,l)` to `L` proves `H_L=U diag(delta) U^T`. If `p_t=sum_{k<=t}v_k`, then

\[
x^TKx=\sum_d\frac{g(d)}d
\left(\sum_{t<L}\frac{p_t^2}{t(t+1)}+\frac{p_L^2}{L}\right).
\]

Thus nonnegative coefficients suffice for normalized positive semidefiniteness. Every active block is positive definite on its multiples. The exact nullspace consists of coordinate directions whose indices have no active divisor; rank equals the number of covered indices. In particular, `g(1)>0` gives full rank even if all later coefficients vanish. Constant weights give rank one in the raw matrix and full rank in the normalized matrix.

A negative coefficient is inconclusive for normalized positivity because blocks overlap. For example `w(1)=1,w(2)=3/4` has a negative second coefficient but a positive definite normalized two-by-two matrix. The implementation reports `SIGNED_GRAM_INCONCLUSIVE`, preserving this distinction.

## An integral inverse inside the normalized model

With constant weight one, the normalized kernel is `H_N`. Since `U^{-1}` is first difference, `H_N^{-1}=U^{-T}diag(delta^{-1})U^{-1}` is tridiagonal. The diagonal is `2i^2` for `i<N`, with final entry `N^2`; adjacent entries are `-i(i+1)`. Moreover,

\[
\det H_N=\prod_t\delta_t=\frac1{(N!)^2}.
\]

The API `threshold_solve` applies this inverse in linear time. Every integer observation vector has a unique integer lift even though `H_N` is rational. The saved twelve-coordinate example uses observations near `10^30` and reconstructs them exactly. This special inverse is not a linear-time solver for arbitrary normalized weights.

## Actual perfect-power corpus work

The bounded census contains 6,871 square, 957 cube, 273 fourth-power, 128 fifth-power, 44 sixth-power, 52 seventh-power and 33 eighth-power records, with inputs from one to one million. The runner rebuilds `sigma`, checks all 8,358 records against stored values and roots, and checks `sigma(n)=sum_{d|n}d` at all one million coordinates. These are bounded results, without a new global classification.

For raw weight `w=sigma`, the coefficient is simply `g(d)=d`. A finite input set has feature coordinate `c_d`, its number of members divisible by `d`. Consequently,

\[
\sum_{n\in A,m\in B}\sigma(\gcd(n,m))
=\sum_d d\,c_d(A)c_d(B).
\]

Exact factorization and divisor counting build the seven-by-seven Gram matrix of the stored hit sets. It represents 69,856,164 ordered occurrence pairs without enumerating them. Its exact rank is seven; the largest feature support has 26,348 divisors. Forty-nine direct pairings of actual census subsets independently reproduce the sparse result. Inputs belonging to several degrees remain in all corresponding vectors, without a claim of independent statistical evidence. The sigma kernel also encodes the actual square-hit indicator on inputs one through 128; its complete integer solver decodes all 128 coordinates.

These coordinates give exact arithmetic similarity and observation decoding. They do not predict unseen perfect powers or prove finiteness. They can be used alongside the complete arithmetic routes already in the repository.

The fresh 50,000-coordinate benchmark records approximately 0.068 seconds for exact raw construction and action, 0.198 seconds for complete integer solving, and 0.190 seconds for the numerical normalized action. All decoded coordinates match. Ten normalized rows agree with independent direct summation, with maximum observed difference below `9e-16`. A dense float64 table would contain 2.5 billion entries and occupy 20 billion bytes; it is never allocated. These are single current-host timings, not portable promises or reproduced historical timings. The sample comparison does not prove floating accuracy at every coordinate or a spectral growth law.

## Reproduction and scope

Run `python python/recover_divisor_kernel.py`, optionally with `--benchmark`. The script resolves inputs from its own location and can run by absolute path from a downloads directory. It needs only the standard library, including for cold archive replay with `python -S`.

Run `PYTHONPATH=python python -m perfectpower divisor-kernel --family sigma --N 4 --vector '[1,0,1,0]'` for action and Gram energy. Explicit weights use `--weights '[1,3,4,7]'`; a complete integer fibre uses `--rhs '[1,2,3,4]' --domain integer`. Add `--normalized` for normalized action. Console solving covers raw kernels; the threshold inverse is a Python API. JSON fractions are strings and exact console inputs reject floats.

The public module supplies `divisor_transform`, `DivisorKernel.from_weights`, `power_kernel`, `sigma_kernel`, `apply`, `energy`, `certificate`, `solve`, `lift`, `threshold_solve`, `sparse_divisor_counts` and `sparse_pairing`. Direct coefficient construction permits a provably nonnegative Gram choice. No optional numerical library or SMT solver is required.

Fifteen focused tests compare transformations against incidence matrices, random exact actions and energies against dense GCD sums, determinant and rank against independent elimination, and integer decisions against the constructive Smith solver. They reconstruct small integer solutions' parameters, check both positivity counterexamples, prove the constant-weight inverse computationally on exact examples, and compare sparse pairings with direct GCD evaluation. Test execution supports the implementation; the general mathematical derivations above are distinct from a machine-checked Lean theorem. Exact results, source recovery, benchmark, full test log and cold replay are retained under `receipts/divisor_kernel/`. Spectral asymptotics, rigorous large floating error control and formalization of general transform execution remain unfinished.
