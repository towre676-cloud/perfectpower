# Height, bounded arithmetic oscillators, and Pauli transport

Research account — October 13, 2026. This is a self-contained numerical and mathematical research push. The package contains executable source, all retained observations, and the derivations below. It does not claim a Riemann-hypothesis proof, a new prime generator, or historical priority for the underlying ballot-path, Pauli, or Schur-complement techniques.

## Outcome

The strongest result is an exact connection between arithmetic height barriers and the first nonzero coefficient of transport between perfect powers. Pure prime multiplication/division protects a d-step return order. The d-th compressed off-diagonal operator is exactly the original prime graph on the roots, with weights raised to the d-th power. Between p^d and q^d, shortest paths under the cutoff q^d become lattice paths beneath an irrational logarithmic boundary. Their normalized count has an explicit positive limit and a computable first finite-size correction. This is a derived application of established probability and spectral machinery, with independent finite arithmetic checks; historical novelty has not been established.

The primary computation ran 620.032 seconds of elapsed time, with 619.862 seconds of process CPU time. It executed 270 deterministic arithmetic spectral cases and 9188 adaptive matched-population controls. An additional deterministic control program evaluated 1,440 anchored or height-stratified masks, plus 90 target spectra. The combined spectral file contains 10,988 rows. Pauli matrices have dimensions up to 768. Exact boundary counts reach N=2,000,000. Four ballot families were counted through d=2048, followed by a held-out (2,3) calculation at d=4096. No deliberate waiting or sleeping contributes to the computation receipt.

## Arithmetic operator and exact return theorem

Let S_p|n> = |pn> and let C_N be the symmetric adjacency operator on 1≤n≤N with edges n↔pn, weighted w_p, for a finite prime set. Let P_d select exact d-th powers and U_d|a>=|a^d>, for a≤floor(N^(1/d)). Let offdiag remove diagonal entries in the arithmetic basis. A walk changes the prime valuation vector by unit coordinate steps. Distinct d-th powers have valuation differences divisible by d. Therefore fewer than d edges cannot connect them. At exactly d edges, the only possible nonzero difference is ±d in a single prime coordinate; every step must use that prime in the same direction. All intermediate values lie between the endpoints, so finite height truncation removes none of these paths.

The resulting identities are offdiag(U_d* C_N^k U_d)=0 for 1≤k<d, and offdiag(U_d* C_N^d U_d)=C_floor(N^(1/d))(w_p^d). Meanwhile U_d* H_N U_d=d H_floor(N^(1/d)), where H_N=diag(log n). The diagonal part of C_N^d contains return walks and is deliberately retained separately. Calling the full compressed matrix equal to the root graph would be false. The program checks 80 weighted integer matrix-power identities across 20 parameter choices, in addition to the earlier unit-weight selection checks.

For connected roots a,b in the same prime-generated component, multiplicative graph distance satisfies dist(a^d,b^d)=d sum_p |v_p(a)-v_p(b)|. The lower bound follows from valuations; decreasing to the gcd and then increasing to the endpoint realizes the bound within the maximum endpoint cutoff. If N≥lcm(a,b)^d, every shortest step ordering is permitted and the number of shortest paths is (dL)! / product_p (d |v_p(a)-v_p(b)|)!, with L=sum_p |v_p(a)-v_p(b)|. A tighter height cap can remove step orderings without increasing the shortest distance. The package records 448 exact geodesic cases and independently checks 224 unrestricted multinomial identities.

## Pauli transport

Define D=σ1⊗C+σ2⊗H+mσ3⊗Q, where Q=I-P is the nonsolution projector. These are finite self-adjoint matrices. The infinite diagonal-height construction with bounded C,Q is self-adjoint on the height domain and has compact resolvent when height sublevels are finite. In the finite model, diagonal height and mass insertions cannot change the arithmetic label. Consequently the first nonzero off-site coefficient between distinct d-th powers occurs at order d and has spin factor σ1^d. Specifically, the amplitude from a^d to (pa)^d begins (-it)^d w_p^d σ1^d/d!, and the spin-summed probability begins w_p^(2d)t^(2d)/(d!)^2. These are small-time asymptotics, not guarantees of large-time transfer.

For real symmetric C,H,Q, the antiunitary J=(σ2⊗I)K satisfies JDJ^-1=-D and J^2=-I. Thus ± pairing is forced by the construction. The largest measured pairing defect is 4.476e-13. It cannot be interpreted as evidence that the spectrum knows the Riemann zeros. At m=0, D has no dependence on the population projector at all: all arithmetic labels produce identical spectra for fixed N,C,H.

## Height-barrier ballot theorem

Consider shortest paths from p^d to q^d, with p<q, confined to integers at most q^d. There must be d divisions by p and d multiplications by q. Reverse each path. A prefix with u p-increments and v q-increments is permissible precisely when p^u≤q^v. The exact count A_d is therefore the number of monotone paths (0,0)→(d,d) satisfying u log p≤v log q. No approximate logarithmic comparison is needed in the implementation; all admissibility decisions compare integer powers.

Define α=log(q)/log(pq)>1/2 and b_n=2^-n sum_{k>αn} binom(n,k). The survival constant is c_pq=exp(-sum_{n≥1} b_n/n). The series converges exponentially. With I=α log(2α)+(1-α)log(2(1-α)), its remaining logarithmic sum after L terms is at most exp(-(L+1)I)/((L+1)(1-exp(-I))). The numerical constants use 65-digit arithmetic and exact integer binomial tails. The truncation bound is analytical; floating-point rounding has not been enclosed by interval arithmetic.

The limit A_d/binom(2d,d)→c_pq follows by comparing any fixed prefix of a uniformly sampled balanced bridge with independent fair steps. Sampling without replacement tends to independent sampling on fixed prefixes. For both models, the probability of a forbidden prefix after K is bounded uniformly by a geometric sum of Chernoff bounds, because α>1/2. Letting d tend to infinity and then K tend to infinity establishes the limit.

The same result has a generating-function derivation. Put B(x,y)=sum_{i log p>j log q} binom(i+j,i)x^i y^j/(i+j). The generating function for admissible path counts is F(x,y)=exp(sum_{i log p≤j log q, i+j>0} binom(i+j,i)x^i y^j/(i+j))=G(x,y)/(1-x-y), where G=exp(-B). This is the bivariate form of the Sparre-Andersen/Spitzer factorization. Because the forbidden coefficients decay exponentially at x=y=1/2, G is analytic in a neighborhood of that point. Expanding the coefficient ratio binom(2d-i-j,d-i)/binom(2d,d) gives 2^-(i+j)[1+((i+j)-(i-j)^2)/(4d)+O(d^-2)]. Thus the explicit refinement is A_d/binom(2d,d)=c_pq+a_pq/d+O(d^-2), with a_pq={(E-J^2)G}(1/2,1/2)/4, E=x∂x+y∂y and J=x∂x-y∂y. Equivalently a_pq=c_pq{J^2B-EB-(JB)^2}(1/2,1/2)/4. The reported correction coefficients are computed from this formula, not fitted to the exact-count tables. A separate exponential-series recurrence checks 1024 integer coefficients against the path dynamic program.

| Prime pair | Limit c | Derived 1/d coefficient | Exact ratio, d=2048 | Corrected absolute error |
| --- | --- | --- | --- | --- |
| 2→3 | 0.262153991332 | 0.221665661945 | 0.262262222265 | 4.253e-09 |
| 2→5 | 0.392482234023 | 0.163936679303 | 0.392562288183 | 6.954e-09 |
| 3→5 | 0.221869256783 | 0.209988615888 | 0.221971771906 | 1.838e-08 |
| 5→7 | 0.132803456578 | 0.308501411473 | 0.132954090587 | 1.446e-09 |


| d | Exact (2,3) ratio | Prediction c+a/d | Limit-only error | Corrected error |
| --- | --- | --- | --- | --- |
| 32 | 0.269044875922 | 0.269081043267 | 6.891e-03 | 3.617e-05 |
| 128 | 0.263885092453 | 0.263885754316 | 1.731e-03 | 6.619e-07 |
| 512 | 0.262586868891 | 0.262586932078 | 4.329e-04 | 6.319e-08 |
| 2048 | 0.262262222265 | 0.262262226518 | 1.082e-04 | 4.253e-09 |
| 4096 | 0.262208107850 | 0.262208108925 | 5.412e-05 | 1.075e-09 |


For a Pauli walk the first nonzero p^d→q^d coefficient appears at order 2d. Its magnitude is A_d t^(2d)/(2d)!, and its leading transfer probability is A_d^2 t^(4d)/((2d)!)^2. The height barrier therefore suppresses this coefficient by c_pq asymptotically and its leading probability by c_pq^2. This comparison concerns the first Taylor coefficient as d grows; it does not interchange the small-time and large-d limits or assert a finite-time probability ratio.

The held-out cutoff is 3^4096, an integer with 1955 decimal digits. This calculation enumerates a structured path rectangle, not every integer below that cutoff. The dynamic program avoids constructing an astronomical ambient matrix by operating on valuation coordinates.

## Addition and shifts destroy the unadapted grading

The prime set here is {2,3,5,7}. Adding n↔n+1 edges changes the shortest return order. Cubes have the shortcut 1→7→8; fourth powers have 16→80→81. Consequently the d-step theorem depends on the chosen transition algebra. It is not a universal fact about all arithmetic moves.

| Power d | Population at N=16384 | Multiplicative onset | Onset with addition | A shortest witness |
| --- | --- | --- | --- | --- |
| 2 | 128 | 2 | 2 | 1024→4096 |
| 3 | 25 | 3 | 2 | 1→8 |
| 4 | 11 | 4 | 2 | 16→81 |
| 5 | 6 | 5 | 4 | 32→1 |
| 6 | 5 | 6 | 4 | 64→1 |
| 7 | 4 | 7 | 5 | 128→1 |
| 8 | 3 | 8 | 6 | 256→1 |


For shifted populations n+k=a^d, the original multiplication graph need not preserve valuation charges. At N=4096, shifted squares with k=1 already have the one-step edge 3→15. Some shifted populations are disconnected under the restricted prime set. Empty onset entries mean no connected pair in that finite graph, not global finiteness or impossibility. An adapted transition n→p^d(n+k)-k preserves the shifted-power population wherever its image remains in the domain. This is a change of arithmetic correspondence, rather than recovery of the original graph symmetry.

## Exact boundary law and spectral moment recovery

For pure prime transitions, every d-th power has no adjacent d-th power when d≥2. The weighted solution-to-nonsolution boundary is exactly E_d(N)=sum_p w_p^2[floor((N/p)^(1/d))+floor(floor(N^(1/d))/p)]. It differs from N^(1/d)sum_p w_p^2(p^-1/d+p^-1) by less than 2sum_p w_p^2. The finite checks span six cutoffs, seven exponents, and six primes: 252 exact boundary cases.

The commutator identity ||[C,Q]||_HS^2=2||QCP||_HS^2 supplies the same boundary quantity for general conditions. Writing D_m for the mass-dependent Pauli matrix, tr(D_m^2)-tr(D_0^2)=2m^2 tr Q. Further, tr(D_m^4)-tr(D_0^4)=4m^2 tr((C^2+H^2)Q)+2m^4 tr Q+2m^2||[C,Q]||_HS^2. The moments therefore recover the finite solution count, and, given the displayed incident-energy term, recover its boundary. These are representation identities, not a free counting algorithm: constructing Q already requires the condition to be evaluated. Twelve eigenvalue-based recovery cases have maximum count error 1.705e-13 and maximum boundary error 4.547e-12.

## Effective transport with a large nonsolution penalty

A separate scalar model A=H+gC+mQ isolates the Schur-complement mechanism. This is not the Pauli Hamiltonian. On the prime-power chain p^a, retain sites a divisible by d. At E=d log p the first neighboring retained-site coupling is (-1)^(d-1)g^d/product_{j=1..d-1}(m+j log p-E), followed by higher-order corrections. Its asymptotic scale is g^d/m^(d-1). The program evaluates the exact finite Schur complement at the stated E and compares it with this leading expression; that is not an approximate eigenvalue claim. There are 196 parameter cases over d=2..8, four primes, and seven penalties.

| d | Exact coupling, p=2,m=1280,g=0.5 | Relative leading-form error | |coupling|m^(d-1)/g^d |
| --- | --- | --- | --- |
| 2 | -1.954183e-04 | 0.000e+00 | 1.000541815 |
| 3 | 7.641806e-08 | 1.528e-07 | 1.001626772 |
| 4 | -2.989938e-11 | 3.058e-07 | 1.003256780 |
| 5 | 1.170480e-14 | 4.590e-07 | 1.005434791 |
| 6 | -4.584602e-18 | 6.123e-07 | 1.008164658 |
| 7 | 1.796698e-21 | 7.658e-07 | 1.011451146 |
| 8 | -7.045059e-25 | 9.195e-07 | 1.015299947 |


## Negative spectral finding

Smallest Pauli gaps mostly measure the height-zero state n=1 and its immediate virtual neighborhood. High exponents become almost indistinguishable by this statistic even after anchoring the controls at n=1. Each control mean below averages eight masks. This is descriptive evidence, not a trained classifier or significance test.

| d | Perfect-power gap | Anchored-control mean | Height-stratified mean |
| --- | --- | --- | --- |
| 2 | 0.238146075 | 0.265613609 | 0.420479078 |
| 3 | 0.239070090 | 0.238881451 | 0.371561489 |
| 4 | 0.239069742 | 0.238961524 | 0.238797667 |
| 5 | 0.239069744 | 0.239070002 | 0.239069898 |
| 6 | 0.239069744 | 0.239069743 | 0.239069744 |


The delay order and exact height-barrier path coefficients carry substantially clearer arithmetic information than the raw gap. The leading t^2 leakage from n=1 is also exponent-blind for d≥2 in the pure prime graph: all directly adjacent primes are nonsolutions. This rules out another tempting superficial diagnostic.

## Next bounded push

The next implementation should compile the valuation-coordinate operator directly, expose exact delayed-return coefficients and height-barrier path counts, and preserve them as queryable populations. It should support shifted arithmetic correspondences explicitly instead of treating raw multiplication as coordinate-independent. A finite proof target is the weighted d-step compression theorem and the geodesic recursion, followed by source-bound integer replay packets. A separate analytic target is an interval-certified survival constant and a computable remainder for the 1/d expansion. Lean verification, polynomial-curve transport, and a general decision algorithm are not completed here.

Relevant established sources are Bost–Connes arithmetic statistical mechanics (https://alainconnes.org/wp-content/uploads/bookwebfinal-2.pdf), Dusson–Sigal–Stamm on the Feshbach–Schur map (https://arxiv.org/abs/2105.02058), Kempton–Tolbert on isospectral reductions and quantum walks (https://numdam.org/articles/10.5802/alco.333/), and Janssen–van Leeuwaarden on Spitzer's identity (https://arxiv.org/abs/1710.09670). These establish the neighboring machinery; the exact arithmetic specialization, computations, and proof arguments above are retained in this package.
