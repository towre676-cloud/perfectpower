# Universal divisibility and complete repeated-factor arithmetic

## The mathematical advance

The repository can now replace an all-prime obstruction search by the gcd of a short list of exact polynomial values. For an integer polynomial f of degree d, define D as the nonnegative gcd of f(0), ..., f(d). Then, for every positive integer q, q divides D if and only if q divides f(x) for every signed integer x. The statement also includes q=0 with the usual divisibility convention. The zero polynomial has D=0; a constant c has D=abs(c). No assumption of separability, nonzero derivative, irreducibility or primitive coefficient content is needed.

This closes the repeated-factor limitation of the preceding local power-free release. That release obtains a finite exceptional-prime criterion from a checked derivative Bezout identity and retains useful root counts and root-lifting information. The new route answers the narrower universal-divisibility question directly, without constructing a derivative certificate or a residue set. For every exponent k, local admissibility of f is equivalent to k-freeness of D. Here local admissibility means that no prime k-th power divides every value; it does not mean that a globally k-free value exists.

A second advance turns a common source of global failure into complete finite arithmetic. If f=g^k h with g nonconstant and integer coefficients, a k-free value of f forces g(x)=1 or g(x)=-1. Complete integer roots of those two fibres give a finite candidate set, and testing f at the candidates gives the exact global solution set. Generic Lean theorems establish the reduction, and emitted fixtures prove literal all-integer solution equivalence. This supplies global answers for a substantial repeated-factor class, without needing a squarefree-density theorem.

## Why degree plus one values suffice

Let Delta f(X)=f(X+1)-f(X). Its degree is at most one less than the degree of a nonconstant f. If q divides f(0), ..., f(d), it divides Delta f(0), ..., Delta f(d-1). Induction on the degree proves that q divides Delta f at every nonnegative integer. Starting from f(0), induction along f(n+1)=Delta f(n)+f(n) proves divisibility of every nonnegative value of f.

For positive q, polynomial evaluation respects congruence modulo q. Every signed integer is congruent to a nonnegative canonical residue, so divisibility transfers to negative inputs too. For q=0, the sample hypothesis makes every nonnegative value zero. The polynomial root bound then proves f=0, which gives the signed conclusion. Constant and zero cases are handled inside the same theorem, not supplied as external assumptions.

The recursive gcd of an integer list has an elementary universal property: q divides it if and only if q divides each listed integer. Combining that property with the finite-window theorem proves the characterization of D. Windows longer than d+1 give the same gcd. Translating the polynomial by any integer leaves D unchanged. These are reusable Lean results, rather than properties checked only on the release examples.

Degree plus one is genuinely necessary in the worst case. The polynomial X(X-1)(X-2) vanishes at 0, 1 and 2, so a three-value gcd is zero and says nothing useful. Its fourth value is 6; its true fixed divisor is 6. More generally the degree-d falling factorial vanishes at its first d sample points and has fixed divisor d!.

Coefficient content is a different quantity. X(X-1) has coefficient gcd one but fixed divisor two. The quotient X(X-1)/2 is integer-valued without having integer coefficients. That distinction is useful for the repository's Gamma, factorial and binomial interfaces: divisibility belongs to the values on an integer domain, not merely to the coefficient list.

## Local admissibility with no residue enumeration

For a modulus q>0, all q canonical residues are roots if and only if q divides every signed evaluation. The existing modular root count rho therefore equals q exactly when q divides D. Since rho cannot exceed q, the strict inequality rho(f,p^k)<p^k is equivalent to p^k not dividing D. Quantifying over all primes proves the fixed-divisor criterion for local admissibility.

The producer factors D to expose its exact valuations. Every prime whose valuation is at least k is a universal obstruction. For a factor prime whose valuation is below k, the packet gives a concrete sample input where p^k fails to divide the value. Primes outside the factor support cannot be universal obstructions. D=1 is locally admissible for every positive k, while D=0 is obstructed for every k. At k=1, local admissibility requires D=1; it does not require every individual value to be a unit.

This route removes the old prime-power modulus budget from the admissibility decision. A constant equal to 10007^2 is rejected at k=2 without enumerating 100140049 residues. The degree-16 falling factorial is diagnosed from 17 samples. Its fixed divisor is 16!=20922789888000. The scaling receipt extends the same calculation through degree 128, using 129 samples rather than a residue space tied to 128!. These are structural operation-count comparisons, not measured speedup claims against an industrial solver.

Factorization still has a work budget. An exact fixed divisor can be returned even when its prime decomposition is too costly; an admissibility request raises WorkLimit on factorization exhaustion. It never labels an unfinished factorization as an admissible result. The earlier root and wheel route remains valuable when the caller needs the actual residue population rather than just the presence of a universal obstruction.

## Arithmetic progressions and value normalization

For an original polynomial f and integers a,b, the progression interface forms the exact pullback F(n)=f(a+b*n). It computes the fixed divisor of F. Emitted Lean source checks that polynomial composition identity and proves, for every natural modulus q, that q divides the returned D if and only if q divides f(a+b*n) for every signed n. The parameter n ranges over all integers, including when b is negative. With b=0 the interface becomes the exact single-value problem.

For f=X^2+1, the unrestricted fixed divisor is one. On odd inputs x=1+2n it becomes two: every odd square plus one is even, while n=0 gives the value two. The odd progression is consequently locally obstructed at k=1 but locally admissible at k=2. A progression must be analyzed in its own domain; using the unrestricted coefficient content or fixed divisor can miss the obstruction introduced by the domain.

The Python packet also computes all forward differences at zero. Newton's formula expresses F(n) as the sum of Delta^j F(0) times binomial(n,j), including negative n through generalized integral binomial coefficients. The gcd of those coefficients equals the sample-value gcd. Dividing the differences by a nonzero D exposes a primitive integer-valued quotient F/D. The packet records an explicit signed integer combination of the sample values that equals D. Independent tests check these identities. The generic Newton/binomial execution and Python producer are not themselves formally verified; the fixed-divisor theorem and the retained emitted source are kernel-checked separately.

## The global repeated-factor reduction

Suppose a prime p divides g(x). Then p^k divides g(x)^k h(x), regardless of the cofactor. A k-free value therefore makes g(x) an integer unit, hence either one or minus one. This argument includes zero: a zero factor cannot produce a k-free value. It handles negative values without changing the prime-divisibility definition.

The Python producer uses exact squarefree decomposition over the rationals, chooses a nonconstant factor of multiplicity at least k, converts it to a primitive integer polynomial, and verifies the integral cofactor in f=g^k h. Complete integer-root machinery finds the two unit fibres. It then factors the original values at the candidates, retains the k-free values, and returns a complete finite set. Native emission independently checks the polynomial factorization, factor-coordinate identity, native unit-fibre sets and each retained or rejected candidate. The final theorem is PowerFree k (f.eval x) if and only if x belongs to the literal returned solution set, for every signed integer x.

The distinction between local and global answers is concrete. The polynomial (X^2+2)^2 has fixed divisor one and passes all local squarefree tests, but has no squarefree values: its inner factor is at least two at every integer. The polynomial (X^2+1)^2 has exactly one squarefree input, x=0. X^2 and -X^2 each have inputs {-1,1}. The polynomial X^2(X+1) retains only x=1: x=-1 is a unit-fibre candidate but the original value is zero. The shifted cube (X-2)^3 has exactly the cube-free inputs {1,3}.

This is global finiteness for the specified repeated-factor class. It does not solve separable polynomial squarefree density, arbitrary Diophantine equations or all repeated-factor phenomena at a fixed k. When every multiplicity is below k, this reduction has no nonconstant k-fold factor and rejects the request explicitly. Within its supported class, the finite solution theorem establishes density zero as an immediate mathematical consequence; no asymptotic experiment is substituted for completeness.

## Public interface and replay

The module perfectpower.fixed_divisor exposes fixed_divisor, admissibility, native_certificate, repeated_power_free and native_repeated_power_free. Integer coefficients are supplied in ascending order. The fixed-divisor and admissibility interfaces accept start and step. The repeated-factor interface currently uses the original unrestricted integer coordinate; progression users can pass the returned pullback coefficients explicitly.

```python
from perfectpower.fixed_divisor import admissibility, repeated_power_free
local = admissibility([4,0,4,0,1], exponent=2)
assert local['locally_admissible']
global_hits = repeated_power_free([4,0,4,0,1], exponent=2)
assert global_hits['solutions'] == []
odd = admissibility([1,0,1], start=1, step=2, exponent=2)
assert odd['fixed_divisor'] == 2
```

The JSON query operations are fixed_divisor, fixed_divisor_admissibility, native_fixed_divisor_certificate, repeated_power_free and native_repeated_power_free. Producer flags remain kernel_checked=false until the generated source is compiled. The release summary records the exact combined source hash and successful audits of the retained fixtures. It does not claim that future API output has already been checked.

The computational interface supports degree at most 128, at most 129 coefficients, coefficient height at most 2048 bits and affine parameters at most 512 bits. Sample values have a 131072-bit cap. Admissibility exponents range from 1 to 1024; repeated-factor exponents from 2 to 128. Factorization work is capped at one million trial steps and inherits the existing 4096-bit input cap. Native source emission caps degree at 32; native fixed-divisor coefficients have a 4096-bit cap. Repeated native unit-fibre checking has an explicit signed-divisor budget, defaulting to square-root trial bound 4096. These are execution budgets, not hypotheses of the generic Lean theorems.

Replay the whole focused release with make fixed-divisor-check in the pinned Lean 4.20 environment. The checker regenerates packets, compiles the needed modules and audits the generic and literal declarations. The corpus contains 15 local packets and eight complete global repeated-factor packets. Independent evidence covers 180 polynomials, 2700 complete prime-power residue comparisons, 1260 signed Newton reconstructions and 2408 repeated-factor value comparisons. Twenty-four focused tests check domain, sign, primitive content, zero, constant, budget and service behavior.

## What this enables next

The fixed-divisor result is a reusable domain-aware arithmetic preprocessing step. It can reject universally obstructed branches before the repository launches a large wheel, an integer search or an effective-bound calculation. The integer-valued normalization gives the factorial and Gamma machinery a concrete arithmetic output. The repeated-factor reduction can turn locally admissible but globally sparse expressions into exact finite populations that the repository can count, inspect or join with other constraints.

The remaining high-value arithmetic front is global k-free behavior for separable polynomials, including the analytic hypotheses required for density claims. Formal refinement of the Newton producer, factorization transcript, generic JSON interpreter and complete compiler remains separate. The earlier root-lifting and wheel assembly obligations also remain. Efficient general Sturm checking, effective Baker/Matveev bounds, number-ring unit equations, rigorous analytic periods and smooth geometric comparisons are independent repository fronts. This release changes the local and repeated-factor arithmetic obligations; it does not claim to settle those larger problems.
