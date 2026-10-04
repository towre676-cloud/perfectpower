# Complete square-plus-constant lists through divisors

## Practical value

A search can find examples where a formula produces a square or cube. It cannot tell you that an answer does not occur much later. PerfectPower produces complete answers for supported families: a finite list, a rule generating answers, or an explicit account of what remains unproved. Its useful deliverable is a checkable reason that the answer covers every input. It does not solve every integer equation.

This push makes **y²=P(x)²+k**, for every nonconstant integer polynomial P and nonzero integer k, more practical. The Lean theorem covers both coordinates over all integers. Compiler constraints continue to restrict their input coordinate to positive integers.

## Factor pairs instead of coordinate rectangles

Put p=P(x). Every solution gives (y−p)(y+p)=k. Thus enumerate the ordered signed factor pairs (u,v) of k and recover p=(v−u)/2 and y=(v+u)/2. The formal implementation filters reconstructed values against y²=p²+k. This rejects mismatched parity without relying on informal assumptions about total integer division.

`FastDivisors.small` tests positive divisors up to ⌊√n⌋. Its union with complementary quotients contains every positive divisor of nonzero n: if a divisor and its complementary quotient both exceeded √n, their product would exceed n. Lean proves equality with Mathlib's divisor set and then equality of signed factor pairs with Mathlib's integer divisor antidiagonal. `values_complete` proves that the reconstructed value pairs are exactly the solutions of y²=p²+k. There is no factorization oracle, floating-point square root, height premise, or analytic assumption.

Kernel computation uses a structurally recursive, fuelled Newton iteration. `sqrtIter_eq` and `sqrt_eq` prove equality with Mathlib's square-root implementation; each strict decrease consumes one unit of fuel, so starting with fuel n suffices. It stops at the Newton fixed point. This avoids expensive kernel reduction of the source's well-founded recursion while preserving its exact result.

## Complete polynomial fibres

For each possible p, find every integer root of P(x)−p. If its constant coefficient a is nonzero, a+xQ(x)=0 implies x divides a. Test these signed divisors against the exact polynomial. When a=0, include x=0 and recurse on the tail. This preserves repeated roots as single set members and handles any number of initial zero coefficients.

`NativePolynomialRoots.complete` proves the procedure complete for every list ending in a nonzero coefficient. `fibre_complete` characterizes P(x)=p. Subtracting a constant preserves nonconstancy. Taking the union of these fibres with their corresponding y values gives `NativeDivisorSquare.complete`, which characterizes all integer solutions. `polynomial_complete` exports genuine `Polynomial ℤ` evaluation. `rectangle_eq` proves equality with the previous rectangle algorithm, whose independent height bounds remain available.

## Proof-producing use

```lean
import PerfectPower.Tactic.NativePolynomialPower

native_polynomial_square shifted for [1000000, 1], 1
#check shifted_complete
-- Exactly {(-1000000,-1), (-1000000,1)}.
```

Coefficients are ascending. The elaborator proposes data using the exact divisor and fibre computations. The emitted proof independently checks equality with the formal finite set using `decide +kernel`, then invokes completeness. Incorrect lists are rejected. Neither the metaprogram, Python, nor `native_decide` establishes the theorem. Constants, trailing zeros, and k=0 retain their diagnostic rejections; k=0 is an infinite family.

The generated theorem raises its local reduction recursion limit. Large examples also need a larger Lean worker stack; the audit uses `lake env lean -s 65536`. This changes available computation resources, not kernel inference rules. The million-shift example should be run with that stack setting.

The compiler recognizes expanded integral polynomial squares plus a constant by reconstructing coefficients from the top downward, requiring exact division and checking all nonconstant coefficients. When k≠0 and the work budget permits, it uses the divisor solver. Exhaustion falls back to existing routes and never labels a partial result complete. Python execution remains unverified. `divisor_square.emit_lean` produces a native command for an independently checkable instance.

For the million-shift example the old rectangle contains **6,000,021 coordinate pairs**, while the Python divisor solver performs **1,001 trial-divisor checks**. These are deterministic counts of different operations, not a wall-clock speedup or Lean reduction measurement. `data/divisor_reuse_receipt.json` records inputs, outputs, counts, and trust labels. Regenerate it with `PYTHONPATH=python python python/divisor_reuse_receipt.py`.

## Exact arithmetic reuse

Morphonic Kernel v1.74.0 supplies the reusable source. Archive and source hashes, adaptation mapping, and MIT license are under `reuse/morphonic`. Its finite-extension machinery provides the multiplication-matrix construction, exact norm and trace, inversion by polynomial Euclid, and Faddeev–LeVerrier characteristic polynomial. The adaptation uses PerfectPower's existing rational polynomial core.

The API says **quotient algebra**: reducible moduli and zero divisors are allowed, and nonunit inversion fails explicitly. No irreducibility proof is implied. Receipts mark execution and irreducibility certification false. Tests include known quadratic and cubic norms, multiplicative norms, additive traces, inverses, and Cayley–Hamilton across degrees two through six. This is exact proposal machinery for future norm certificates, not a completed number-ring solver.

## Quartic charts and finite exclusions

The reused quartic source studies z²=dM⁴+AM²e²+ce⁴. Its charts are e unit with t=M/e, and M unit with e nonunit, u=e/M in pℤₚ. Writing u=pw makes the second polynomial **d+Ap²w²+cp⁴w⁴**. The source's `initialScale=p` adjusted witness coordinates without substituting in the polynomial. The adaptation substitutes the coefficients themselves. This corrects chart/witness correspondence; no claim is made that the source's final verdict necessarily changes.

The integration certifies a narrower part: finite modular exclusions. `LocalQuarticObstruction.obstructed` checks residue triples with M or e nonzero. `no_primitive_point` transports an obstruction to integers; `no_point_of_not_dvd` states primitivity through divisibility. A surviving residue makes no assertion about a p-adic or integer point. The Python proposal API requires a prime and a budget and rejects false certificates before emitting Lean for independent checking.

The audit certifies that z²=2M⁴+M²e²+2e⁴ has no point primitive at 3. The zero triple remains a point, illustrating why primitivity is essential. A soluble residue case rejects a false obstruction.

## Verification and remaining scope

Run `bash scripts/check_divisor_reuse.sh` with pinned Lean 4.20.0 and Mathlib. It includes earlier near-square and finite-field audits, new polynomial divisor and quartic audits, and focused Python tests. The verification record reports the actual runs and source hashes. Axiom audits cover general theorems and generated examples; no `sorry`, axiom declaration, or `native_decide` is introduced.

The focused Python tests compare 150 randomized cases with independent scans within the prior proved bounds. Lean audits include million-sized shifts, both coefficient signs, repeated roots, and empty families. Repository-wide Python results are reported separately. Focused checking does not claim a rerun of the entire heavy Lean build, regeneration pipeline, optional Sage checks, or external solver integrations.

Square-root trial division remains costly for huge integers. General Baker bounds, broad Runge automation, complete number-ring solvers, and certified fast factorization remain separate work. Placeholder theorems concluding `True` and sampled floating derivative estimates were not imported as arithmetic proofs. Existing exact interval certificates retain their role.
