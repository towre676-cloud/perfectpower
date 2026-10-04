# Recovered ideas rebuilt as exact arithmetic machinery

This release changes the purpose of the excavation. The old conversations are a source of design ideas; reproducing their exact experiments is no longer the admission test. The result is an integrated integer-equation engine and an exact closest-integer optimizer. They combine useful pieces of the earlier geometry, operator, divisibility, quotient and phase work with classical arithmetic algorithms. They come with replayable certificates and measured applications to the repository's actual data. There is no claim of priority for the mathematics or of superiority to industrial solvers.

## What was reviewed, and what changed

The audit covers the 22 existing top-level monographs, their recovered families and the compiler's established routes, plus retrieved older work from October 2024 through September 2026. `receipts/enhanced_machinery/gem_inventory.json` records the documents, hashes, decisions and additional historical inspirations. This is an inventory of accessible material, not a claim that every historical conversation was available.

The main adaptations are these:

| Earlier idea | Revised mechanism | Practical consequence |
|---|---|---|
| Polynomial power coordinates, orbit quotients and invariant presentations | Canonical rational centering, power compression, checked coefficient identity | Expanded equations reduce to smaller equations even after enormous affine shifts |
| Integral lifting and Smith coordinates | Saturated integer fibres and both divisibility tests after polynomial transport | No rational point or incorrect congruence class becomes a spurious integer answer |
| Phase-sensitive local arithmetic and tube filters | Complete power-residue tables, joined over the full least-common-multiple period | Safe global obstructions and fewer finite candidate checks, including at negative coordinates |
| Native quartic and Runge bounds | Reusable finite leaf certificates, including an absolute-value extension of the rational root gap | Completeness is attached to a proved bound rather than an arbitrary search window |
| Weighted task sections and constraint projectors | Exact closest-point enumeration in the integer fibre | The optimizer returns whole-number solutions, including every equally good answer |
| Divisor/GCD feature kernels | The actual stored seven-channel Gram matrix becomes the optimizer's metric | A recovered arithmetic operator is used in a complete integer optimization problem |
| Formation/Wilson shared carriers and delayed quotients | Canonical leaf cache, residue-table cache and reusable Smith/metric decompositions | Related queries share verified work instead of repeating discovery |
| Early spectral and compression proposals | Explicit identities, error boundaries and work budgets | Useful design principles survive without adopting unsupported spectral or tower-collapse claims |

Existing divisor routes, Pell and radical generators, descent, recurrence reconstruction, finite Fourier operators, invariant calculations and analytic geometry remain complementary tools. In particular, exact proper powers retain the compiler's existing theorem-backed radical/Pell routes when those routes offer the richer counting interface. The new finite route follows the cheaper divisor and quartic recognizers. Numerical periods and meshes remain numerical evidence; they are not used to prove integer completeness.

## Complete equations through small coordinates

The direct engine addresses all integer pairs satisfying

\[
y^d=F(x),\qquad F\in\mathbb Z[x],\quad 2\le d\le64.
\]

It supports degree at most 64 and coefficients of at most 16,384 bits. These are implementation budgets, not mathematical boundaries. For a degree-N input, the canonical center is

\[
h=-\frac{f_{N-1}}{Nf_N},\qquad a=\operatorname{den}(h)>0,
\quad b=-\operatorname{num}(h),\quad t=ax+b.
\]

The engine expands `F((t-b)/a)` exactly. If every nonconstant exponent is divisible by q, this centered polynomial is `G(t^q)`. It tries divisors of their gcd in descending order. For s equal to the least common multiple of the coefficients' denominators, the checked integral identity is

\[
(sy)^d=H((ax+b)^q),\qquad H=s^dG\in\mathbb Z[u].
\]

The transformation is useful even when the center is rational. No approximate roots or coefficient clustering are involved. There is also an identity-coordinate fallback. It does not discover arbitrary polynomial decompositions or arbitrary birational maps.

A complete leaf list `(u,v)` must satisfy three image conditions before returning to the original equation: `v` is divisible by s; `u=t^q` has an integer root t, with both signs for even q; and `t-b` is divisible by a. The lifted pair is `((t-b)/a,v/s)`. Every pair is substituted into the original polynomial again. The finite engine's domain includes negative x, zero and both y signs when appropriate. Its main-compiler adapter subsequently preserves the compiler's positive-index domain and existing witness restrictions.

Unsupported families return `UNRESOLVED` with no finite point list. Exact polynomial powers and constant powers return explicit generators. Exhausted candidate budgets never return a partial list described as complete; strict mode raises the corresponding exception.

## Complete residue covers

For a modulus m, the local table retains precisely the residues r for which `F(r)` is a d-th power modulo m. The defaults are 16, 9, 5 and 7. These deliberately include prime powers. Joining tables retains all compatible phases over their least common multiple; the implementation also supports noncoprime moduli without pretending they are independent CRT factors.

Every integer solution maps into the retained set. An empty set therefore proves that no integer pair exists anywhere. A nonempty set proves only a necessary condition. For example, `y²=2x⁴+3` has an empty table modulo 16 and needs no height bound.

For a certified interval `[-B,B]`, the engine counts surviving arithmetic-progression entries before scanning. It rejects work beyond the budget before exposing a partial result. The surviving entries are merged and tested using integer root extraction. Covers are rebuilt during certificate replay. Cached tables are keyed by the actual reduced coefficients, exponent and modulus; canonical leaf caches are bounded and public leaf receipts are copied defensively.

## Why the finite leaf covers both signs of x

Integral near-square quartics reuse the existing `LinearPerturbation.complete` bound. Rational square-leading quartics reuse the normalization and bound associated with `SquareLeadingQuartic.complete`. The fallback uses the repository's rational truncation certificate

\[
F=Q^d+R,\qquad Q=P/D,\quad D>0,\qquad
\deg R<(d-1)\deg Q,
\]

with nonzero R. The checker verifies the coefficient identity and exact coefficient inequalities at the cutoff B. Their degree differences make those inequalities persist for every `|x|≥B`.

Write q=deg Q, r=deg R and b for Q's leading coefficient. The inequalities ensure

\[
|Q(x)|\ge |b||x|^q/2,\quad R(x)\ne0,\quad
|R(x)|\le |Q(x)|^d/2,\quad
|R(x)|<|Q(x)|^{d-1}/(2D).
\]

All estimates use `|x|`, so the proof also applies to negative x. For odd d, an alleged integer y with `y^d=F(x)` has the same sign as Q. For even d, choose the signed integer root z with the same sign as Q. In either case, factoring the difference of powers in their common-sign magnitudes gives

\[
|z-Q(x)|\le |R(x)|/|Q(x)|^{d-1}<1/(2D).
\]

But `Dz-P(x)` is an integer. The strict bound forces it to be zero, forcing R(x)=0, a contradiction. Thus all pairs lie in `[-B+1,B-1]`. This absolute-value extension is a written derivation checked through exact Python inequalities. It is not a newly compiled Lean theorem.

## The nearest integer solution, with every tie

The second engine solves

\[
\min_{x\in\mathbb Z^n,\ Ax=b}(x-t)^TM(x-t),
\]

for integral A and b, rational target t, and rational symmetric positive-definite M. Smith coordinates either produce an exact divisibility/image obstruction or describe the whole fibre as `x=x₀+Kz`, `z∈Z^r`, with a saturated kernel. Rational projection followed by coordinate rounding would not preserve this fibre.

An optional weighted exact LLL reduction changes the kernel basis by recorded integer column additions and swaps. Those unimodular operations preserve every integer point. Correctness does not depend on the resulting basis satisfying a particular quality estimate. Discovery and certificate replay both enforce explicit budgets.

Let `G=KᵀMK`, `h=KᵀM(x₀-t)` and `c=-G⁻¹h`. The objective becomes

\[
E(z)=E_{\rm cont}+(z-c)^TG(z-c),\qquad
E_{\rm cont}=E(0)+h^Tc.
\]

An exact LDL decomposition writes `G=UᵀDU`, with U upper triangular and unit diagonal. A rounded descending seed supplies a feasible incumbent. Enumeration then proceeds from the last coordinate upward, retaining only branches inside the incumbent ellipsoid. For local center `p/q` and remaining squared allowance w, the precise integer range is obtained from

\[
s=\left\lfloor\sqrt{\lfloor wq^2\rfloor}\right\rfloor,
\qquad \left\lceil\frac{p-s}{q}\right\rceil
\le z_i\le\left\lfloor\frac{p+s}{q}\right\rfloor.
\]

The allowance includes division by the corresponding positive LDL diagonal. Only integer arithmetic and fractions are used. Positive definiteness makes this a finite search. Pruning uses strict worsening, so all ties survive. The result contains the integer minimizers, exact minimum energy and exact continuous lower bound. A failed node budget raises an exception and returns no asserted optimum.

This is classical lattice reduction and ellipsoid enumeration adapted to the recovered exact interfaces. It has exponential worst-case cost. The default limits are 64 rows/columns, 12 kernel parameters and 100,000 enumeration nodes. The recorded genus-7 cell has 14 kernel parameters and is explicitly outside the default run. Background: [Micciancio's academic account of lattice enumeration](https://cseweb.ucsd.edu/~daniele/LatticeLinks/Enum.html).

## Discovery and replay are separate

`verify_result` checks supplied coordinate identities, complete local tables, leaf bounds, the entire surviving finite search and integer image restrictions. It does not repeat normal-form discovery or compiler dispatch. `verify_optimum` checks the Smith certificate and unimodular basis transcript, then repeats the exact finite ellipsoid search; it does not discover Smith or LLL coordinates again. Thus replay checks completeness, rather than merely substituting the listed answers. It still trusts the exact Python implementation and is not a separately verified execution kernel.

All new receipts state `execution_verified: false`. The release adds no Lean source and reports zero new Lean compilations. Existing quartic theorem packets are inherited inputs; their coefficients, literal lists and saved `COMPLETE_KERNEL_CHECK` ledger are checked before using them as corpus references.

## Results on actual stored work

The runner starts with all 3,080 stored complete quartics. It solves each square-coordinate and cube-coordinate pullback, then an expanded affine disguise of each. Disguises use slopes 2 through 5 and shifts near `10³⁰`. This produces 12,320 complete equations, all independently replayed and matched to the original source lists through exact image tests.

Plain pullbacks contain 5,255 point occurrences and affine variants 1,362. These are counts across labelled equations, not globally distinct pairs. Across queries, 438,934 candidates survive from 5,098,757 certified leaf-interval positions, about 91.39% fewer root tests. Both totals include repeated canonical leaves. This ratio is not an end-to-end speedup measurement. The current-host run takes 11.97 seconds including certificate replay, with 2,013 leaf-cache hits and 3,333 misses; unsupported attempts count as misses, and globally obstructed queries need no leaf cache. This is a stored mathematical corpus and constructed variants, not an independent industrial benchmark.

Three constructed stress examples have expanded degrees 12, 40 and 15, coefficient sizes 1,208, 4,099 and 1,510 bits, and answers at `x=10³⁰`. Their recovered leaves need two, two and four candidate checks. The degree-15 example retains its negative cube witness. All three also pass through the existing positive-index compiler.

The nearest-integer engine is applied to the actual seven-channel divisor-feature Gram matrix from the previous recovery, representing 69,856,164 ordered pairs. With the stored channel counts as A and the stated rational target, it returns the unique solution `(1,0,0,0,0,0,0)` after 57 basis operations and six enumeration nodes. This optimizes a specified integer combination of actual features; it does not predict unseen perfect powers. Forty-one large-target queries reuse one Smith/metric decomposition. The equation `x₁+x₂=1` at target zero returns both closest vectors `(0,1)` and `(1,0)`, with energy 1 and continuous lower bound 1/2. Stored cell models of genera 0 through 4 also receive certified integer weighted-coclosed optimizations.

The full Python suite passes 608 tests, with four skipped dependency tests. Twenty-two new tests include independent exhaustive-box checks, negative coordinates, rational centers, lost divisibility conditions, all ties, budget failures, adversarial receipt mutations, JSON replay, cache isolation and both command-line interfaces. `validation.json` records source hashes and a fresh-copy, standard-library-only replay of the six deterministic runner receipts.

## Reproduce and use

From the repository root:

```sh
python python/enhance_machinery.py
PYTHONPATH=python python -m unittest discover -s python/tests
PYTHONPATH=python python -m perfectpower exact-solve --coeff '[1,1,0,0,1]' --d 2 --verify
PYTHONPATH=python python -m perfectpower nearest-lift --matrix '[[1,1]]' --rhs '[1]' --target '[0,0]' --verify
```

Use `--benchmark` on the runner to refresh the separately recorded timing. Fractions in CLI targets or metrics are supplied as strings, such as `"1/3"`; floating-point inputs are rejected. The primary modules are `arithmetic_engine.py`, `residue_cover.py` and `closest_integer.py`. The deterministic receipts preserve actual source provenance and their declared domains.

The most useful next expansion would add more effective finite leaves and then formally prove the new transport/replay interfaces. The current redesign already turns previously separate recovered ideas into executable compositions. Its scope grows through checked routes and honest budgets, rather than through unsupported claims that every integer equation is now decidable.
