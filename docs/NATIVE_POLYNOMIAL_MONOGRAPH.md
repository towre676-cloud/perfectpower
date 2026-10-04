# Native effective bounds for square-plus-constant polynomial equations

This extension proves an unconditional, computable finite search for the equation y²=P(x)²+k, where P is any nonconstant integer polynomial and k is a nonzero integer. The degree and leading coefficient are unrestricted. It extends the earlier monic quadratic near-square solver to arbitrary degree, while retaining a deliberately precise mathematical scope: it does not decide arbitrary equations yᵈ=F(x), discharge general linear-forms-in-logarithms premises, or implement general Runge theory.

## The coefficient representation

The input is a list of integer coefficients in ascending order. Thus [−1,−1,1,1] denotes −1−x+x²+x³ and [0,0,0,2] denotes 2x³. A valid list ends in a nonzero coefficient and contains at least two coefficients. Rejecting trailing zeros makes the nonconstant condition transparent and decidable. Users can remove trailing zeros without changing the polynomial. Constants require separate treatment because their equation may hold at every integer x.

The executable evaluator is Horner evaluation: E([],x)=0 and E(a::as,x)=a+xE(as,x). The coefficient height is H([])=0 and H(a::as)=|a|+H(as). Both operations use exact integers. The formal polynomial interpretation uses C(a)+X times the recursively interpreted tail. `polynomial_eval` proves that this genuine `Polynomial ℤ` has exactly the executable evaluator's value. `polynomial_complete` exports the completeness result in standard polynomial evaluation notation, rather than leaving the coefficient representation as an informal convention.

## An effective bound without an analytic premise

For a valid coefficient list, Lean proves that |E(as,x)|≥1 whenever |x|≥H(as)+1. The proof is an induction on the coefficient list. A singleton evaluates to its nonzero coefficient, whose absolute value is at least one because it is an integer. For a longer list, the induction hypothesis gives |E(tail,x)|≥1. The triangle inequality applied to a+xE(tail,x) then yields

|x| ≤ |x| |E(tail,x)| ≤ |E(a::tail,x)|+|a|.

Since |x|≥|a|+H(tail)+1, the evaluated polynomial cannot vanish. This argument needs neither monicity nor positivity of the leading coefficient. It is an elementary integer coefficient bound; its purpose is to support executable enumeration, rather than to optimize a classical real-valued root bound.

For a nonconstant list, the same inequality proves that |E(as,x)|≤|k| implies |x|≤H(as)+|k|+1. If x exceeded that bound, it would also lie outside the tail's height, so the lower bound above would contradict |E(as,x)|≤|k|. The theorem `eval_bound` formalizes this implication with all hypotheses explicit.

The earlier `NativeNearSquare.square_bounds` supplies the second ingredient. Factoring y²−P(x)² gives (y−P(x))(y+P(x))=k. For nonzero k, each integer factor has absolute value at most |k|. Taking their sum and difference therefore proves |y|≤|k| and |P(x)|≤|k|. Combining the two results gives a rectangle containing every solution:

|x|≤H(as)+|k|+1, and |y|≤|k|.

`points` enumerates this rectangle and filters it using the original equation. `complete` proves that membership is equivalent to the equation for every integer x and y. No externally supplied height assertion occurs in this theorem. The bound is intentionally conservative. Large coefficients or large k can make kernel reduction expensive; a mathematically finite search is not automatically a practical search at every input size.

## Native proof-producing use

Import `PerfectPower.Tactic.NativePolynomialPower` and issue:

```lean
native_polynomial_square cubic_points for [0, 0, 0, 2], 1
#check cubic_points_complete
```

The command creates a concrete finite set and a theorem characterizing all solutions of y²=(2x³)²+1. Its complete set is {(0,−1),(0,1)}. The audit also transports this generated theorem to the expanded equation y²=4x⁶+1.

The command's elaborator evaluates closed input terms, runs an exact integer search, and proposes a point list. This metaprogram is not trusted to establish completeness. The emitted proof uses `decide +kernel` to check that the proposed set is the formally defined filtered rectangle, then applies the general completeness theorem. An incorrect list is rejected. The native evaluator contributes data, while the proof's finite computation is checked by the Lean kernel. Neither Python nor `native_decide` participates in this path.

The tactic `decide_polynomial_square coefficients, k => expected_points` provides the same check for a user-supplied finite set. It proves the coefficient validity, nonconstant condition, and nonzero k requirement before applying completeness. The command rejects constant lists, zero final coefficients, and k=0 with targeted diagnostics. When k=0, y=P(x) already gives infinitely many points, so a finite-list result would be false.

## Validation and remaining work

`audit/NativePolynomialPower.lean` generates six complete solution lists. These include the nonmonic sextic above, y²=x⁶+8, y²=x⁶−1, y²=9x¹⁴+7, a shifted cubic square-plus-one equation, and an empty nonmonic family. The degree-14 example has exactly (−1,±4) and (1,±4). Kernel reduction independently checks the explicit expected lists. Three diagnostic tests reject unsupported inputs, and a fourth test confirms that a false empty list cannot be certified. The audit prints the axioms of the coefficient bounds, both completeness theorems, all six generated results, and the expanded equation result. Each uses only propext, Classical.choice, and Quot.sound.

The retained check script runs the earlier native near-square and finite-field audits as well as the new modules and audit. Its log and source-hash receipt document focused checks under Lean 4.20.0 and the pinned Mathlib revision. This is not a claim that the entire heavy repository build has been rerun. Earlier results such as the k=22 Mordell closure and the weighted norm-107 theorem remain intact.

The open-front checkpoint continues to distinguish this supported family from the larger research agenda. General Baker bounds, arbitrary-polynomial perfect-power automation, complete number-ring solvers, auxiliary-prime orbit exclusion, and GPU/WASM deployment remain unfinished. Classical Chabauty requires rank strictly below genus; a genus assumption by itself cannot justify completeness. The finite-field Fermat classification already in the repository is a separate restricted family, not a general function-field solver. Future pushes can improve search efficiency, recognize expanded square-plus-constant inputs, and broaden the effective-bound families while preserving the same kernel-checked trust boundary.
