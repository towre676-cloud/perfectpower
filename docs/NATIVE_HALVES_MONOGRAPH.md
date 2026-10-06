# Complete native elliptic halving fibres

## The completed interface

This continuation connects the rational halving producer to Mathlib's actual rational elliptic point group. The preceding bridge already proved complete two-torsion on the completed-square model. This edition checks a concrete rational anchor's doubling and uses that complete kernel to prove the entire nonempty fibre. A second route proves that a root-free halving quartic excludes every actual half of an affine target. The third route handles infinity directly through the complete two-torsion list. None of these native completeness statements assumes a height bound, finite search completeness, a rank computation or a classification of rational torsion.

The public operation is `native_halves_certificate`. Registered elliptic objects expose `native_halves`. An optional anchor avoids halving discovery: the producer validates the coordinates, proposes the point's double, and emits a separate Lean proof of that doubling equality. Incorrect anchors are rejected before a certificate is returned. Without an anchor, the existing bounded producer searches for one. A proposed result remains execution-unverified until its emitted source is compiled.

The exact native statement is about the completed model y²=x³+Ax²+Bx+C. Generalized Weierstrass coefficients are retained in the packet, along with the completed target and anchor. The earlier square-completion identities explain that coordinate transformation, but a native additive equivalence from the original actual point group to the completed actual point group is still a separate task. The certificate also retains numeric producer output coordinates. Its proved list is the native group expression defined in Lean, rather than a proof that the JSON point list equals that expression. This boundary is explicit in the public scope string.

## A checked anchor makes a complete coset

Let P be a rational elliptic point and suppose a rational point H satisfies [2]H=P. For any rational point Q, subtracting H gives

```text
[2]Q = P  iff  [2](Q-H) = 0.
```

Thus the complete fibre is H+E(Q)[2]. The repository's existing group theorem `EllipticDivision.fibre_list_complete` proves this for every additive commutative group and every multiplication scalar, not merely for elliptic curves. The new producer supplies its concrete elliptic premises rather than leaving the anchor equality unchecked.

For a completed affine point (x,y) with y nonzero, Mathlib's actual addition computes the tangent slope (3x²+2Ax+B)/(2y), the doubled x-coordinate slope²-A-2x, and the corresponding reflected y-coordinate. The emitted `anchor_checked` theorem rewrites integer doubling as point addition, invokes Mathlib's nonvertical addition formula, reduces equality of affine points to equality of both coordinates, and checks those rational expressions using kernel-checked arithmetic. Smoothness and each supplied point's curve equation are proved first. Python's multiplication assertion is therefore not a premise of this theorem.

The complete two-torsion list comes from the earlier native rational-root bridge applied to x³+Ax²+Bx+C. It includes infinity and the branch point (r,0) for every checked rational root r. The new native `halves` list is the map T to H+T over that list. `actual_halves_complete` quantifies over every actual rational point Q and proves

```text
[2]Q = target  iff  Q belongs to halves.
```

On y²=x³-2, the anchor (3,5) doubles to (129/100,-383/1000). The cubic has no rational roots, so its rational two-torsion contains only infinity and the fibre has the single point (3,5). On y²=x³-25x, the anchor (25/4,75/8) produces a four-element fibre because the cubic roots are -5,0,5. A generalized fixture with a-invariants [1,-1/4,1,-1/2,-9/4] uses the original anchor (3,3), whose completed coordinates are (3,5). Its completed model is again y²=x³-2, while its original coordinates remain distinct evidence.

## Empty fibres from the actual doubling equation

The new reusable theorem `half_supplies_quartic_root` starts from an actual equality [2]Q=P for an affine target P=(u,v). Q cannot be infinity, since infinity doubles to infinity. Q cannot be a branch point either, since a branch point is two-torsion and also doubles to infinity. Therefore Q has affine coordinates (x,y) with y nonzero.

The proof rewrites actual point doubling using Mathlib's nonvertical formula. Equality with P supplies the doubled x-coordinate u. The existing `actual_doubling_x_iff` theorem then yields the exact quartic equation

```text
x⁴ - 4u x³ + (-2B-4uA)x² + (-8C-4uB)x
    + B²-4AC-4uC = 0.
```

This is a necessary condition for every actual half; it does not assume the half was discovered by a search. The second reusable theorem, `no_half_of_quartic_root_free`, takes a proof that this quartic has no rational roots and excludes every actual Q satisfying [2]Q=P. The target's own y-coordinate may be zero: only the hypothetical half must avoid the branch locus. This makes the obstruction valid for nondivisible branch targets as well as ordinary affine targets.

The empty-fibre emitter constructs this quartic from the original supplied target, emits a native complete rational-root theorem for it, proves that its polynomial evaluation equals the halving formula, and reduces the complete root set to empty. It applies the reusable actual-point obstruction and defines `halves` as the empty list. The same complete membership theorem is obtained as in the anchored route.

Two retained examples are the target (3,5) on y²=x³-2 and the branch target (0,0) on y²=x³-x. Their halving quartics have no rational roots. In the latter case the quartic is x⁴+2x²+1. The native proof excludes halves without turning the branch point itself into a division-by-zero input.

A quartic may have rational x-roots whose cubic values are nonsquares, or lifts whose double has the opposite y-sign. Python's existing producer can resolve those cases. This edition's native empty-fibre gate accepts only a root-free quartic and rejects the remaining lifting cases explicitly. It does not silently return a partial empty-fibre claim. Native nonsquare certificates and a complete signed-lift checker are the next arithmetic extensions.

## Reproduction and evidence

`make native-halves-receipts` regenerates six worked packets, six cold service requests and their combined Lean audit. The fixtures cover infinity, an empty ordinary affine fibre, an empty branch-target fibre, a one-element coset, a four-element coset and a generalized model. `make native-halves-lean` builds the actual point-group module, compiles every generated packet, prints the axioms of the complete membership theorems and their premises, and runs namespace lint. The audit includes the original-polynomial scaling proofs from the preceding root bridge; it does not trust a real-root Sturm count as a native premise.

The new five-test producer suite checks the coset sizes and original/completed coordinates, exact doubling of the numeric examples, root-free packets, infinity, discovery of an anchor, invalid anchors, invalid points, the native work budget, the direct JSONL operation and the registered elliptic method. The existing elliptic suite and the preceding native-bridge suite are also rerun. These are focused checks of the changed interfaces; the historical full-repository Lean build and the broad Python suite from the preceding push are not represented as freshly rerun here.

The source-bound validation receipt records hashes of the changed code, generated audit and documentation, along with the exact test totals and Lean audit declarations. The complete ZIP contains every tracked file at the published commit, including prior flavor and elliptic division receipts. Its file contents are checked against a Git archive of that commit, and the delivered PDF is checked against the committed monograph.

## The next useful interfaces

Original-model point transport would let the actual theorem quantify over points on the user's generalized Weierstrass model directly. Native literal-list equality would bind each returned coordinate pair to the proved coset list, closing another part of the producer-to-meaning interface. Nonsquare and sign-lift certificates would extend native empty fibres beyond the root-free quartic gate. Efficient generic Sturm proofs would replace the bounded signed-divisor route and support larger division polynomials. The parallel Python tripling and composite division engine can then consume those stronger native roots and point-law interfaces.

These advances are independent of full Mordell-Weil rank, saturation or a global integral-point bound. Halving a supplied rational point is already complete once its actual anchor and complete two-torsion are proved. Rank and saturation need additional global arguments. The wider repository still has geometric marking, analytic-period, smooth-metric, arithmetic-reduction, Gamma and solver refinement fronts; the preceding native-bridges monograph records their connection to this exact arithmetic layer.
