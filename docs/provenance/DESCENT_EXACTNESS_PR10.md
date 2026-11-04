# Lean Descent Wave Three — Report

**Headline result: targets T1 and T2 of the wave-two report are closed completely and unconditionally over ℚ.** The wave-two report left the reverse inclusions `ker δ ⊆ range φ` and `ker δ' ⊆ range ψ` as the solubility half of the two-isogeny descent, and this wave's brief asked for them to be proved modulo one clearly named hypothesis — solubility of the `d = 1` quartic cover — closing them fully only if that solubility fell to machinery already available. It did fall, and the reason is worth stating plainly: for these explicit connecting homomorphisms, triviality of the label is *itself* the solubility. If `δ(P′) = 1`, wave two's `isSquare_of_cls_eq_one` immediately produces a rational square root of the relevant coordinate, and the cover point is written down directly from `P′` — `(t, 1, y′/t)` when the `x`-coordinate is `t² ≠ 0`, and `(0, 1, s)` with `s² = B` at the exceptional point. There is no hidden arithmetic input and no remaining hypothesis in the final theorems. The reduction theorems requested by the brief are stated and proved as separate results (so the logical structure "cover-soluble ⟹ kernel inclusion" is explicit in the file), and the unconditional theorems are then obtained by discharging their solubility hypothesis with the proved lemma. Everything below is in the single new module `PerfectPower.DescentCover` (namespace `PerfectPower.DescentCover`), built on top of wave two's `PerfectPower.DescentDelta` in a copied build tree at `repo_copy/`; the cloned repository was not modified; this package is submitted on the branch `muse/lean-descent-exactness`.

## Defined

The homogeneous space is defined in multiplied-out form, so that no division by the label `d` occurs in the predicate. For `d ≠ 0` it is equivalent over ℚ to the classical cover `w² = d·u⁴ + A·u²v² + (B/d)·v⁴` of the model `E A B : y² = x(x² + A x + B)`:

```lean
def QuarticCover (A B d : ℚ) (u v w : ℚ) : Prop :=
  d * w ^ 2 = d ^ 2 * u ^ 4 + A * d * u ^ 2 * v ^ 2 + B * v ^ 4
```

## Proved

The two main theorems, with no hypotheses beyond the standing nonsingularity conditions `b ≠ 0` and `a² − 4b ≠ 0`, are:

```lean
theorem deltaPhi_ker_le_phiHom_range (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) :
    (deltaPhi a b hb hd).ker ≤ (phiHom a b hb hd).range

theorem deltaDual_ker_le_dualHom_range (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0) :
    (deltaDual a b hb).ker ≤ (dualHom a b hb hd).range
```

Combined with wave two's inclusions by antisymmetry, these give the exact kernel identifications `phiHom_range_eq_deltaPhi_ker : (phiHom a b hb hd).range = (deltaPhi a b hb hd).ker` and `dualHom_range_eq_deltaDual_ker : (dualHom a b hb hd).range = (deltaDual a b hb).ker`, which is the exactness at the middle term that the descent exact sequence needs. The wave-two report's target statements are also present verbatim in their integer-parameter form, as `deltaPhi_ker_le_phiHom_range_int` and `deltaDual_ker_le_dualHom_range_int` (with hypotheses `(hb : b ≠ 0)`, `(hd : a ^ 2 - 4 * b ≠ 0)` over ℤ and `(hdQ : (a : ℚ) ^ 2 - 4 * (b : ℚ) ≠ 0)`); the integer discriminant hypothesis is carried because the wave-two target shape includes it, although the ℚ theorem underneath does not need it — this is also the source of the only two linter warnings in the build log (unused variable `hd` in the two `_int` corollaries).

The supporting results are proved in the order the argument needs them. `quarticCover_one_iff` identifies the `d = 1` cover with the plain quartic `w ^ 2 = u ^ 4 + A * u ^ 2 * v ^ 2 + B * v ^ 4`, and `quarticCover_scale` shows a cover point `(u, v, w)` with `v ≠ 0` rescales to the normalised representative `(u / v, 1, w / v ^ 2)`, which is what justifies working throughout with `v = 1` points. The general-label bookkeeping lemma, valid for every `d`, is:

```lean
theorem point_of_quarticCover (A B d : ℚ) (hd : d ≠ 0) (hB : B ≠ 0)
    (hdisc : A ^ 2 - 4 * B ≠ 0) {u v w : ℚ} (hv : v ≠ 0)
    (hcov : QuarticCover A B d u v w) :
    ∃ hp : (E A B).Nonsingular (d * u ^ 2 / v ^ 2) (d * u * w / v ^ 3),
      delta A B hB (Point.some hp) = cls d
```

This is the converse direction of the shape the repository already has in `TwoDescentBridges.rational_point_cover_complete`: a rational point of `C_d` maps to the point `(d·u²/v², d·u·w/v³)` of `E A B`, and its `δ`-value is exactly the label class `cls d` — for `u ≠ 0` because the `x`-coordinate is `d·(u/v)²`, and for `u = 0` because the cover equation then reads `d·w² = B·v⁴`, so the exceptional value `cls B` equals `cls d`. The kernel-to-cover step is:

```lean
theorem exists_cover_of_delta_eq_one (A B : ℚ) (hB : B ≠ 0) {x' y' : ℚ}
    (hp : (E A B).Nonsingular x' y') (hδ : delta A B hB (Point.some hp) = 1) :
    ∃ U W : ℚ, QuarticCover A B 1 U 1 W ∧ x' = U ^ 2 ∧ y' = U * W
```

and the two constructive preimage steps are `phi_preimage_of_cover` and `dual_preimage_of_cover`. For `φ`, given `QuarticCover (-2 * a) (a ^ 2 - 4 * b) 1 U 1 W`, the point `(U², U·W)` of `D(a, b)` is produced as `phi a b hb hd P` where `P` is the point of `E(a, b)` with coordinates `x = (U² − a + W)/2` and `y = x·U`; the whole verification rests on two scalar identities that are exact consequences of the cover equation `W² = U⁴ − 2a·U² + (a² − 4b)`, namely `x² + (a − U²)·x + b = 0` and `x² − b = x·W`, discharged by `linear_combination` with coefficients `1/4` and `−1/4` respectively (the first gives both the curve equation at `P` and `X(a, b, x) = U²`; the second gives `Y(b, x, x·U) = U·W`, and also `x ≠ 0`, since `x = 0` would force `b = 0`). For `ψ`, given `QuarticCover a b 1 U 1 S`, the point `(U², U·S)` of `E(a, b)` is produced as `dualHom a b hb hd (Point.some hp')` where the preimage in `D(a, b)` has coordinates `x′ = a + 2U² − 2S` and `y′ = −2·x′·U`; the corresponding scalar identities are `x′² − (2a + 4U²)·x′ + (a² − 4b) = 0` and `x′² + 4S·x′ − (a² − 4b) = 0`, with `linear_combination` coefficients `4` and `−4` (the second gives both `Y(a² − 4b, x′, y′) = 8·U·S` after the dual map's division by `8`, and `x′ ≠ 0`, since `x′ = 0` would force `a² − 4b = 0`). All of these polynomial identities were additionally checked symbolically with sympy before formalisation, and every one of them reduced to zero.

## Reduced to a hypothesis — and then discharged

As the brief required, the reduction step is isolated as two theorems whose only extra hypothesis is the solubility statement, named `hsol` in both:

```lean
theorem deltaPhi_ker_le_phiHom_range_of_soluble (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0)
    (hsol : ∀ (x' y' : ℚ) (hp : (D a b).Nonsingular x' y'),
      delta (-2 * a) (a ^ 2 - 4 * b) hd (Point.some hp) = 1 →
      ∃ U W : ℚ, QuarticCover (-2 * a) (a ^ 2 - 4 * b) 1 U 1 W
        ∧ x' = U ^ 2 ∧ y' = U * W) :
    (deltaPhi a b hb hd).ker ≤ (phiHom a b hb hd).range

theorem deltaDual_ker_le_dualHom_range_of_soluble (a b : ℚ) (hb : b ≠ 0)
    (hd : a ^ 2 - 4 * b ≠ 0)
    (hsol : ∀ (x y : ℚ) (hp : (E a b).Nonsingular x y),
      delta a b hb (Point.some hp) = 1 →
      ∃ U S : ℚ, QuarticCover a b 1 U 1 S ∧ x = U ^ 2 ∧ y = U * S) :
    (deltaDual a b hb).ker ≤ (dualHom a b hb hd).range
```

These implications are proved completely (the point at infinity is handled by `map_zero`; an affine kernel point is fed through `hsol` and the relevant preimage construction, and the resulting point is identified with the given one by `some_congr`). The hypothesis `hsol` is then discharged in both cases by `exists_cover_of_delta_eq_one` — applied to the model `D(a, b)` for T1 and to `E(a, b)` for T2 — which is exactly the sense in which the `d = 1` solubility "fell to machinery already in the repo": it is a two-case consequence of wave two's characterisation of when a square class is trivial. Two small extraction lemmas, `delta_eq_one_of_deltaPhi_ker` and `delta_eq_one_of_deltaDual_ker`, bridge between kernel membership (additive `= 0`) and the multiplicative statement `δ = 1` used everywhere above. **Nothing in the final T1/T2 theorems is conditional**: the `_of_soluble` forms remain in the file as the explicit reduction the brief asked for, but they are stepping stones, not the end state.

## Verification

The final clean build is in `build_final.log`: `lake build PerfectPower.DescentCover` completed successfully (37.5 s, dependencies served from wave two's cached build tree), and `lake env lean PerfectPower/VerifyCover.lean` (57.1 s) printed, for each of the sixteen declarations audited — `quarticCover_one_iff`, `quarticCover_scale`, `point_of_quarticCover`, `exists_cover_of_delta_eq_one`, `phi_preimage_of_cover`, `dual_preimage_of_cover`, `delta_eq_one_of_deltaPhi_ker`, `delta_eq_one_of_deltaDual_ker`, both `_of_soluble` reductions, both unconditional inclusions, both kernel identifications, and both `_int` forms — exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`, with no additional axioms. A grep of the module finds no `sorry`, no `admit`, and no `axiom` declaration; the only textual occurrence of the word "sorry" is inside the header comment's sentence "there is no `sorry`". Builds were run strictly serially on the one tree, as wave two's experience requires. Two cosmetic notes: the build log shows the two unused-variable linter warnings for `hd` in the `_int` corollaries discussed above, and no other warnings.

## Still open

Within the scope of this wave, nothing is left open: T1 and T2 are proved, not merely reduced. For orientation, the neighbouring items that this wave did **not** touch remain exactly where the earlier reports left them: the divisor-four counting step T3 for `DescentRankBridge`, the decomposition premise in `DescentRankBridge`, and the `PrimeSupport` / `PrimeSaturated` / `hbound` hypotheses in `MordellCompletionBridge`. One honest scoping remark about the cover theory itself: the kernel-to-cover direction is proved here only at `d = 1`, which is all the kernel inclusions need; a general-`d` homogeneous-space theory (relating points with `δ`-value `cls d ≠ 1` to solubility of `C_d`, in the direction opposite to `point_of_quarticCover`) is not formalised and would be the natural next piece if the descent is later pushed toward a full Selmer-group computation. The deliverables are `DescentCover.lean` (the module), `VerifyCover.lean` (the axiom audit), `build_final.log` (the clean build and audit output), and this report, with the buildable tree preserved at `repo_copy/`.
