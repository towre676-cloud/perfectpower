import PerfectPower.EllipticPointDivision

namespace PerfectPower.EllipticSquareTransport
open WeierstrassCurve WeierstrassCurve.Affine

/-- The completed-square model of the original generalized equation. -/
def model (W : Affine ℚ) : Affine ℚ := EllipticPointDivision.completed
  (W.a₂ + W.a₁^2/4) (W.a₄ + W.a₁*W.a₃/2) (W.a₆ + W.a₃^2/4)
/-- The original-to-completed ordinate. -/
def shift (W : Affine ℚ) (x y : ℚ) : ℚ := y + (W.a₁*x+W.a₃)/2

/-- Completing the square preserves the discriminant. -/
theorem discriminant (W : Affine ℚ) : (model W).Δ = W.Δ := by
  simp only [model, EllipticPointDivision.completed, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Exact equation transport in both directions. -/
theorem equation (W : Affine ℚ) (x y : ℚ) :
    (model W).Equation x (shift W x y) ↔ W.Equation x y := by
  rw [equation_iff', equation_iff']
  simp only [model, EllipticPointDivision.completed, shift]
  constructor <;> intro h <;> linear_combination h

/-- Smooth original points yield smooth completed points. -/
theorem nonsingular (W : Affine ℚ) (hΔ : W.Δ ≠ 0) (x y : ℚ) :
    (model W).Nonsingular x (shift W x y) ↔ W.Nonsingular x y := by
  rw [← equation_iff_nonsingular_of_Δ_ne_zero (by simpa [discriminant] using hΔ),
    ← equation_iff_nonsingular_of_Δ_ne_zero hΔ, equation]

/-- Reflection pairs are preserved by the ordinate shift. -/
theorem vertical (W : Affine ℚ) (x₁ x₂ y₁ y₂ : ℚ) :
    (x₁=x₂ ∧ shift W x₁ y₁ = (model W).negY x₂ (shift W x₂ y₂)) ↔
    (x₁=x₂ ∧ y₁=W.negY x₂ y₂) := by
  constructor <;> rintro ⟨hx,hy⟩ <;> subst x₂ <;> refine ⟨rfl, ?_⟩
  all_goals simp only [shift, model, EllipticPointDivision.completed, negY] at *
  all_goals linear_combination hy

/-- Both tangent and secant slopes transform by the same affine shift. -/
theorem slope_shift (W : Affine ℚ) (x₁ x₂ y₁ y₂ : ℚ)
    (hv : ¬(x₁=x₂ ∧ y₁=W.negY x₂ y₂))
    (heq : x₁=x₂ → y₁=y₂) :
    (model W).slope x₁ x₂ (shift W x₁ y₁) (shift W x₂ y₂) =
      W.slope x₁ x₂ y₁ y₂ + W.a₁/2 := by
  by_cases hx : x₁=x₂
  · have he := heq hx
    subst x₂
    subst y₂
    have hy : y₁ ≠ W.negY x₁ y₁ := fun h => hv ⟨rfl,h⟩
    have hy' : shift W x₁ y₁ ≠ (model W).negY x₁ (shift W x₁ y₁) :=
      fun h => hv ((vertical W x₁ x₁ y₁ y₁).mp ⟨rfl,h⟩)
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy]
    have hd : y₁-W.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hc : shift W x₁ y₁ - (model W).negY x₁ (shift W x₁ y₁) =
        y₁-W.negY x₁ y₁ := by
      simp only [shift, model, EllipticPointDivision.completed, negY]
      ring
    rw [hc]
    have hn : 3*x₁^2+2*(model W).a₂*x₁+(model W).a₄-(model W).a₁*shift W x₁ y₁ =
        (3*x₁^2+2*W.a₂*x₁+W.a₄-W.a₁*y₁) + W.a₁/2*(y₁-W.negY x₁ y₁) := by
      simp only [model, EllipticPointDivision.completed, negY]
      ring
    rw [hn, add_div]
    rw [mul_div_cancel_right₀ _ hd]
  · rw [slope_of_X_ne hx, slope_of_X_ne hx]
    have hd : x₁-x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hn : shift W x₁ y₁ - shift W x₂ y₂ =
        (y₁-y₂)+W.a₁/2*(x₁-x₂) := by unfold shift; ring
    rw [hn, add_div]
    rw [mul_div_cancel_right₀ _ hd]


/-- Equal abscissae of nonopposite curve points give equal ordinates. -/
theorem same_x (W : Affine ℚ) (x₁ x₂ y₁ y₂ : ℚ)
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hv : ¬(x₁=x₂ ∧ y₁=W.negY x₂ y₂)) (hx : x₁=x₂) : y₁=y₂ := by
  subst x₂
  rw [equation_iff'] at h₁ h₂
  have h : (y₁-y₂)*(y₁+y₂+W.a₁*x₁+W.a₃)=0 := by linear_combination h₁-h₂
  rcases mul_eq_zero.mp h with he | he
  · exact sub_eq_zero.mp he
  · exfalso
    apply hv
    refine ⟨rfl, ?_⟩
    simp only [negY]
    linear_combination he

/-- Abscissae of sums agree under the slope shift. -/
theorem addX_shift (W : Affine ℚ) (x₁ x₂ l : ℚ) :
    (model W).addX x₁ x₂ (l+W.a₁/2) = W.addX x₁ x₂ l := by
  simp only [addX, model, EllipticPointDivision.completed]
  ring
/-- Ordinates of sums agree under the slope shift. -/
theorem addY_shift (W : Affine ℚ) (x₁ x₂ y l : ℚ) :
    (model W).addY x₁ x₂ (shift W x₁ y) (l+W.a₁/2) =
      shift W (W.addX x₁ x₂ l) (W.addY x₁ x₂ y l) := by
  simp only [addY, negAddY, addX, negY, shift, model, EllipticPointDivision.completed]
  ring

/-- The actual point map, with nonsingularity established from the discriminant. -/
noncomputable def forward (W : Affine ℚ) (hΔ : W.Δ ≠ 0) : W.Point → (model W).Point
  | .zero => .zero
  | @Point.some _ _ _ x y h => Point.some ((nonsingular W hΔ x y).mpr h)
/-- The inverse actual point map. -/
noncomputable def backward (W : Affine ℚ) (hΔ : W.Δ ≠ 0) : (model W).Point → W.Point
  | .zero => .zero
  | @Point.some _ _ _ x y h => Point.some (by
      apply (nonsingular W hΔ x (y-(W.a₁*x+W.a₃)/2)).mp
      convert h using 1
      unfold shift
      ring)

/-- Point addition commutes with completion, including infinity and vertical lines. -/
theorem forward_add (W : Affine ℚ) (hΔ : W.Δ ≠ 0) (P Q : W.Point) :
    forward W hΔ (P+Q) = forward W hΔ P + forward W hΔ Q := by
  cases P with
  | zero =>
    change forward W hΔ (0+Q) = 0+forward W hΔ Q
    simp
  | @some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | @some x₂ y₂ h₂ =>
      by_cases hv : x₁=x₂ ∧ y₁=W.negY x₂ y₂
      · have hv' := (vertical W x₁ x₂ y₁ y₂).mpr hv
        rw [Point.add_of_Y_eq hv.1 hv.2]
        change 0 = Point.some _ + Point.some _
        rw [Point.add_of_Y_eq hv'.1 hv'.2]
      · have hv' : ¬(x₁=x₂ ∧ shift W x₁ y₁ = (model W).negY x₂ (shift W x₂ y₂)) :=
          fun h => hv ((vertical W x₁ x₂ y₁ y₂).mp h)
        rw [Point.add_some hv]
        change Point.some _ = Point.some _ + Point.some _
        rw [Point.add_some hv', Point.some.injEq]
        have hs := slope_shift W x₁ x₂ y₁ y₂ hv (same_x W x₁ x₂ y₁ y₂ h₁.1 h₂.1 hv)
        rw [hs, addX_shift, addY_shift]
        exact ⟨rfl,rfl⟩

/-- Completion is an additive equivalence of actual rational point groups. -/
noncomputable def equiv (W : Affine ℚ) (hΔ : W.Δ ≠ 0) : W.Point ≃+ (model W).Point where
  toFun := forward W hΔ
  invFun := backward W hΔ
  left_inv P := by
    cases P with
    | zero => rfl
    | @some x y h =>
      change Point.some _ = Point.some h
      rw [Point.some.injEq]
      exact ⟨rfl, by unfold shift; ring⟩
  right_inv P := by
    cases P with
    | zero => rfl
    | @some x y h =>
      change Point.some _ = Point.some h
      rw [Point.some.injEq]
      exact ⟨rfl, by unfold shift; ring⟩
  map_add' := forward_add W hΔ

/-- Every multiplication fibre transports through the explicit actual point map. -/
theorem fibre (W : Affine ℚ) (hΔ : W.Δ ≠ 0) (n : ℤ) (Q P : W.Point) :
    n • equiv W hΔ Q = equiv W hΔ P ↔ n • Q = P :=
  EllipticDivision.transport_fibre (equiv W hΔ) n Q P

/-- Coordinate encoding of actual points, including infinity. -/
def coordinates {W : Affine ℚ} : W.Point → Option (ℚ × ℚ)
  | .zero => none
  | @Point.some _ _ _ x y _ => some (x,y)

/-- The encoding distinguishes actual rational points. -/
theorem coordinates_injective (W : Affine ℚ) : Function.Injective (coordinates (W:=W)) := by
  intro P Q h
  cases P <;> cases Q <;> simp only [coordinates, Option.some.injEq, Prod.mk.injEq] at h
  · rfl
  · contradiction
  · contradiction
  · rw [Point.some.injEq]; exact h


/-- Identity transport along an equality of affine models. -/
noncomputable def castEquiv {W V : Affine ℚ} (h : W=V) : W.Point ≃+ V.Point := by
  subst V
  exact AddEquiv.refl _

/-- Casting a point along a model equality does not change its coordinates. -/
theorem coordinates_cast {W V : Affine ℚ} (h : W=V) (P : W.Point) :
    coordinates (castEquiv h P) = coordinates P := by subst V; rfl

/-- The inverse point map is the literal inverse ordinate shift. -/
theorem coordinates_backward (W : Affine ℚ) (hΔ : W.Δ ≠ 0) (P : (model W).Point) :
    coordinates (backward W hΔ P) =
      (coordinates P).map (fun xy => (xy.1,xy.2-(W.a₁*xy.1+W.a₃)/2)) := by
  cases P <;> rfl

/-- An actual group isomorphism transports a complete literal fibre list. -/
theorem list_transport {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : ℤ) (P : H) (L : List H)
    (hL : ∀ Q, n • Q = P ↔ Q ∈ L) (Q : G) :
    n • Q = e.symm P ↔ Q ∈ L.map e.symm := by
  rw [← e.injective.eq_iff, map_zsmul, AddEquiv.apply_symm_apply, hL]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨e Q,h,by simp⟩
  · intro h
    obtain ⟨T,hT,he⟩ := List.mem_map.mp h
    simpa [← he] using hT

end PerfectPower.EllipticSquareTransport
