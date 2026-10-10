import PerfectPower.MordellParity
import PerfectPower.IsogenyCoordinates

namespace PerfectPower.TwoIsogenyPointMap

open WeierstrassCurve WeierstrassCurve.Affine

abbrev E (a b : ℚ) := MordellParity.completed a b 0
abbrev D (a b : ℚ) := E (-2*a) (a^2-4*b)

@[simp] theorem equation (a b x y : ℚ) :
    (E a b).Equation x y ↔ y^2 = x*(x^2+a*x+b) := by
  rw [MordellParity.equation_completed]
  unfold EllipticDivision.cubic
  constructor <;> intro h <;> linear_combination h

@[simp] theorem negY (a b x y : ℚ) : (E a b).negY x y = -y := by
  simp [E, MordellParity.completed, WeierstrassCurve.Affine.negY]

theorem smooth (a b x y : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (hp : y^2 = x*(x^2+a*x+b)) : (E a b).Nonsingular x y := by
  rw [nonsingular_iff', equation]
  refine ⟨hp, ?_⟩
  change 0*y-(3*x^2+2*a*x+b) ≠ 0 ∨ 2*y+0*x+0 ≠ 0
  by_cases hy : y = 0
  · left
    simp only [zero_mul, zero_sub, neg_ne_zero]
    intro hs
    by_cases hx : x = 0
    · simp [hx] at hs
      exact hb hs
    · have hq : x^2+a*x+b = 0 := by
        have := hp
        rw [hy, zero_pow (by decide : 2 ≠ 0)] at this
        exact (mul_eq_zero.mp this.symm).resolve_left hx
      have hxq : x*(2*x+a) = 0 := by linear_combination hs-hq
      have ht : 2*x+a = 0 := (mul_eq_zero.mp hxq).resolve_left hx
      apply hd
      nlinarith [sq_nonneg (2*x+a)]
  · right
    simpa using mul_ne_zero (by norm_num : (2:ℚ) ≠ 0) hy

theorem dual_smooth (a b : ℚ) (hb : b ≠ 0) :
    (-2*a)^2-4*(a^2-4*b) ≠ 0 := by
  have he : (-2*a)^2-4*(a^2-4*b) = 16*b := by ring
  rw [he]
  exact mul_ne_zero (by norm_num) hb

def X (a b x : ℚ) := x+a+b/x
def Y (b x y : ℚ) := y*(1-b/x^2)

theorem image_smooth (a b x y : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (hx : x ≠ 0) (hp : (E a b).Nonsingular x y) :
    (D a b).Nonsingular (X a b x) (Y b x y) := by
  apply smooth (-2*a) (a^2-4*b) _ _ hd (dual_smooth a b hb)
  have h := IsogenyCoordinates.isogeny_lands_on_curve a b x y hx ((equation ..).mp hp.1)
  convert h using 1
  dsimp [X,Y]
  ring

noncomputable def phi (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (E a b).Point → (D a b).Point
  | .zero => 0
  | @Point.some _ _ _ x y hp =>
    if hx : x = 0 then 0 else Point.some (image_smooth a b x y hb hd hx hp)

@[simp] theorem phi_zero (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    phi a b hb hd 0 = 0 := rfl

theorem phi_some (a b x y : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (hp : (E a b).Nonsingular x y) (hx : x ≠ 0) :
    phi a b hb hd (Point.some hp) = Point.some (image_smooth a b x y hb hd hx hp) := by
  simp only [phi, dif_neg hx]

theorem phi_some_zero (a b y : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (hp : (E a b).Nonsingular 0 y) : phi a b hb hd (Point.some hp) = 0 := by
  simp [phi]

theorem some_congr {W : Affine ℚ} {x y x' y' : ℚ}
    {hp : W.Nonsingular x y} {hq : W.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') : Point.some hp = Point.some hq := by
  subst hx; subst hy; rfl

theorem phi_neg (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P : (E a b).Point) : phi a b hb hd (-P) = -phi a b hb hd P := by
  cases P with
  | zero => rfl
  | @some x y hp =>
    rw [Point.neg_some]
    by_cases hx : x = 0
    · subst x
      rw [phi_some_zero, phi_some_zero, Point.neg_zero]
    · rw [phi_some _ _ _ _ hb hd _ hx, phi_some _ _ _ _ hb hd _ hx, Point.neg_some]
      apply some_congr rfl
      simp only [D, TwoIsogenyPointMap.negY, Y, neg_mul]

noncomputable def T (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) : (E a b).Point :=
  Point.some (smooth a b 0 0 hb hd (by norm_num))

theorem T_ne_zero (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    T a b hb hd ≠ 0 := Point.some_ne_zero _

@[simp] theorem T_add_T (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    T a b hb hd + T a b hb hd = 0 := by
  apply Point.add_self_of_Y_eq
  rw [TwoIsogenyPointMap.negY]
  ring

@[simp] theorem phi_T (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    phi a b hb hd (T a b hb hd) = 0 := by
  apply phi_some_zero

theorem phi_eq_zero_iff (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P : (E a b).Point) : phi a b hb hd P = 0 ↔ P = 0 ∨ P = T a b hb hd := by
  cases P with
  | zero => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | @some x y hp =>
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := by
        have he := (equation ..).mp hp.1
        simp only [zero_mul] at he
        exact pow_eq_zero he
      subst y
      rw [phi_some_zero]
      exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
    · rw [phi_some _ _ _ _ hb hd hp hx]
      constructor
      · intro he
        exact False.elim (Point.some_ne_zero _ he)
      · rintro (he | he)
        · exact False.elim (Point.some_ne_zero hp he)
        · have hc : x = 0 ∧ y = 0 := by
            simpa only [T, Point.some.injEq] using he
          have h := hc.1
          exact False.elim (hx h)


theorem translate_coordinates (a b x y : ℚ) (hx : x ≠ 0)
    (hp : y^2 = x*(x^2+a*x+b)) :
    (E a b).addX x 0 ((E a b).slope x 0 y 0) = b/x ∧
    (E a b).addY x 0 y ((E a b).slope x 0 y 0) = -b*y/x^2 := by
  rw [slope_of_X_ne hx]
  simp only [sub_zero, addX, addY, negAddY, E, MordellParity.completed,
    WeierstrassCurve.Affine.negY, zero_mul, zero_add]
  constructor
  · field_simp [hx]
    linear_combination x*hp
  · field_simp [hx]
    linear_combination -y*x^2*hp

theorem translation_image (a b x y : ℚ) (hb : b ≠ 0) (hx : x ≠ 0) :
    X a b (b/x) = X a b x ∧ Y b (b/x) (-b*y/x^2) = Y b x y := by
  dsimp [X,Y]
  constructor <;> field_simp [hx,hb] <;> ring

/-- Addition by the kernel point leaves the actual point map unchanged. -/
theorem phi_add_T (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P : (E a b).Point) : phi a b hb hd (P+T a b hb hd) = phi a b hb hd P := by
  cases P with
  | zero => exact phi_T a b hb hd
  | @some x y hp =>
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := by
        have he := (equation ..).mp hp.1
        simp only [zero_mul] at he
        exact pow_eq_zero he
      subst y
      change phi a b hb hd (T a b hb hd + T a b hb hd) = _
      rw [T_add_T, phi_zero, phi_some_zero]
    · have hc := translate_coordinates a b x y hx ((equation ..).mp hp.1)
      have hsum : (E a b).addX x 0 ((E a b).slope x 0 y 0) ≠ 0 := by
        rw [hc.1]
        exact div_ne_zero hb hx
      unfold T
      rw [Point.add_of_X_ne hx, phi_some _ _ _ _ hb hd _ hsum,
        phi_some _ _ _ _ hb hd _ hx]
      apply some_congr
      · rw [hc.1]
        exact (translation_image a b x y hb hx).1
      · rw [hc.1, hc.2]
        exact (translation_image a b x y hb hx).2

/-- The map respects addition whenever one summand belongs to its kernel. -/
theorem phi_add_of_kernel (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P Q : (E a b).Point) (hQ : phi a b hb hd Q = 0) :
    phi a b hb hd (P+Q) = phi a b hb hd P + phi a b hb hd Q := by
  rcases (phi_eq_zero_iff a b hb hd Q).mp hQ with h | h
  · subst Q
    rw [add_zero, phi_zero, add_zero]
  · subst Q
    rw [phi_add_T, phi_T, add_zero]


/-- The chord/tangent polynomial records all three roots, including multiplicities. -/
theorem chord_roots (a b x₁ x₂ y₁ y₂ : ℚ)
    (h₁ : (E a b).Nonsingular x₁ y₁) (h₂ : (E a b).Nonsingular x₂ y₂)
    (hxy : ¬(x₁=x₂ ∧ y₁=(E a b).negY x₂ y₂)) :
    let l := (E a b).slope x₁ x₂ y₁ y₂
    let n := y₁-l*x₁
    let r := (E a b).addX x₁ x₂ l
    x₁+x₂+r=l^2-a ∧
      x₁*x₂+x₁*r+x₂*r=b-2*l*n ∧ x₁*x₂*r=n^2 := by
  dsimp only
  have he := addPolynomial_slope h₁.1 h₂.1 hxy
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective] at he
  have hc := congrArg Cubic.c he
  have hd := congrArg Cubic.d he
  change 2*x₁*((E a b).slope x₁ x₂ y₁ y₂)^2+
    (0*x₁-2*y₁-0)*(E a b).slope x₁ x₂ y₁ y₂+(-0*y₁+b) =
      x₁*x₂+x₁*(E a b).addX x₁ x₂ ((E a b).slope x₁ x₂ y₁ y₂)+
        x₂*(E a b).addX x₁ x₂ ((E a b).slope x₁ x₂ y₁ y₂) at hc
  change -x₁^2*((E a b).slope x₁ x₂ y₁ y₂)^2+
    (2*x₁*y₁+0*x₁)*(E a b).slope x₁ x₂ y₁ y₂-(y₁^2+0*y₁-0) =
      -(x₁*x₂*(E a b).addX x₁ x₂ ((E a b).slope x₁ x₂ y₁ y₂)) at hd
  refine ⟨?_, ?_, ?_⟩
  · simp only [addX, E, MordellParity.completed]
    ring
  · linear_combination -hc
  · linear_combination hd

/-- The image of a nonvertical chord is a line with its computed slope and intercept. -/
theorem image_line (a b l n x : ℚ) (hx : x ≠ 0) (hn : n ≠ 0)
    (hp : (l*x+n)^2 = x*(x^2+a*x+b)) :
    Y b x (l*x+n) = (l-b/n)*X a b x + (n-a*l+b*l^2/n) := by
  dsimp [X,Y]
  linear_combination (norm := (field_simp [hx,hn]; ring)) (-b/(n*x^2))*hp

/-- Symmetric root identities transport the chord and its tangent multiplicity. -/
theorem image_root_sums (a b l n x₁ x₂ r : ℚ)
    (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) (hr : r ≠ 0) (hn : n ≠ 0)
    (hs : x₁+x₂+r=l^2-a)
    (hp : x₁*x₂+x₁*r+x₂*r=b-2*l*n) (ht : x₁*x₂*r=n^2) :
    X a b x₁+X a b x₂+X a b r=(l-b/n)^2+2*a ∧
    X a b x₁*X a b x₂+X a b x₁*X a b r+X a b x₂*X a b r =
      a^2-4*b-2*(l-b/n)*(n-a*l+b*l^2/n) := by
  have es : X a b x₁+X a b x₂+X a b r =
      (x₁+x₂+r)+3*a+b*(x₁*x₂+x₁*r+x₂*r)/(x₁*x₂*r) := by
    dsimp [X]
    field_simp [h₁,h₂,hr]
    ring
  have ep : X a b x₁*X a b x₂+X a b x₁*X a b r+X a b x₂*X a b r =
      (x₁*x₂+x₁*r+x₂*r)+2*a*(x₁+x₂+r)+3*a^2-3*b+
      (b*((x₁+x₂+r)+2*a)*(x₁*x₂+x₁*r+x₂*r)+b^2*(x₁+x₂+r))/(x₁*x₂*r) := by
    dsimp [X]
    field_simp [h₁,h₂,hr]
    ring
  rw [hs,hp,ht] at es ep
  constructor
  · rw [es]
    field_simp [hn]
    ring
  · rw [ep]
    field_simp [hn]
    ring


theorem line_second (a b x₁ x₂ y₁ y₂ : ℚ)
    (h₁ : (E a b).Nonsingular x₁ y₁) (h₂ : (E a b).Nonsingular x₂ y₂)
    (hxy : ¬(x₁=x₂ ∧ y₁=(E a b).negY x₂ y₂)) :
    y₂ = (E a b).slope x₁ x₂ y₁ y₂*x₂+
      (y₁-(E a b).slope x₁ x₂ y₁ y₂*x₁) := by
  by_cases hx : x₁=x₂
  · have hy := Y_eq_of_Y_ne h₁.1 h₂.1 hx (fun h => hxy ⟨hx,h⟩)
    rw [← hx, ← hy]
    ring
  · rw [slope_of_X_ne hx]
    field_simp [sub_ne_zero.mpr hx]
    ring

theorem line_slope (a b x₁ x₂ r y₁ y₂ l n : ℚ)
    (h₁ : (E a b).Nonsingular x₁ y₁) (h₂ : (E a b).Nonsingular x₂ y₂)
    (hy₁ : y₁=l*x₁+n) (hy₂ : y₂=l*x₂+n)
    (hs : x₁+x₂+r=l^2-a) (hp : x₁*x₂+x₁*r+x₂*r=b-2*l*n) :
    ¬(x₁=x₂ ∧ y₁=(E a b).negY x₂ y₂) ∧ (E a b).slope x₁ x₂ y₁ y₂=l := by
  by_cases hx : x₁=x₂
  · subst x₂
    have hy : y₁=y₂ := hy₁.trans hy₂.symm
    have he : 3*x₁^2+2*a*x₁+b=2*l*y₁ := by
      rw [hy₁]
      linear_combination 2*x₁*hs-hp
    have hn : y₁ ≠ 0 := by
      intro hz
      have hns := (nonsingular_iff' ..).mp h₁
      change _ ∧ (0*y₁-(3*x₁^2+2*a*x₁+b) ≠ 0 ∨ 2*y₁+0*x₁+0 ≠ 0) at hns
      rw [he,hz] at hns
      simpa using hns.2
    have hneg : y₁ ≠ (E a b).negY x₁ y₂ := by
      rw [TwoIsogenyPointMap.negY, ← hy]
      intro hz
      apply hn
      linarith
    refine ⟨fun h => hneg h.2, ?_⟩
    rw [slope_of_Y_ne rfl hneg]
    change (3*x₁^2+2*a*x₁+b-0*y₁)/(y₁-(E a b).negY x₁ y₁)=l
    rw [TwoIsogenyPointMap.negY, he]
    field_simp [hn]
    ring
  · refine ⟨fun h => hx h.1, ?_⟩
    rw [slope_of_X_ne hx, hy₁, hy₂]
    field_simp [sub_ne_zero.mpr hx]
    ring

theorem image_vertical (a b l x₁ x₂ : ℚ) (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0)
    (hp : x₁*x₂=b) :
    X a b x₁=X a b x₂ ∧ Y b x₁ (l*x₁) = -Y b x₂ (l*x₂) := by
  rw [← hp]
  dsimp [X,Y]
  constructor <;> field_simp [h₁,h₂] <;> ring


/-- The rational degree-two map respects the actual Mathlib elliptic addition law. -/
theorem phi_add (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P Q : (E a b).Point) :
    phi a b hb hd (P+Q)=phi a b hb hd P+phi a b hb hd Q := by
  classical
  by_cases hP : phi a b hb hd P = 0
  · simpa only [add_comm] using phi_add_of_kernel a b hb hd Q P hP
  by_cases hQ : phi a b hb hd Q = 0
  · exact phi_add_of_kernel a b hb hd P Q hQ
  cases P with
  | zero => exact False.elim (hP rfl)
  | @some x₁ y₁ hp =>
    cases Q with
    | zero => exact False.elim (hQ rfl)
    | @some x₂ y₂ hq =>
      have hx₁ : x₁ ≠ 0 := by
        intro hz; subst x₁; exact hP (phi_some_zero a b y₁ hb hd hp)
      have hx₂ : x₂ ≠ 0 := by
        intro hz; subst x₂; exact hQ (phi_some_zero a b y₂ hb hd hq)
      by_cases hxy : x₁=x₂ ∧ y₁=(E a b).negY x₂ y₂
      · rw [Point.add_of_Y_eq hxy.1 hxy.2, phi_zero,
          phi_some _ _ _ _ hb hd _ hx₁, phi_some _ _ _ _ hb hd _ hx₂]
        symm
        apply Point.add_of_Y_eq
        · rw [hxy.1]
        · rw [hxy.2]
          simp only [D, TwoIsogenyPointMap.negY, Y, neg_mul]
          rw [hxy.1]
      · let l := (E a b).slope x₁ x₂ y₁ y₂
        let n := y₁-l*x₁
        let r := (E a b).addX x₁ x₂ l
        have hs := chord_roots a b x₁ x₂ y₁ y₂ hp hq hxy
        change x₁+x₂+r=l^2-a ∧ x₁*x₂+x₁*r+x₂*r=b-2*l*n ∧ x₁*x₂*r=n^2 at hs
        have hy₁ : y₁=l*x₁+n := by dsimp [n]; ring
        have hy₂ : y₂=l*x₂+n := line_second a b x₁ x₂ y₁ y₂ hp hq hxy
        have hyr : (E a b).addY x₁ x₂ y₁ l = -(l*r+n) := by
          simp only [addY, negAddY, TwoIsogenyPointMap.negY]
          dsimp [r,n]
          ring
        rw [Point.add_some hxy, phi_some _ _ _ _ hb hd _ hx₁,
          phi_some _ _ _ _ hb hd _ hx₂]
        by_cases hr : r=0
        · have hn : n=0 := by
            have he := hs.2.2
            rw [hr,mul_zero] at he
            exact pow_eq_zero he.symm
          have hprod : x₁*x₂=b := by simpa only [hr,hn,mul_zero,add_zero,sub_zero] using hs.2.1
          have hvir := image_vertical a b l x₁ x₂ hx₁ hx₂ hprod
          have hxsum : (E a b).addX x₁ x₂ l=0 := hr
          rw [phi, dif_pos hxsum]
          symm
          apply Point.add_of_Y_eq hvir.1
          rw [D, TwoIsogenyPointMap.negY, hy₁, hy₂, hn, add_zero, add_zero]
          exact hvir.2
        · have hn : n ≠ 0 := by
            intro hz
            have he := hs.2.2
            rw [hz,zero_pow (by decide : 2 ≠ 0)] at he
            exact mul_ne_zero (mul_ne_zero hx₁ hx₂) hr he
          have hsum := image_root_sums a b l n x₁ x₂ r hx₁ hx₂ hr hn hs.1 hs.2.1 hs.2.2
          have hi₁ := image_line a b l n x₁ hx₁ hn (by rw [← hy₁]; exact (equation ..).mp hp.1)
          have hi₂ := image_line a b l n x₂ hx₂ hn (by rw [← hy₂]; exact (equation ..).mp hq.1)
          rw [← hy₁] at hi₁
          rw [← hy₂] at hi₂
          have ht := line_slope (-2*a) (a^2-4*b) (X a b x₁) (X a b x₂) (X a b r)
            (Y b x₁ y₁) (Y b x₂ y₂) (l-b/n) (n-a*l+b*l^2/n)
            (image_smooth a b x₁ y₁ hb hd hx₁ hp) (image_smooth a b x₂ y₂ hb hd hx₂ hq)
            hi₁ hi₂ (by linear_combination hsum.1) hsum.2
          rw [phi_some _ _ _ _ hb hd _ hr, Point.add_some ht.1]
          apply some_congr
          · rw [ht.2]
            change X a b r = (l-b/n)^2+0*(l-b/n)-(-2*a)-X a b x₁-X a b x₂
            linear_combination hsum.1
          · have hp₃ := (nonsingular_add hp hq hxy).1
            have hc₃ : (l*r+n)^2=r*(r^2+a*r+b) := by
              have he := (equation ..).mp hp₃
              rw [hyr] at he
              simpa only [neg_sq] using he
            have hi₃ := image_line a b l n r hr hn hc₃
            rw [hyr, ht.2]
            simp only [Y, neg_mul] at hi₃ ⊢
            simp only [addY, negAddY, D, E, MordellParity.completed,
              WeierstrassCurve.Affine.negY, addX, zero_mul, zero_add, sub_zero]
            dsimp only [Y] at hi₁
            linear_combination -hi₃ + hi₁ - (l-b/n)*hsum.1

noncomputable def phiHom (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (E a b).Point →+ (D a b).Point where
  toFun := phi a b hb hd
  map_zero' := phi_zero a b hb hd
  map_add' := phi_add a b hb hd

end PerfectPower.TwoIsogenyPointMap
