import PerfectPower.TwoIsogenyPointMap
import PerfectPower.IsogenyIndexBridges

namespace PerfectPower.TwoIsogenyDual

open WeierstrassCurve WeierstrassCurve.Affine
open TwoIsogenyPointMap

theorem scaled_smooth (a b x y : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (hp : (E (4*a) (16*b)).Nonsingular x y) : (E a b).Nonsingular (x/4) (y/8) := by
  apply smooth a b _ _ hb hd
  have he := (equation ..).mp hp.1
  linear_combination (1/64:ℚ)*he

noncomputable def scaleBack (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (E (4*a) (16*b)).Point → (E a b).Point
  | .zero => 0
  | .some hp => Point.some (scaled_smooth a b _ _ hb hd hp)

theorem scaleBack_slope (a b x₁ x₂ y₁ y₂ : ℚ) :
    (E a b).slope (x₁/4) (x₂/4) (y₁/8) (y₂/8) =
      (E (4*a) (16*b)).slope x₁ x₂ y₁ y₂ / 2 := by
  by_cases hx : x₁=x₂
  · subst x₂
    by_cases hy : y₁=-y₂
    · have hi : y₁/8=(E a b).negY (x₁/4) (y₂/8) := by
        rw [TwoIsogenyPointMap.negY,hy]; ring
      have ho : y₁=(E (4*a) (16*b)).negY x₁ y₂ := by
        rw [TwoIsogenyPointMap.negY]; exact hy
      rw [slope_of_Y_eq rfl hi,slope_of_Y_eq rfl ho,zero_div]
    · have hi : y₁/8 ≠ (E a b).negY (x₁/4) (y₂/8) := by
        rw [TwoIsogenyPointMap.negY]
        intro he; apply hy; linarith
      have ho : y₁ ≠ (E (4*a) (16*b)).negY x₁ y₂ := by
        rw [TwoIsogenyPointMap.negY]; exact hy
      rw [slope_of_Y_ne rfl hi,slope_of_Y_ne rfl ho]
      simp only [TwoIsogenyPointMap.negY,E,MordellParity.completed]
      by_cases hz : y₁=0
      · simp [hz]
      · field_simp [hz]; ring
  · have hi : x₁/4 ≠ x₂/4 := by intro he; apply hx; linarith
    rw [slope_of_X_ne hi,slope_of_X_ne hx]
    field_simp [sub_ne_zero.mpr hx]
    ring

theorem scaleBack_add (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P Q : (E (4*a) (16*b)).Point) :
    scaleBack a b hb hd (P+Q)=scaleBack a b hb hd P+scaleBack a b hb hd Q := by
  cases P with
  | zero => change scaleBack a b hb hd (0+Q) = 0+scaleBack a b hb hd Q
            rw [zero_add,zero_add]
  | @some x₁ y₁ hp =>
    cases Q with
    | zero => change scaleBack a b hb hd (Point.some hp+0) = scaleBack a b hb hd (Point.some hp)+0
              rw [add_zero,add_zero]
    | @some x₂ y₂ hq =>
      by_cases hxy : x₁=x₂ ∧ y₁=(E (4*a) (16*b)).negY x₂ y₂
      · rw [Point.add_of_Y_eq hxy.1 hxy.2]
        change 0 = Point.some _ + Point.some _
        symm
        apply Point.add_of_Y_eq
        · rw [hxy.1]
        · rw [hxy.2,TwoIsogenyPointMap.negY,TwoIsogenyPointMap.negY]; ring
      · have hi : ¬(x₁/4=x₂/4 ∧ y₁/8=(E a b).negY (x₂/4) (y₂/8)) := by
          rintro ⟨hx,hy⟩
          apply hxy
          rw [TwoIsogenyPointMap.negY] at hy ⊢
          exact ⟨by linarith,by linarith⟩
        rw [Point.add_some hxy]
        change Point.some _ = Point.some _ + Point.some _
        rw [Point.add_some hi]
        apply some_congr
        · simp only [addX]
          rw [scaleBack_slope]
          dsimp only [E,MordellParity.completed]
          ring
        · simp only [addY,negAddY,TwoIsogenyPointMap.negY,addX]
          rw [scaleBack_slope]
          dsimp only [E,MordellParity.completed]
          ring

noncomputable def scaleBackHom (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (E (4*a) (16*b)).Point →+ (E a b).Point where
  toFun := scaleBack a b hb hd
  map_zero' := rfl
  map_add' := scaleBack_add a b hb hd


theorem dual_a (a : ℚ) : -2*(-2*a)=4*a := by ring
theorem dual_b (a b : ℚ) : (-2*a)^2-4*(a^2-4*b)=16*b := by ring

noncomputable def pointCastHom (a b a' b' : ℚ) (ha : a=a') (hb : b=b') :
    (E a b).Point →+ (E a' b').Point := by
  subst a'; subst b'
  exact AddMonoidHom.id _

theorem pointCast_some (a b a' b' x y : ℚ) (ha : a=a') (hb : b=b')
    (hp : (E a b).Nonsingular x y) (hq : (E a' b').Nonsingular x y) :
    pointCastHom a b a' b' ha hb (Point.some hp) = Point.some hq := by
  subst a'; subst b'
  rfl

noncomputable def rawDualHom (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (D a b).Point →+ (E (4*a) (16*b)).Point :=
  (pointCastHom _ _ _ _ (dual_a a) (dual_b a b)).comp
    (phiHom (-2*a) (a^2-4*b) hd (dual_smooth a b hb))

noncomputable def dualHom (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (D a b).Point →+ (E a b).Point :=
  (scaleBackHom a b hb hd).comp (rawDualHom a b hb hd)

theorem rawDual_some (a b x y : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (hp : (D a b).Nonsingular x y) (hx : x ≠ 0) :
    rawDualHom a b hb hd (Point.some hp) =
      Point.some (smooth (4*a) (16*b) (X (-2*a) (a^2-4*b) x) (Y (a^2-4*b) x y)
        (mul_ne_zero (by norm_num) hb) (by rw [show (4*a)^2-4*(16*b)=16*(a^2-4*b) by ring]; exact mul_ne_zero (by norm_num) hd)
        (by have he := IsogenyCoordinates.isogeny_lands_on_curve (-2*a) (a^2-4*b) x y hx ((equation ..).mp hp.1)
            dsimp [X,Y]; convert he using 1
            ring)) := by
  change pointCastHom _ _ _ _ _ _ (phi (-2*a) (a^2-4*b) hd (dual_smooth a b hb) (Point.some hp)) = _
  rw [phi_some _ _ _ _ hd _ hp hx]
  apply pointCast_some


theorem rawDual_some_zero (a b y : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (hp : (D a b).Nonsingular 0 y) : rawDualHom a b hb hd (Point.some hp)=0 := by
  change pointCastHom _ _ _ _ _ _ (phi (-2*a) (a^2-4*b) hd (dual_smooth a b hb) (Point.some hp)) = 0
  rw [phi_some_zero,map_zero]

theorem rawDual_of_x_zero (a b x y : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (hp : (D a b).Nonsingular x y) (hx : x=0) : rawDualHom a b hb hd (Point.some hp)=0 := by
  subst x
  exact rawDual_some_zero a b y hb hd hp

theorem dual_some (a b x y : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (hp : (D a b).Nonsingular x y) (hx : x ≠ 0) :
    ∃ hq : (E a b).Nonsingular (X (-2*a) (a^2-4*b) x/4) (Y (a^2-4*b) x y/8),
      dualHom a b hb hd (Point.some hp)=Point.some hq := by
  change ∃ _, scaleBack a b hb hd (rawDualHom a b hb hd (Point.some hp)) = _
  rw [rawDual_some a b x y hb hd hp hx]
  exact ⟨_,rfl⟩

theorem doubling_x (a b x y : ℚ) (hy : y ≠ 0)
    (hp : y^2=x*(x^2+a*x+b)) :
    (E a b).addX x x ((E a b).slope x x y y)=(x^2-b)^2/(4*y^2) := by
  have hn : y ≠ (E a b).negY x y := by
    rw [TwoIsogenyPointMap.negY]; intro he; apply hy; linarith
  rw [slope_of_Y_ne rfl hn]
  simp only [addX,TwoIsogenyPointMap.negY]
  change ((3*x^2+2*a*x+b-0*y)/(y- -y))^2+0*((3*x^2+2*a*x+b-0*y)/(y- -y))-a-x-x = _
  linear_combination (norm := (field_simp [hy]; ring)) (-(a+2*x)/y^2)*hp

set_option maxHeartbeats 0 in
theorem dual_composition_y (a b x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hp : y^2=x*(x^2+a*x+b)) :
    Y (a^2-4*b) (X a b x) (Y b x y)/8 =
      -(3*x^2+2*a*x+b)/(2*y)*((x^2-b)^2/(4*y^2)-x)-y := by
  let q := x^2+a*x+b
  let s := 3*x^2+2*a*x+b
  let d := a^2-4*b
  let c := (x^2-b)*(q^2-d*x^2)+8*x^2*q^2
  have hq : q ≠ 0 := by
    intro hz
    have he := hp
    change y^2=x*q at he
    rw [hz,mul_zero] at he
    exact hy (pow_eq_zero he)
  have he : X a b x=q/x := by dsimp [X,q]; field_simp [hx]; ring
  rw [he]
  dsimp only [Y]
  linear_combination (norm := (dsimp [q,s,d,c]; field_simp [hx,hy,hq]; ring))
    ((c*y^2-4*x^3*q^2*s+c*x*q)/(8*x^2*q^2*y^3))*hp

/-- The normalized dual composed with the degree-two map is actual elliptic doubling. -/
theorem dual_phi (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P : (E a b).Point) : dualHom a b hb hd (phi a b hb hd P)=P+P := by
  cases P with
  | zero => exact map_zero _
  | @some x y hp =>
    by_cases hx : x=0
    · subst x
      rw [phi_some_zero,map_zero]
      symm
      apply Point.add_self_of_Y_eq
      rw [TwoIsogenyPointMap.negY]
      have he := (equation ..).mp hp.1
      simp only [zero_mul] at he
      have hy := pow_eq_zero he
      rw [hy]
      ring
    · have he := (equation ..).mp hp.1
      rw [phi_some _ _ _ _ hb hd hp hx]
      by_cases hy : y=0
      · have hX : X a b x=0 := by
          have hq : x^2+a*x+b=0 := by
            rw [hy,zero_pow (by decide : 2 ≠ 0)] at he
            exact (mul_eq_zero.mp he.symm).resolve_left hx
          dsimp [X]
          linear_combination (norm := (field_simp [hx]; ring)) (1/x)*hq
        change scaleBack a b hb hd (rawDualHom a b hb hd (Point.some _)) = _
        rw [rawDual_of_x_zero a b _ _ hb hd _ hX]
        change 0 = Point.some hp+Point.some hp
        symm
        apply Point.add_self_of_Y_eq
        rw [TwoIsogenyPointMap.negY,hy]
        ring
      · have hX : X a b x ≠ 0 := by
          have hq : x^2+a*x+b ≠ 0 := by
            intro hz; rw [hz,mul_zero] at he; exact hy (pow_eq_zero he)
          have hz : X a b x=(x^2+a*x+b)/x := by dsimp [X]; field_simp [hx]; ring
          rw [hz]; exact div_ne_zero hq hx
        obtain ⟨hq,hmap⟩ := dual_some a b (X a b x) (Y b x y) hb hd _ hX
        rw [hmap]
        have hn : y ≠ (E a b).negY x y := by
          rw [TwoIsogenyPointMap.negY]; intro hz; apply hy; linarith
        rw [Point.add_self_of_Y_ne hn]
        apply some_congr
        · rw [doubling_x a b x y hy he]
          convert IsogenyCoordinates.dual_composition_x a b x y hx hy he using 1
          dsimp [X]
          ring
        · rw [addY,negAddY,TwoIsogenyPointMap.negY,doubling_x a b x y hy he,
            slope_of_Y_ne rfl hn,TwoIsogenyPointMap.negY]
          change Y (a^2-4*b) (X a b x) (Y b x y)/8 =
            -(((3*x^2+2*a*x+b-0*y)/(y- -y))*((x^2-b)^2/(4*y^2)-x)+y)
          convert dual_composition_y a b x y hx hy he using 1
          ring

theorem dual_comp_phiHom (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (dualHom a b hb hd).comp (phiHom a b hb hd)=AddMonoidHom.id _+AddMonoidHom.id _ := by
  ext P
  exact dual_phi a b hb hd P


/-- The corrected index identity now uses the two actual rational point-group maps. -/
theorem actual_doubling_index (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (phiHom a b hb hd).range.relindex
      ((phiHom a b hb hd).range ⊔ (dualHom a b hb hd).ker) *
      (AddMonoidHom.id (E a b).Point+AddMonoidHom.id (E a b).Point).range.index =
      (phiHom a b hb hd).range.index*(dualHom a b hb hd).range.index :=
  IsogenyIndexBridges.doubling_index _ _ _ (dual_comp_phiHom a b hb hd)

end PerfectPower.TwoIsogenyDual
