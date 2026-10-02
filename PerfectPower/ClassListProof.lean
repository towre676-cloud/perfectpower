import PerfectPower.CubicReduction
import PerfectPower.MordellCubicForm
import PerfectPower.ReducibleThue

/-!
# Proving the class-list premise `MordellCubicForm.ClassList k Gs`

Every form `F = (a, 3b, 3c, d)` with `Δ = 4k` (`k > 0`) has discriminant `−108k < 0`.
* `lead_ne`: some `F ∘ T` has nonzero leading coefficient (swap `X, Y` if `a = 0`).
* `CubicReduction.reduce_box` and `CubicReduction.int_bounds`: some `F ∘ T` has `a' = 0` or lies in
  an explicit box (bounds checked per `k` by `norm_num`).
* `shift_zero`: a form with `a' = 0` has `c'` moved into `(−|b'|, |b'|]` by `X ↦ X + tY`.
* `boxCertB`: every form of the box with `Δ = 4k` (the last coefficient solved from `Δ`,
  `ReducibleThue.mem_tCands`) is `G ∘ T` for a listed `G`, by an explicit matrix.
These give `ClassList k Gs` with no premise (`classList_of`).
-/

namespace PerfectPower.ClassListProof

open PerfectPower MordellCubicForm CubicReduction ReducibleThue

/-- `act` composes: `(F ∘ T) ∘ S = F ∘ (T S)`. -/
theorem act_comp (F : ℤ × ℤ × ℤ × ℤ) (p q r s p' q' r' s' : ℤ) :
    act (act F p q r s) p' q' r' s' =
      act F (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') := by
  obtain ⟨a, b, c, d⟩ := F
  simp only [act, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem act_one (F : ℤ × ℤ × ℤ × ℤ) : act F 1 0 0 1 = F := by
  obtain ⟨a, b, c, d⟩ := F
  simp [act]

/-- Equivalence: `F = G ∘ T` for some `T` with `det T = ±1`. -/
def Equiv (G F : ℤ × ℤ × ℤ × ℤ) : Prop :=
  ∃ p q r s : ℤ, (p * s - q * r) ^ 2 = 1 ∧ act G p q r s = F

theorem equiv_trans {F G H : ℤ × ℤ × ℤ × ℤ} (h1 : Equiv F G) (h2 : Equiv G H) : Equiv F H := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := h1
  obtain ⟨p', q', r', s', hd', rfl⟩ := h2
  refine ⟨p * p' + q * r', p * q' + q * s', r * p' + s * r', r * q' + s * s', ?_,
    (act_comp F p q r s p' q' r' s').symm⟩
  have : ((p * p' + q * r') * (r * q' + s * s') - (p * q' + q * s') * (r * p' + s * r')) =
      (p * s - q * r) * (p' * s' - q' * r') := by ring
  rw [this, mul_pow, hd, hd', one_mul]

theorem equiv_symm {F G : ℤ × ℤ × ℤ × ℤ} (h : Equiv F G) : Equiv G F := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := h
  set e := p * s - q * r
  refine ⟨e * s, -(e * q), -(e * r), e * p, ?_, ?_⟩
  · have : e * s * (e * p) - -(e * q) * -(e * r) = e ^ 2 * e := by simp only [e]; ring
    rw [this, hd, one_mul]; exact hd
  · rw [act_comp]
    have h1 : p * (e * s) + q * -(e * r) = e * e := by simp only [e]; ring
    have h2 : p * -(e * q) + q * (e * p) = 0 := by ring
    have h3 : r * (e * s) + s * -(e * r) = 0 := by ring
    have h4 : r * -(e * q) + s * (e * p) = e * e := by simp only [e]; ring
    have he : e * e = 1 := by rw [← sq]; exact hd
    rw [h1, h2, h3, h4, he, act_one]

theorem equiv_refl (F : ℤ × ℤ × ℤ × ℤ) : Equiv F F := ⟨1, 0, 0, 1, by norm_num, act_one F⟩

/-- The discriminant of `(a, 3b, 3c, d)` is `−27 Δ`. -/
theorem disc4_eq (a b c d : ℤ) :
    disc4 (a : ℝ) (3 * b : ℤ) (3 * c : ℤ) (d : ℝ) = -27 * (delta (a, b, c, d) : ℝ) := by
  simp only [disc4, delta]; push_cast; ring

theorem ev4_eq (F : ℤ × ℤ × ℤ × ℤ) (x y : ℤ) :
    ev4 (F.1 : ℝ) ((3 * F.2.1 : ℤ) : ℝ) ((3 * F.2.2.1 : ℤ) : ℝ) (F.2.2.2 : ℝ) x y = (ev F x y : ℝ) := by
  obtain ⟨a, b, c, d⟩ := F
  simp only [ev4, ev]; push_cast; ring

/-- A nonzero leading coefficient, after swapping `X` and `Y` if needed. -/
theorem lead_ne {k : ℤ} (hk : 0 < k) (F : ℤ × ℤ × ℤ × ℤ) (hF : delta F = 4 * k) :
    ∃ G, Equiv F G ∧ delta G = 4 * k ∧ G.1 ≠ 0 := by
  obtain ⟨a, b, c, d⟩ := F
  by_cases ha : a = 0
  · subst ha
    have hd : d ≠ 0 := by
      rintro rfl
      simp only [delta] at hF
      nlinarith [sq_nonneg (b * c)]
    refine ⟨act (0, b, c, d) 0 1 1 0, ⟨0, 1, 1, 0, by norm_num, rfl⟩, ?_, ?_⟩
    · rw [delta_act]; simpa using hF
    · simp [act, hd]
  · exact ⟨(a, b, c, d), equiv_refl _, hF, ha⟩

/-- Numeric parameters for `CubicReduction.int_bounds` at `|D| = 108k`, checked per `k`. -/
structure Params where
  s0 : ℚ
  s1 : ℚ
  H : ℚ
  M : ℚ
  amax : ℚ

/-- The side conditions of `int_bounds`, as rational inequalities (decidable, `norm_num`). -/
def ParamsOK (k : ℤ) (P : Params) : Prop :=
  0 < P.s0 ∧ ((108 * k : ℤ) : ℚ) ^ 2 * P.s0 ^ 3 ≤ 27 ∧ 4 ≤ ((108 * k : ℤ) : ℚ) * P.s1 ^ 2 ∧ P.s0 ≤ P.s1 ∧
  9 * P.s0 ^ 2 * ((108 * k : ℤ) : ℚ) + 12 ≤ 4 * P.H * P.s0 * ((108 * k : ℤ) : ℚ) ∧
  9 * P.s1 ^ 2 * ((108 * k : ℤ) : ℚ) + 12 ≤ 4 * P.H * P.s1 * ((108 * k : ℤ) : ℚ) ∧
  ((108 * k : ℤ) : ℚ) ^ 2 * P.H ^ 3 ≤ 27 * P.M ^ 2 ∧ ((108 * k : ℤ) : ℚ) ^ 2 * P.s1 ^ 3 ≤ 27 * P.amax ^ 2 ∧
  0 ≤ P.M ∧ 0 ≤ P.amax

theorem ev_act10 (G : ℤ × ℤ × ℤ × ℤ) : ev G 1 0 = G.1 := by simp [ev]
theorem ev_act01 (G : ℤ × ℤ × ℤ × ℤ) : ev G 0 1 = G.2.2.2 := by simp [ev]
theorem ev_act11 (G : ℤ × ℤ × ℤ × ℤ) : ev G 1 1 = G.1 + 3 * G.2.1 + 3 * G.2.2.1 + G.2.2.2 := by
  simp [ev]
theorem ev_act1m (G : ℤ × ℤ × ℤ × ℤ) : ev G 1 (-1) = G.1 - 3 * G.2.1 + 3 * G.2.2.1 - G.2.2.2 := by
  simp [ev]; ring

/-- **The reduction step for forms**: some equivalent form has `a' = 0` or lies in the box
`|a'| ≤ amax`, `|d'|, |a' ± 3b' + 3c' ± d'| ≤ M`. -/
theorem reduce_int {k : ℤ} (hk : 0 < k) {P : Params} (hP : ParamsOK k P) (F : ℤ × ℤ × ℤ × ℤ)
    (hF : delta F = 4 * k) (ha : F.1 ≠ 0) :
    ∃ G, Equiv F G ∧ delta G = 4 * k ∧ (G.1 = 0 ∨ (|(G.1 : ℝ)| ≤ (P.amax : ℝ) ∧ |(G.2.2.2 : ℝ)| ≤ (P.M : ℝ) ∧
      |((G.1 + 3 * G.2.1 + 3 * G.2.2.1 + G.2.2.2 : ℤ) : ℝ)| ≤ (P.M : ℝ) ∧
      |((G.1 - 3 * G.2.1 + 3 * G.2.2.1 - G.2.2.2 : ℤ) : ℝ)| ≤ (P.M : ℝ))) := by
  obtain ⟨a, b, c, d⟩ := F
  simp only at ha
  have hD : disc4 (a : ℝ) ((3 * b : ℤ) : ℝ) ((3 * c : ℤ) : ℝ) (d : ℝ) = -(108 * k : ℝ) := by
    rw [disc4_eq, hF]; push_cast; ring
  have hDneg : disc4 (a : ℝ) ((3 * b : ℤ) : ℝ) ((3 * c : ℤ) : ℝ) (d : ℝ) < 0 := by
    rw [hD]; have : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  obtain ⟨x1, y1, x2, y2, hdet, sv, bv, cv, hs, hb, hsc, hdetq, h1, h2, h3, h4⟩ :=
    reduce_box (by exact_mod_cast ha) hDneg
  set G := act (a, b, c, d) x1 x2 y1 y2
  have hEq : Equiv (a, b, c, d) G := ⟨x1, x2, y1, y2, by rw [hdet]; norm_num, rfl⟩
  have hdG : delta G = 4 * k := by
    simp only [G]; rw [delta_act, hF, show x1 * y2 - x2 * y1 = 1 from hdet]; ring
  refine ⟨G, hEq, hdG, ?_⟩
  have hDabs : |disc4 (a : ℝ) ((3 * b : ℤ) : ℝ) ((3 * c : ℤ) : ℝ) (d : ℝ)| = ((108 * k : ℤ) : ℝ) := by
    rw [hD]; push_cast; rw [abs_neg, abs_of_pos (by positivity)]
  have hsq : disc4 (a : ℝ) ((3 * b : ℤ) : ℝ) ((3 * c : ℤ) : ℝ) (d : ℝ) ^ 2 = ((108 * k : ℤ) : ℝ) ^ 2 := by
    rw [← hDabs, sq_abs]
  have e1 : ev G 1 0 = ev (a, b, c, d) x1 y1 := by simp only [G]; rw [ev_act]; ring_nf
  have e2 : ev G 0 1 = ev (a, b, c, d) x2 y2 := by simp only [G]; rw [ev_act]; ring_nf
  have e3 : ev G 1 1 = ev (a, b, c, d) (x1 + x2) (y1 + y2) := by simp only [G]; rw [ev_act]; ring_nf
  have e4 : ev G 1 (-1) = ev (a, b, c, d) (x1 - x2) (y1 - y2) := by simp only [G]; rw [ev_act]; ring_nf
  have c1 := ev4_eq (a, b, c, d) x1 y1
  have c2 := ev4_eq (a, b, c, d) x2 y2
  have c3 : ev4 (a : ℝ) ((3 * b : ℤ) : ℝ) ((3 * c : ℤ) : ℝ) (d : ℝ) ((x1 : ℝ) + x2) ((y1 : ℝ) + y2) =
      (ev (a, b, c, d) (x1 + x2) (y1 + y2) : ℝ) := by
    have := ev4_eq (a, b, c, d) (x1 + x2) (y1 + y2); push_cast at this ⊢; exact this
  have c4 : ev4 (a : ℝ) ((3 * b : ℤ) : ℝ) ((3 * c : ℤ) : ℝ) (d : ℝ) ((x1 : ℝ) - x2) ((y1 : ℝ) - y2) =
      (ev (a, b, c, d) (x1 - x2) (y1 - y2) : ℝ) := by
    have := ev4_eq (a, b, c, d) (x1 - x2) (y1 - y2); push_cast at this ⊢; exact this
  simp only at c1 c2
  rw [c1, hsq] at h1; rw [c2, hsq] at h2; rw [c3, hsq] at h3; rw [c4, hsq] at h4
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hP
  have r := int_bounds (Dabs := ((108 * k : ℤ) : ℝ)) (s0 := (P.s0 : ℝ)) (s1 := (P.s1 : ℝ)) (H := (P.H : ℝ))
    (M := (P.M : ℝ)) (amax := (P.amax : ℝ)) (X1 := ev (a, b, c, d) x1 y1) (X2 := ev (a, b, c, d) x2 y2)
    (X3 := ev (a, b, c, d) (x1 + x2) (y1 + y2)) (X4 := ev (a, b, c, d) (x1 - x2) (y1 - y2))
    (by push_cast; positivity) hs hb hsc (by rw [← hDabs]; exact hdetq)
    (by exact_mod_cast h1) (by exact_mod_cast h2) (by exact_mod_cast h3) (by exact_mod_cast h4)
    (by exact_mod_cast p0) (by exact_mod_cast p1) (by exact_mod_cast p2) (by exact_mod_cast p3)
    (by exact_mod_cast p4) (by exact_mod_cast p5) (by exact_mod_cast p6) (by exact_mod_cast p7)
    (by exact_mod_cast p8) (by exact_mod_cast p9)
  rw [← e1, ← e2, ← e3, ← e4, ev_act10, ev_act01, ev_act11, ev_act1m] at r
  rcases r with r | r
  · exact Or.inl r
  · exact Or.inr r

end PerfectPower.ClassListProof
