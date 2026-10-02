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

theorem delta_zero (b c d : ℤ) : delta (0, b, c, d) = b ^ 2 * (4 * b * d - 3 * c ^ 2) := by
  simp only [delta]; ring

/-- **A form with a rational root** (`a = 0`) is equivalent to one with `a = 0`, `b² ≤ 4k` and
`|c| ≤ |b|` (`X ↦ X + tY` moves `c` by `2bt`). -/
theorem shift_zero {k : ℤ} (hk : 0 < k) (G : ℤ × ℤ × ℤ × ℤ) (hG : delta G = 4 * k) (ha : G.1 = 0) :
    ∃ G', Equiv G G' ∧ delta G' = 4 * k ∧ G'.1 = 0 ∧ G'.2.1 ^ 2 ≤ 4 * k ∧ |G'.2.2.1| ≤ |G'.2.1| := by
  obtain ⟨a, b, c, d⟩ := G
  simp only at ha; subst ha
  rw [delta_zero] at hG
  have hb : b ≠ 0 := by rintro rfl; simp at hG; omega
  have hb2 : b ^ 2 ≤ 4 * k := by
    have hpos : 0 < b ^ 2 := by positivity
    have hq : 0 < 4 * b * d - 3 * c ^ 2 := by
      by_contra hc; push_neg at hc
      have : b ^ 2 * (4 * b * d - 3 * c ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos.le hc
      omega
    nlinarith
  set B := |b| with hB
  have hBpos : 0 < B := abs_pos.mpr hb
  set m := 2 * B
  have hm : 0 < m := by omega
  set q := (c + B - 1) / m
  set r := (c + B - 1) % m
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hm.ne'
  have hr1 : r < m := Int.emod_lt_of_pos _ hm
  have hqr : c + B - 1 = m * q + r := (Int.ediv_add_emod _ _).symm
  -- t with 2 b t = −m q
  obtain ⟨t, ht⟩ : ∃ t, 2 * b * t = -(m * q) := by
    rcases lt_or_gt_of_ne hb with hneg | hpos
    · refine ⟨q, ?_⟩; simp only [m, hB, abs_of_neg hneg]; ring
    · refine ⟨-q, ?_⟩; simp only [m, hB, abs_of_pos hpos]; ring
  refine ⟨act (0, b, c, d) 1 t 0 1, ⟨1, t, 0, 1, by norm_num, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [delta_act, delta_zero, hG]; ring
  · simp [act]
  · simp [act]; exact hb2
  · simp only [act]
    have hc' : 0 * 1 * t ^ 2 + b * (2 * 1 * t * 1 + t ^ 2 * 0) + c * (1 * 1 ^ 2 + 2 * t * 0 * 1) + d * 0 * 1 ^ 2 =
        c + 2 * b * t := by ring
    have hb' : 0 * 1 ^ 2 * t + b * (1 ^ 2 * 1 + 2 * 1 * t * 0) + c * (t * 0 ^ 2 + 2 * 1 * 0 * 1) + d * 0 ^ 2 * 1 = b := by
      ring
    rw [hc', hb', ht, ← hB, abs_le]
    constructor <;> omega

/-- `Δ(a, b, c, d) − 4k` as a quadratic in `d`. -/
def dQuad (k a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a ^ 2, -2 * a * b * c - 4 * b * (a * c - b ^ 2), b ^ 2 * c ^ 2 + 4 * c ^ 2 * (a * c - b ^ 2) - 4 * k)

theorem dQuad_eq (k a b c d : ℤ) :
    delta (a, b, c, d) - 4 * k = (dQuad k a b c).1 * d ^ 2 + (dQuad k a b c).2.1 * d + (dQuad k a b c).2.2 := by
  simp only [delta, dQuad]; ring

/-- A transport certificate: the form, a listed class, and `(p, q, r, s)` with `act G p q r s = F`. -/
abbrev Cert := (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) × ℤ × ℤ × ℤ × ℤ

def certOK (Gs : List (ℤ × ℤ × ℤ × ℤ)) (F : ℤ × ℤ × ℤ × ℤ) (e : Cert) : Bool :=
  decide (e.1 = F) && decide (e.2.1 ∈ Gs) &&
  decide ((e.2.2.1 * e.2.2.2.2.2 - e.2.2.2.1 * e.2.2.2.2.1) ^ 2 = 1) &&
  decide (act e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2 = F)

/-- **The box check**: every `(a, b, c, d)` with `|a| ≤ amax`, `|b|, |c| ≤ bmax` and `Δ = 4k` has a
certificate (`d` runs over the integer roots of `Δ = 4k`, `ReducibleThue.tCands`). -/
def boxCertB (k amax bmax : ℤ) (Gs : List (ℤ × ℤ × ℤ × ℤ)) (certs : List Cert) : Bool :=
  (List.range (2 * amax + 1).toNat).all fun i => (List.range (2 * bmax + 1).toNat).all fun j =>
    (List.range (2 * bmax + 1).toNat).all fun l =>
      let a : ℤ := i - amax
      let b : ℤ := j - bmax
      let c : ℤ := l - bmax
      let Qd := dQuad k a b c
      (decide (Qd.1 ≠ 0 ∨ Qd.2.1 ≠ 0) || decide (Qd.2.2 ≠ 0)) &&
      (tCands Qd.1 Qd.2.1 Qd.2.2).all fun d =>
        decide (delta (a, b, c, d) ≠ 4 * k) || certs.any (certOK Gs (a, b, c, d))

theorem box_sound {k amax bmax : ℤ} {Gs : List (ℤ × ℤ × ℤ × ℤ)} {certs : List Cert}
    (h : boxCertB k amax bmax Gs certs = true) (F : ℤ × ℤ × ℤ × ℤ) (hF : delta F = 4 * k)
    (ha : |F.1| ≤ amax) (hb : |F.2.1| ≤ bmax) (hc : |F.2.2.1| ≤ bmax) : ∃ G ∈ Gs, Equiv G F := by
  obtain ⟨a, b, c, d⟩ := F
  simp only at ha hb hc
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  simp only [boxCertB, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  have hh := h (a + amax).toNat (by omega) (b + bmax).toNat (by omega) (c + bmax).toNat (by omega)
  have e1 : ((a + amax).toNat : ℤ) - amax = a := by omega
  have e2 : ((b + bmax).toNat : ℤ) - bmax = b := by omega
  have e3 : ((c + bmax).toNat : ℤ) - bmax = c := by omega
  simp only [e1, e2, e3] at hh
  obtain ⟨hnd, hall⟩ := hh
  have hq := dQuad_eq k a b c d
  rw [hF, sub_self] at hq
  have hne : (dQuad k a b c).1 ≠ 0 ∨ (dQuad k a b c).2.1 ≠ 0 := by
    rcases hnd with h1 | h1
    · exact h1
    · by_contra hc0
      rw [not_or, not_not, not_not] at hc0
      rw [hc0.1, hc0.2] at hq
      exact h1 (by linarith)
  have hd := mem_tCands (t := d) (γ := (dQuad k a b c).2.2) hne (by linarith)
  rcases hall d hd with h1 | h1
  · exact absurd hF h1
  · obtain ⟨e, -, he⟩ := List.any_eq_true.mp h1
    simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨⟨he1, he2⟩, he3⟩, he4⟩ := he
    exact ⟨e.2.1, he2, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1, e.2.2.2.2.2, he3, he4.trans rfl⟩

/-- **`ClassList k Gs`, proved**: from checked parameters and a checked box certificate. -/
theorem classList_of {k amax bmax : ℤ} (hk : 0 < k) {P : Params} (hP : ParamsOK k P)
    (hA : (P.amax : ℚ) ≤ amax) (hB1 : P.M + P.amax ≤ 3 * bmax) (hB2 : 2 * P.M ≤ 3 * bmax)
    (hB3 : 4 * k ≤ bmax ^ 2) (hB0 : 0 ≤ bmax) {Gs : List (ℤ × ℤ × ℤ × ℤ)} {certs : List Cert}
    (hbox : boxCertB k amax bmax Gs certs = true) : ClassList k Gs := by
  intro F hF
  have hamax0 : (0 : ℚ) ≤ amax := le_trans hP.2.2.2.2.2.2.2.2.2 hA
  have hamax0' : 0 ≤ amax := by exact_mod_cast hamax0
  obtain ⟨G1, hFG1, hd1, ha1⟩ := lead_ne hk F hF
  obtain ⟨G2, hG12, hd2, hcase⟩ := reduce_int hk hP G1 hd1 ha1
  have hFG2 := equiv_trans hFG1 hG12
  suffices hfin : ∃ G ∈ Gs, Equiv G G2 by
    obtain ⟨G, hG, hGG2⟩ := hfin
    exact ⟨G, hG, equiv_trans hGG2 (equiv_symm hFG2)⟩
  rcases hcase with h0 | ⟨r1, r2, r3, r4⟩
  · obtain ⟨G3, hG23, hd3, ha3, hb3, hc3⟩ := shift_zero hk G2 hd2 h0
    obtain ⟨G, hG, hGG3⟩ := box_sound hbox G3 hd3 (by rw [ha3]; simp; omega) (by
      rw [abs_le]; constructor <;> nlinarith [sq_abs G3.2.1, abs_nonneg G3.2.1]) (by
      have : |G3.2.1| ≤ bmax := by
        rw [abs_le]; constructor <;> nlinarith [sq_abs G3.2.1, abs_nonneg G3.2.1]
      linarith)
    exact ⟨G, hG, equiv_trans hGG3 (equiv_symm hG23)⟩
  · obtain ⟨a, b, c, d⟩ := G2
    simp only at r1 r2 r3 r4
    have hA' : (P.amax : ℝ) ≤ amax := by exact_mod_cast hA
    have hB1' : (P.M : ℝ) + P.amax ≤ 3 * bmax := by exact_mod_cast hB1
    have hB2' : 2 * (P.M : ℝ) ≤ 3 * bmax := by exact_mod_cast hB2
    rw [abs_le] at r1 r2 r3 r4
    push_cast at r3 r4
    have ia : |a| ≤ amax := by
      rw [abs_le]; constructor
      · have : (-(amax : ℝ)) ≤ a := by linarith
        exact_mod_cast this
      · have : (a : ℝ) ≤ amax := by linarith
        exact_mod_cast this
    have ib : |b| ≤ bmax := by
      rw [abs_le]; constructor
      · have : (-(bmax : ℝ)) ≤ b := by linarith
        exact_mod_cast this
      · have : (b : ℝ) ≤ bmax := by linarith
        exact_mod_cast this
    have ic : |c| ≤ bmax := by
      rw [abs_le]; constructor
      · have : (-(bmax : ℝ)) ≤ c := by linarith
        exact_mod_cast this
      · have : (c : ℝ) ≤ bmax := by linarith
        exact_mod_cast this
    exact box_sound hbox (a, b, c, d) hd2 ia ib ic

end PerfectPower.ClassListProof
