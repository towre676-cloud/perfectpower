import PerfectPower.RadicalCount
import Mathlib.Analysis.MeanInequalitiesPow

namespace PerfectPower

open Finset

/-! ### The radical type: the real-power asymptotic `A(N) = κ N^{1/t} + O(1)`

`radical_count_bound` counts hits through a parameter cutoff `W`.  Here `W` is identified with
`⌊((vN - u)/z₀)^{1/t}⌋` (and `0` when `vN < u`), and subadditivity of `x ↦ x^{1/t}` turns it into
`(v/z₀)^{1/t} N^{1/t} + O(1)`.  The result is the exact constant

  `κ = (R / v) · (v / z₀)^{1/t}`,  `R = #{w ∈ [1, v] : v ∣ z₀ w^t + u}`,

which is `0` when the final congruence modulo `v` has no admissible residue (`R = 0`): a solution of
the valuation congruences alone does not give infinitely many hits.  The last theorems pass to
integer `IsHit` statements over all `n ∈ [1, N]`, including a factor `G(n)^d` with `G ≠ 0`. -/

/-- The parameter cutoff. -/
noncomputable def radW (z₀ u v t N : ℕ) : ℕ :=
  ⌊(max (((v * N : ℕ) : ℝ) - u) 0 / z₀) ^ ((t : ℝ)⁻¹)⌋₊

lemma radW_spec {z₀ u v t N : ℕ} (hz₀ : 0 < z₀) (ht : 0 < t) (w : ℕ) (hw : 1 ≤ w) :
    z₀ * w ^ t + u ≤ v * N ↔ w ≤ radW z₀ u v t N := by
  set y : ℝ := max (((v * N : ℕ) : ℝ) - u) 0 / z₀
  have hz : (0 : ℝ) < z₀ := by exact_mod_cast hz₀
  have hy : 0 ≤ y := div_nonneg (le_max_right _ _) hz.le
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have key : (w : ℝ) ≤ y ^ ((t : ℝ)⁻¹) ↔ (w : ℝ) ^ (t : ℝ) ≤ y :=
    Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg w) hy htr
  rw [Real.rpow_natCast] at key
  simp only [radW]
  rw [Nat.le_floor_iff (Real.rpow_nonneg hy _), key]
  constructor
  · intro h
    have h' : ((z₀ * w ^ t + u : ℕ) : ℝ) ≤ ((v * N : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [le_div_iff₀ hz]
    have : ((v * N : ℕ) : ℝ) - u ≤ max (((v * N : ℕ) : ℝ) - u) 0 := le_max_left _ _
    push_cast at this ⊢
    nlinarith
  · intro h
    rw [le_div_iff₀ hz] at h
    have hpos : 0 < (w : ℝ) ^ t * z₀ := by positivity
    have hmax : max (((v * N : ℕ) : ℝ) - u) 0 = ((v * N : ℕ) : ℝ) - u := by
      rcases le_total (((v * N : ℕ) : ℝ) - u) 0 with h0 | h0
      · rw [max_eq_right h0] at h; linarith
      · exact max_eq_left h0
    rw [hmax] at h
    have : ((z₀ * w ^ t + u : ℕ) : ℝ) ≤ ((v * N : ℕ) : ℝ) := by push_cast at h ⊢; linarith
    exact_mod_cast this

/-- `W = (v/z₀)^{1/t} N^{1/t} + O(1)`. -/
lemma radW_approx {z₀ u v t N : ℕ} (hz₀ : 0 < z₀) (ht : 0 < t) :
    |(radW z₀ u v t N : ℝ) - ((v : ℝ) / z₀) ^ ((t : ℝ)⁻¹) * (N : ℝ) ^ ((t : ℝ)⁻¹)| ≤
      ((u : ℝ) / z₀) ^ ((t : ℝ)⁻¹) + 1 := by
  set p : ℝ := (t : ℝ)⁻¹
  have hz : (0 : ℝ) < z₀ := by exact_mod_cast hz₀
  have hp0 : 0 ≤ p := inv_nonneg.mpr (Nat.cast_nonneg t)
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast ht)
  set y : ℝ := max (((v * N : ℕ) : ℝ) - u) 0 / z₀
  set Y : ℝ := ((v * N : ℕ) : ℝ) / z₀
  have hy : 0 ≤ y := div_nonneg (le_max_right _ _) hz.le
  have hY : 0 ≤ Y := div_nonneg (Nat.cast_nonneg _) hz.le
  have hu : (0 : ℝ) ≤ u / z₀ := div_nonneg (Nat.cast_nonneg _) hz.le
  have hYeq : ((v : ℝ) / z₀) ^ p * (N : ℝ) ^ p = Y ^ p := by
    rw [← Real.mul_rpow (div_nonneg (Nat.cast_nonneg _) hz.le) (Nat.cast_nonneg _)]
    congr 1; simp only [Y]; push_cast; ring
  rw [hYeq]
  -- y ≤ Y ≤ y + u / z₀
  have hyY : y ≤ Y := by
    simp only [y, Y]
    apply div_le_div_of_nonneg_right _ hz.le
    exact max_le (by linarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u)]) (Nat.cast_nonneg _)
  have hYy : Y ≤ y + u / z₀ := by
    simp only [y, Y]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hz.le
    linarith [le_max_left (((v * N : ℕ) : ℝ) - u) 0]
  have h1 : y ^ p ≤ Y ^ p := Real.rpow_le_rpow hy hyY hp0
  have h2 : Y ^ p ≤ y ^ p + (u / z₀ : ℝ) ^ p :=
    (Real.rpow_le_rpow hY hYy hp0).trans (Real.rpow_add_le_add_rpow hy hu hp0 hp1)
  have hW1 : (radW z₀ u v t N : ℝ) ≤ y ^ p := Nat.floor_le (Real.rpow_nonneg hy _)
  have hW2 : y ^ p < (radW z₀ u v t N : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [abs_le]; constructor <;> linarith

open scoped Classical in
/-- **Radical type, exact asymptotic** (normalised form `c (v n - u)^r`, counted over `ℕ`). -/
theorem radical_asymptotic {c z₀ r d u v : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (hv : 0 < v) (h₀ : ∃ w : ℕ, c * z₀ ^ r = w ^ d)
    (hmin : ∀ p, z₀.factorization p < d / Nat.gcd r d) (N : ℕ) :
    let t := d / Nat.gcd r d
    let R := #{w ∈ Icc 1 v | v ∣ z₀ * w ^ t + u}
    let AN := #{n ∈ Icc 1 N | u < v * n ∧ ∃ w : ℕ, c * (v * n - u) ^ r = w ^ d}
    |(AN : ℝ) - (R : ℝ) / v * ((v : ℝ) / z₀) ^ ((t : ℝ)⁻¹) * (N : ℝ) ^ ((t : ℝ)⁻¹)| ≤
      2 * R + (R : ℝ) / v * (((u : ℝ) / z₀) ^ ((t : ℝ)⁻¹) + 1) := by
  intro t R AN
  have ht : 0 < t := Nat.div_pos (Nat.gcd_le_right (m := r) hd) (Nat.gcd_pos_of_pos_right r hd)
  have hz : 0 < z₀ := Nat.pos_of_ne_zero hz₀
  obtain ⟨b1, b2⟩ := radical_count_bound (u := u) (N := N) (W := radW z₀ u v t N) hd hc hz₀ hv h₀
    hmin (fun w hw => radW_spec hz ht w hw)
  have hvr : (0 : ℝ) < v := by exact_mod_cast hv
  have e1 : (v : ℝ) * AN ≤ R * radW z₀ u v t N + 2 * R * v := by exact_mod_cast b1
  have e2 : (R : ℝ) * radW z₀ u v t N ≤ v * AN + 2 * R * v := by exact_mod_cast b2
  have happ := radW_approx (u := u) (v := v) (N := N) hz ht
  set Wr : ℝ := (radW z₀ u v t N : ℝ)
  set q : ℝ := ((v : ℝ) / z₀) ^ ((t : ℝ)⁻¹) * (N : ℝ) ^ ((t : ℝ)⁻¹)
  set e : ℝ := ((u : ℝ) / z₀) ^ ((t : ℝ)⁻¹) + 1
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hRv : (0 : ℝ) ≤ R / v := div_nonneg hR0 hvr.le
  -- |AN - (R/v) W| ≤ 2R
  have eqA : ((R : ℝ) * Wr + 2 * R * v) / v = R / v * Wr + 2 * R := by
    field_simp
  have eqB : ((R : ℝ) * Wr - 2 * R * v) / v = R / v * Wr - 2 * R := by
    field_simp; ring
  have hA1 : (AN : ℝ) ≤ R / v * Wr + 2 * R := by
    rw [← eqA, le_div_iff₀ hvr]; linarith
  have hA2 : R / v * Wr - 2 * R ≤ (AN : ℝ) := by
    rw [← eqB, div_le_iff₀ hvr]; linarith
  have hq := abs_le.mp happ
  have hmul1 : R / v * (Wr - q) ≤ R / v * e := mul_le_mul_of_nonneg_left hq.2 hRv
  have hmul2 : R / v * (-e) ≤ R / v * (Wr - q) := mul_le_mul_of_nonneg_left hq.1 hRv
  rw [show (R : ℝ) / v * ((v : ℝ) / z₀) ^ ((t : ℝ)⁻¹) * (N : ℝ) ^ ((t : ℝ)⁻¹) = R / v * q by
    simp only [q]; ring]
  rw [abs_le]; constructor <;> nlinarith

/-- For a natural number, being an integer `d`-th power is being a natural `d`-th power. -/
lemma isHit_natCast_iff {d X : ℕ} : IsHit d (X : ℤ) ↔ ∃ w : ℕ, X = w ^ d := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m.natAbs, ?_⟩
    have : ((X : ℤ)).natAbs = (m ^ d).natAbs := by rw [hm]
    simpa [Int.natAbs_pow] using this
  · rintro ⟨w, rfl⟩; exact ⟨w, by push_cast; ring⟩

/-- Multiplying by a nonzero `d`-th power does not change hit status. -/
lemma isHit_mul_pow_iff {d : ℕ} (hd : d ≠ 0) {H G : ℤ} (hG : G ≠ 0) :
    IsHit d (H * G ^ d) ↔ IsHit d H := by
  constructor
  · rintro ⟨m, hm⟩
    refine (isHit_iff_rat hd H).mpr ⟨(m : ℚ) / G, ?_⟩
    have hG' : (G : ℚ) ≠ 0 := by exact_mod_cast hG
    rw [div_pow, eq_div_iff (pow_ne_zero _ hG')]
    exact_mod_cast hm
  · rintro ⟨m, rfl⟩; exact ⟨m * G, by ring⟩

open scoped Classical in
/-- **Radical type, integer form.**  For the family `F(n) = c (v n - u)^r G(n)^d`, where
`G : ℕ → ℤ` vanishes at no more than `Z` indices, the count over all `n ∈ [1, N]` satisfies
`|A(N) - κ N^{1/t}| ≤ K` with `κ = (R/v) (v/z₀)^{1/t}` and an explicit `K`. -/
theorem radical_asymptotic_int {c z₀ r d u v Z : ℕ} (hd : 0 < d) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (hv : 0 < v) (h₀ : ∃ w : ℕ, c * z₀ ^ r = w ^ d)
    (hmin : ∀ p, z₀.factorization p < d / Nat.gcd r d) (G : ℕ → ℤ)
    (hG : ∀ N, #((Icc 1 N).filter fun n => G n = 0) ≤ Z) (N : ℕ) :
    let t := d / Nat.gcd r d
    let R := #{w ∈ Icc 1 v | v ∣ z₀ * w ^ t + u}
    |(#((Icc 1 N).filter fun n : ℕ =>
          IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r * G n ^ d)) : ℝ) -
        (R : ℝ) / v * ((v : ℝ) / z₀) ^ ((t : ℝ)⁻¹) * (N : ℝ) ^ ((t : ℝ)⁻¹)| ≤
      2 * R + (R : ℝ) / v * (((u : ℝ) / z₀) ^ ((t : ℝ)⁻¹) + 1) + u + Z := by
  intro t R
  have base := radical_asymptotic (u := u) hd hc hz₀ hv h₀ hmin N
  simp only at base
  set AN := #{n ∈ Icc 1 N | u < v * n ∧ ∃ w : ℕ, c * (v * n - u) ^ r = w ^ d}
  set S := (Icc 1 N).filter fun n : ℕ => IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r * G n ^ d)
  set Sb := (Icc 1 N).filter fun n : ℕ => u < v * n ∧ ∃ w : ℕ, c * (v * n - u) ^ r = w ^ d
  -- outside the zeros of G and the finitely many n with v n ≤ u, the two conditions agree
  have hagree : ∀ n ∈ Icc 1 N, G n ≠ 0 → u < v * n →
      (IsHit d ((c : ℤ) * ((v : ℤ) * n - u) ^ r * G n ^ d) ↔
        ∃ w : ℕ, c * (v * n - u) ^ r = w ^ d) := by
    intro n _ hGn hun
    rw [isHit_mul_pow_iff hd.ne' hGn, ← isHit_natCast_iff]
    have : ((v : ℤ) * n - u) = ((v * n - u : ℕ) : ℤ) := by push_cast [Nat.cast_sub hun.le]; ring
    rw [this]; push_cast; rfl
  set Bad := ((Icc 1 N).filter fun n => G n = 0) ∪ ((Icc 1 N).filter fun n => v * n ≤ u)
  have hBad : #Bad ≤ Z + u := by
    refine (card_union_le _ _).trans (Nat.add_le_add (hG N) ?_)
    calc #((Icc 1 N).filter fun n => v * n ≤ u) ≤ #(Icc 1 u) := by
          apply card_le_card
          intro n hn
          simp only [mem_filter, mem_Icc] at hn ⊢
          exact ⟨hn.1.1, by nlinarith [hn.2]⟩
      _ = u := by simp
  have hS : S ⊆ Sb ∪ Bad := by
    intro n hn
    simp only [S, mem_filter] at hn
    by_cases hG0 : G n = 0
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hn.1, hG0⟩))
    by_cases hun : u < v * n
    · exact mem_union_left _ (mem_filter.mpr ⟨hn.1, hun, (hagree n hn.1 hG0 hun).mp hn.2⟩)
    · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hn.1, by omega⟩))
  have hSb : Sb ⊆ S ∪ Bad := by
    intro n hn
    simp only [Sb, mem_filter] at hn
    by_cases hG0 : G n = 0
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hn.1, hG0⟩))
    · exact mem_union_left _ (mem_filter.mpr ⟨hn.1, (hagree n hn.1 hG0 hn.2.1).mpr hn.2.2⟩)
  have c1 : #S ≤ #Sb + (Z + u) := (card_le_card hS).trans ((card_union_le _ _).trans (by omega))
  have c2 : #Sb ≤ #S + (Z + u) := (card_le_card hSb).trans ((card_union_le _ _).trans (by omega))
  have r1 : (#S : ℝ) ≤ #Sb + (Z + u) := by exact_mod_cast c1
  have r2 : (#Sb : ℝ) ≤ #S + (Z + u) := by exact_mod_cast c2
  have hAN : AN = #Sb := rfl
  rw [hAN] at base
  rw [abs_le] at base ⊢
  constructor <;> linarith [base.1, base.2]

end PerfectPower
