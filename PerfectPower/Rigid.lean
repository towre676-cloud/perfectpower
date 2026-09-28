import PerfectPower.Density

open Polynomial Filter Topology
open scoped Classical

namespace PerfectPower

/-- Rigid case: `d ∣ deg F` and the leading coefficient is an integer `d`-th power. -/
def IsRigid (d : ℕ) (F : ℤ[X]) : Prop :=
  d ∣ F.natDegree ∧ ∃ b : ℤ, F.leadingCoeff = b ^ d

/-- The value-one case: `F = G^d` over `ℤ`; every index is a hit. -/
theorem hit_of_pow_eq {d : ℕ} {F G : ℤ[X]} (h : F = G ^ d) (n : ℕ) :
    IsHit d (F.eval (n : ℤ)) := ⟨G.eval (n : ℤ), by rw [h, eval_pow]⟩

/-! ### Denominators -/

/-- Clear denominators. `D` is an arbitrary nonzero integer (sign is irrelevant downstream). -/
theorem exists_denominator (Q : ℚ[X]) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ P : ℤ[X], C (D : ℚ) * Q = P.map (Int.castRingHom ℚ) := by
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) Q
  refine ⟨(b : ℤ), nonZeroDivisors.coe_ne_zero b,
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q, ?_⟩
  rw [algebraMap_int_eq] at hb
  rw [Polynomial.C_eq_intCast, ← zsmul_eq_mul, ← hb]

/-- Finitely many fractional parts of `Q(n)` (optional; the finite-hit argument below only needs
`exists_denominator`, since `Q(n) ∈ (1/D)ℤ` for every integer `n`). -/
theorem frac_periodic (Q : ℚ[X]) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ n n' : ℤ, n ≡ n' [ZMOD D] → ∃ z : ℤ, Q.eval (n : ℚ) - Q.eval (n' : ℚ) = z := by
  obtain ⟨D, hD, P, hP⟩ := exists_denominator Q
  refine ⟨D, hD, fun n n' h => ?_⟩
  have h1 : D ∣ n - n' := Int.modEq_iff_dvd.mp h.symm
  have h2 : D ∣ P.eval n - P.eval n' := h1.trans (Polynomial.sub_dvd_eval_sub n n' P)
  have hev : ∀ x : ℤ, (D : ℚ) * Q.eval (x : ℚ) = ((P.eval x : ℤ) : ℚ) := by
    intro x
    have := congrArg (Polynomial.eval (x : ℚ)) hP
    simpa [Polynomial.eval_intCast_map] using this
  obtain ⟨z, hz⟩ := h2
  refine ⟨z, ?_⟩
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  apply mul_left_cancel₀ hDq
  rw [mul_sub, hev n, hev n']
  exact_mod_cast hz

/-- `Q^d = F` in `ℚ[X]` with `F ∈ ℤ[X]` forces `Q ∈ ℤ[X]`. Proof by Gauss content:
`D Q = P ∈ ℤ[X]` gives `P^d = D^d F`, so `D^d ∣ content(P)^d`, hence `D ∣ content(P)`,
hence `P = D G` and `Q = G`. -/
theorem integral_closure_step {d : ℕ} (hd : 2 ≤ d) (F : ℤ[X]) (Q : ℚ[X])
    (h : Q ^ d = F.map (Int.castRingHom ℚ)) :
    ∃ G : ℤ[X], G.map (Int.castRingHom ℚ) = Q := by
  obtain ⟨D, hD, P, hP⟩ := exists_denominator Q
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have h1 : (P ^ d).map (Int.castRingHom ℚ) = (C (D ^ d) * F).map (Int.castRingHom ℚ) := by
    rw [Polynomial.map_pow, ← hP, mul_pow, ← C_pow, h, Polynomial.map_mul, Polynomial.map_C]
    simp
  have h2 : P ^ d = C (D ^ d) * F := Polynomial.map_injective _ hinj h1
  have h3 : D ^ d ∣ (P ^ d).content := dvd_content_iff_C_dvd.mpr ⟨F, h2⟩
  have h4 : ∀ n : ℕ, (P ^ n).content = P.content ^ n := by
    intro n
    induction n with
    | zero => simp [Polynomial.content_one]
    | succ n ih => rw [pow_succ, content_mul, ih, pow_succ]
  have h5 : D ∣ P.content := by
    rw [h4] at h3
    exact (Int.pow_dvd_pow_iff (by omega)).mp h3
  obtain ⟨G, hG⟩ := dvd_content_iff_C_dvd.mp h5
  refine ⟨G, ?_⟩
  have hCD : (C (D : ℚ)) ≠ 0 := Polynomial.C_ne_zero.mpr (by exact_mod_cast hD)
  have h6 : C (D : ℚ) * G.map (Int.castRingHom ℚ) = C (D : ℚ) * Q := by
    rw [hP, hG, Polynomial.map_mul, Polynomial.map_C]; simp
  exact mul_left_cancel₀ hCD h6

/-! ### Algebraic truncated `d`-th root -/

lemma degree_lt_of_coeff_zero {p : ℚ[X]} {N : ℕ} (h1 : p.degree ≤ N) (h2 : p.coeff N = 0) :
    p.degree < N := by
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exact absurd h2 (coeff_ne_zero_of_eq_degree h)

lemma degree_le_of_lt_succ {p : ℚ[X]} {n : ℕ} (h : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    p.degree ≤ n := by
  by_cases hp : p = 0
  · simp [hp]
  · have := (natDegree_lt_iff_degree_lt hp).mpr h
    exact degree_le_of_natDegree_le (by omega)

/-- Second-order binomial remainder: `(Q+T)^(e+2) = Q^(e+2) + (e+2) T Q^(e+1) + E`,
with `deg E ≤ 2 deg T + e deg Q` when `deg T ≤ deg Q`. -/
lemma binom_remainder (Q T : ℚ[X]) (e : ℕ) (hT : T.natDegree ≤ Q.natDegree) :
    ∃ E : ℚ[X], (Q + T) ^ (e + 2) = Q ^ (e + 2) + ((e + 2 : ℕ) : ℚ[X]) * T * Q ^ (e + 1) + E ∧
      E.natDegree ≤ 2 * T.natDegree + e * Q.natDegree := by
  rw [add_comm Q T, add_pow]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  refine ⟨∑ i ∈ Finset.range (e + 1),
      T ^ (i + 1 + 1) * Q ^ (e + 2 - (i + 1 + 1)) * (((e + 2).choose (i + 1 + 1) : ℕ) : ℚ[X]), ?_, ?_⟩
  · simp
    ring
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    have hi' : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : (T ^ (i + 1 + 1)).natDegree ≤ (i + 1 + 1) * T.natDegree := natDegree_pow_le
    have h2 : (Q ^ (e + 2 - (i + 1 + 1))).natDegree ≤ (e + 2 - (i + 1 + 1)) * Q.natDegree :=
      natDegree_pow_le
    have h3 : ((((e + 2).choose (i + 1 + 1) : ℕ)) : ℚ[X]).natDegree = 0 := natDegree_natCast _
    calc _ ≤ (T ^ (i + 1 + 1) * Q ^ (e + 2 - (i + 1 + 1))).natDegree
              + ((((e + 2).choose (i + 1 + 1) : ℕ)) : ℚ[X]).natDegree := natDegree_mul_le
      _ ≤ ((T ^ (i + 1 + 1)).natDegree + (Q ^ (e + 2 - (i + 1 + 1))).natDegree) + 0 := by
          rw [h3]; exact Nat.add_le_add_right natDegree_mul_le 0
      _ ≤ (i + 1 + 1) * T.natDegree + (e - i) * Q.natDegree := by
          have : e + 2 - (i + 1 + 1) = e - i := by omega
          rw [this] at h2 ⊢; omega
      _ ≤ 2 * T.natDegree + e * Q.natDegree := by
          obtain ⟨s, rfl⟩ : ∃ s, e = i + s := ⟨e - i, by omega⟩
          have : i + s - i = s := by omega
          rw [this]
          nlinarith [Nat.mul_le_mul_left i hT]

/-- Core induction: match the top `j+1` coefficients of `F` against `Q^d`, `Q` of degree `q`. -/
lemma trunc_induction {q e : ℕ} (b : ℚ) (hb : b ≠ 0) (F : ℚ[X])
    (hFd : F.natDegree = q * (e + 2)) (hlead : F.leadingCoeff = b ^ (e + 2)) :
    ∀ j, j ≤ q → ∃ Q : ℚ[X], Q.natDegree = q ∧ Q.leadingCoeff = b ∧
      (F - Q ^ (e + 2)).degree < ((q * (e + 2) - j : ℕ) : WithBot ℕ) := by
  have hF0 : F ≠ 0 := by
    intro h
    rw [h, leadingCoeff_zero] at hlead
    exact hb ((pow_eq_zero_iff (by omega)).mp hlead.symm)
  have hqd : q * (e + 2) = (e + 1) * q + q := by ring
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨C b * X ^ q, natDegree_C_mul_X_pow q b hb, leadingCoeff_C_mul_X_pow b q, ?_⟩
    have hpow : (C b * X ^ q) ^ (e + 2) = C (b ^ (e + 2)) * X ^ (q * (e + 2)) := by
      rw [mul_pow, ← C_pow, ← pow_mul]
    have hdeg : (C (b ^ (e + 2)) * X ^ (q * (e + 2))).degree = ((q * (e + 2) : ℕ) : WithBot ℕ) :=
      degree_C_mul_X_pow (q * (e + 2)) (pow_ne_zero _ hb)
    have hFdeg : F.degree = ((q * (e + 2) : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree hF0, hFd]
    rw [Nat.sub_zero, hpow]
    have := degree_sub_lt (p := F) (q := C (b ^ (e + 2)) * X ^ (q * (e + 2)))
      (by rw [hFdeg, hdeg]) hF0 (by rw [hlead, leadingCoeff_C_mul_X_pow])
    rwa [hFdeg] at this
  | succ j ih =>
    intro hj
    obtain ⟨Q, hQd, hQl, hQR⟩ := ih (by omega)
    have hQ0 : Q ≠ 0 := by
      intro h; rw [h, leadingCoeff_zero] at hQl; exact hb hQl.symm
    obtain ⟨k, hk⟩ : ∃ k, k = q - j - 1 := ⟨_, rfl⟩
    obtain ⟨N1, hN1⟩ : ∃ N1, N1 = q * (e + 2) - j - 1 := ⟨_, rfl⟩
    have hkq : k < q := by omega
    have hN1eq : N1 = (e + 1) * q + k := by omega
    let R : ℚ[X] := F - Q ^ (e + 2)
    let c : ℚ := R.coeff N1 / (((e + 2 : ℕ) : ℚ) * b ^ (e + 1))
    let T : ℚ[X] := C c * X ^ k
    have hTd : T.natDegree ≤ k := natDegree_C_mul_X_pow_le c k
    have hTq : T.natDegree < Q.natDegree := by omega
    refine ⟨Q + T, ?_, ?_, ?_⟩
    · rw [natDegree_add_eq_left_of_natDegree_lt hTq, hQd]
    · rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree hTq), hQl]
    · -- degree bound after the correction step
      obtain ⟨E, hEeq, hEd⟩ := binom_remainder Q T e hTq.le
      let M : ℚ[X] := ((e + 2 : ℕ) : ℚ[X]) * T * Q ^ (e + 1)
      have hexp : F - (Q + T) ^ (e + 2) = R - M - E := by
        rw [hEeq]; simp only [R, M]; ring
      have hRle : R.degree ≤ N1 := by
        have h' : q * (e + 2) - j = N1 + 1 := by omega
        rw [h'] at hQR
        exact degree_le_of_lt_succ hQR
      have hQpow : (Q ^ (e + 1)).natDegree = (e + 1) * q := by rw [natDegree_pow, hQd]
      have hMform : M = C (((e + 2 : ℕ) : ℚ) * c) * (Q ^ (e + 1) * X ^ k) := by
        simp only [M, T]
        rw [← Polynomial.C_eq_natCast, C_mul]; ring
      have hMle : M.degree ≤ N1 := by
        rw [hMform]
        refine degree_le_of_natDegree_le ?_
        calc _ ≤ (Q ^ (e + 1) * X ^ k).natDegree := natDegree_C_mul_le _ _
          _ ≤ (Q ^ (e + 1)).natDegree + (X ^ k : ℚ[X]).natDegree := natDegree_mul_le
          _ ≤ N1 := by rw [hQpow, natDegree_X_pow]; omega
      have hEle : E.natDegree < N1 := by
        have : (e * q) + q = (e + 1) * q := by ring
        rw [hQd] at hEd hTq
        omega
      have hMcoef : M.coeff N1 = R.coeff N1 := by
        rw [hMform, coeff_C_mul, hN1eq, coeff_mul_X_pow]
        have hcl : (Q ^ (e + 1)).coeff ((e + 1) * q) = b ^ (e + 1) := by
          rw [← hQpow, ← leadingCoeff, leadingCoeff_pow, hQl]
        rw [hcl]
        have h1 : (((e + 2 : ℕ) : ℚ)) ≠ 0 := by positivity
        have h2 : b ^ (e + 1) ≠ 0 := pow_ne_zero _ hb
        simp only [c]
        field_simp
        rw [← hN1eq]; ring
      have hcoef : (R - M - E).coeff N1 = 0 := by
        rw [coeff_sub, coeff_sub, hMcoef, coeff_eq_zero_of_natDegree_lt hEle]; ring
      have hdeg : (R - M - E).degree ≤ N1 :=
        (degree_sub_le _ _).trans (max_le ((degree_sub_le _ _).trans (max_le hRle hMle))
          (degree_le_of_natDegree_le hEle.le))
      rw [hexp]
      have hidx : q * (e + 2) - (j + 1) = N1 := by omega
      rw [hidx]
      exact degree_lt_of_coeff_zero hdeg hcoef

/-- Truncated root: for rigid `F ≠ 0` there is `Q ∈ ℚ[X]` of degree `deg F / d` with
`deg (F - Q^d) < deg (Q^(d-1))` (in `WithBot ℕ`, so `F = Q^d` is included). -/
theorem exists_truncated_root {d : ℕ} (hd : 2 ≤ d) {F : ℤ[X]} (hF : IsRigid d F) (hF0 : F ≠ 0) :
    ∃ Q : ℚ[X], Q.natDegree = F.natDegree / d ∧
      (F.map (Int.castRingHom ℚ) - Q ^ d).degree < (Q ^ (d - 1)).degree := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  obtain ⟨⟨q, hq⟩, b, hb⟩ := hF
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF0
  have hb0 : (b : ℚ) ≠ 0 := by
    intro h
    have : b = 0 := by exact_mod_cast h
    apply hlc
    rw [hb, this, zero_pow (by omega)]
  have hFd : (F.map (Int.castRingHom ℚ)).natDegree = q * (e + 2) := by
    rw [natDegree_map_eq_of_injective hinj, hq, mul_comm]
  have hlead : (F.map (Int.castRingHom ℚ)).leadingCoeff = (b : ℚ) ^ (e + 2) := by
    rw [leadingCoeff_map' hinj, hb]; simp
  obtain ⟨Q, hQd, hQl, hQR⟩ := trunc_induction (q := q) (e := e) (b : ℚ) hb0 _ hFd hlead q le_rfl
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, leadingCoeff_zero] at hQl; exact hb0 hQl.symm
  refine ⟨Q, ?_, ?_⟩
  · rw [hQd, hq, Nat.mul_div_cancel_left _ (by omega)]
  · have hpd : (Q ^ (e + 2 - 1)).degree = (((e + 1) * q : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree (pow_ne_zero _ hQ0), natDegree_pow, hQd]
      rfl
    rw [hpd]
    have : q * (e + 2) - q = (e + 1) * q := by
      have : q * (e + 2) = (e + 1) * q + q := by ring
      omega
    rwa [this] at hQR

end PerfectPower
