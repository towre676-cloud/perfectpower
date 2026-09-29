import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.ZMod.Basic
import PerfectPower.Basic

/-!
# A second rank-one curve: the integral points of `y^2 = x^3 - 4`

The integral points are `(2, ± 2)` and `(5, ± 11)` (Fermat's other claim).  The proof works in the
Gaussian integers `ℤ[i]` (Euclidean in Mathlib), where every unit is a cube.

* `y` odd: `y + 2i`, `y - 2i` are coprime (explicit Bézout), so `y + 2i = (a + b i)^3` and
  `b (3a^2 - b^2) = 2`; only `b = -2`, `a = ± 1` survives, giving `y = ∓ 11`, `x = 5`.
* `y` even: `y = 2 y₁`, `x = 2 x₁`, `y₁^2 + 1 = 2 x₁^3`, `y₁ = 2 j + 1` odd.  Then
  `y₁ + i = (1 + i) w` with `w = (j + 1) - j i`, and `w`, `conj w` are coprime with product `x₁^3`.
  So `w = (a + b i)^3`, and adding real and imaginary parts gives the Thue equation
  `(a - b)(a^2 + 4ab + b^2) = 1`, whose solutions give `j ∈ {0, -1}`, `y = ± 2`, `x = 2`.
-/

namespace PerfectPower.MordellMinus4

open GaussianInt

lemma norm_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

lemma cube_mk (a b : ℤ) :
    (⟨a, b⟩ : GaussianInt) ^ 3 = ⟨a ^ 3 - 3 * a * b ^ 2, 3 * a ^ 2 * b - b ^ 3⟩ := by
  ext <;> simp [pow_succ, Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring

/-- Every unit of `GaussianInt` is a cube: `1 = 1^3`, `-1 = (-1)^3`, `i = (-i)^3`, `-i = i^3`. -/
lemma unit_is_cube (u : GaussianIntˣ) : ∃ c : GaussianInt, (u : GaussianInt) = c ^ 3 := by
  have hn : (u : GaussianInt).norm = 1 := (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr u.isUnit
  generalize (u : GaussianInt) = z at hn ⊢
  obtain ⟨p, q⟩ := z
  rw [norm_eq] at hn
  simp only at hn
  have hp1 : -1 ≤ p := by nlinarith [sq_nonneg q]
  have hp2 : p ≤ 1 := by nlinarith [sq_nonneg q]
  have hq1 : -1 ≤ q := by nlinarith [sq_nonneg p]
  have hq2 : q ≤ 1 := by nlinarith [sq_nonneg p]
  interval_cases p <;> interval_cases q <;> simp at hn
  · exact ⟨⟨-1, 0⟩, by rw [cube_mk]; ext <;> simp⟩
  · exact ⟨⟨0, 1⟩, by rw [cube_mk]; ext <;> simp⟩
  · exact ⟨⟨0, -1⟩, by rw [cube_mk]; ext <;> simp⟩
  · exact ⟨⟨1, 0⟩, by rw [cube_mk]; ext <;> simp⟩

/-- If `a b = c^3` with `a`, `b` coprime, then `a` is a cube. -/
lemma cube_of_coprime {a b c : GaussianInt} (hab : IsCoprime a b) (h : a * b = c ^ 3) :
    ∃ e : GaussianInt, e ^ 3 = a := by
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  obtain ⟨c', hc'⟩ := unit_is_cube u
  exact ⟨d * c', by rw [mul_pow, ← hc', hu]⟩

lemma cube_inj {a b : ℤ} (h : a ^ 3 = b ^ 3) : a = b :=
  (Odd.pow_inj (⟨1, rfl⟩ : Odd 3)).mp h

/-- The odd case: `y + 2i` is a cube. -/
lemma odd_case (x y k : ℤ) (h : y ^ 2 = x ^ 3 - 4) (hk : y = 2 * k + 1) :
    x = 5 ∧ (y = 11 ∨ y = -11) := by
  have hAB : (⟨y, 2⟩ : GaussianInt) * ⟨y, -2⟩ = (⟨x, 0⟩ : GaussianInt) ^ 3 := by
    rw [cube_mk]; ext
    · simp [Zsqrtd.mul_re]; linear_combination h
    · simp [Zsqrtd.mul_im]; ring
  have hcop : IsCoprime (⟨y, 2⟩ : GaussianInt) ⟨y, -2⟩ := by
    refine ⟨⟨y, -2⟩ + ⟨0, k ^ 2 + k + 1⟩, -(⟨0, k ^ 2 + k + 1⟩ : GaussianInt), ?_⟩
    rw [hk]; ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
  obtain ⟨⟨a, b⟩, he⟩ := cube_of_coprime hcop hAB
  rw [cube_mk] at he
  obtain ⟨hre, him⟩ := Zsqrtd.mk.inj he
  have hb : b * (3 * a ^ 2 - b ^ 2) = 2 := by linear_combination him
  have hbd : b ∣ 2 := ⟨_, hb.symm⟩
  have hb2 : b ≤ 2 := Int.le_of_dvd (by norm_num) hbd
  have hb2' : -2 ≤ b := by
    have := Int.le_of_dvd (by norm_num) (neg_dvd.mpr hbd); linarith
  have hsq := sq_nonneg a
  interval_cases b
  · -- b = -2
    have ha2 : a ^ 2 = 1 := by nlinarith
    have ha : (a - 1) * (a + 1) = 0 := by linear_combination ha2
    rcases mul_eq_zero.mp ha with ha | ha
    · have : a = 1 := by linarith
      subst this
      refine ⟨cube_inj (by nlinarith), Or.inr (by linarith)⟩
    · have : a = -1 := by linarith
      subst this
      refine ⟨cube_inj (by nlinarith), Or.inl (by linarith)⟩
  · -- b = -1
    exfalso; nlinarith
  · -- b = 0
    simp at hb
  · -- b = 1: then `y = ± 2`, not odd
    exfalso
    have ha2 : a ^ 2 = 1 := by nlinarith
    have ha : (a - 1) * (a + 1) = 0 := by linear_combination ha2
    rcases mul_eq_zero.mp ha with ha | ha
    · have : a = 1 := by linarith
      subst this; omega
    · have : a = -1 := by linarith
      subst this; omega
  · -- b = 2
    exfalso
    have h3 : 3 * a ^ 2 = 5 := by linarith
    generalize a ^ 2 = t at h3
    omega

/-- The even case: reduce to `y₁^2 + 1 = 2 x₁^3` and a Thue equation. -/
lemma even_case (x y : ℤ) (h : y ^ 2 = x ^ 3 - 4) (hy : y % 2 = 0) :
    x = 2 ∧ (y = 2 ∨ y = -2) := by
  obtain ⟨y₁, rfl⟩ : ∃ y₁, y = 2 * y₁ := ⟨y / 2, by omega⟩
  have hx2 : x % 2 = 0 := by
    have key : ∀ X : ZMod 2, X ^ 3 = 0 → X = 0 := by decide
    have h2 := congrArg (Int.cast : ℤ → ZMod 2) (show x ^ 3 = 4 * y₁ ^ 2 + 4 by linarith)
    push_cast at h2
    have h0 : (x : ZMod 2) ^ 3 = 0 := by
      rw [h2]; have : (4 : ZMod 2) = 0 := by decide
      rw [this]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp (key _ h0)
    omega
  obtain ⟨x₁, rfl⟩ : ∃ x₁, x = 2 * x₁ := ⟨x / 2, by omega⟩
  have h1 : y₁ ^ 2 + 1 = 2 * x₁ ^ 3 := by linarith
  have hy₁ : y₁ % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one y₁ with e | e
    · exfalso
      obtain ⟨t, rfl⟩ : ∃ t, y₁ = 2 * t := ⟨y₁ / 2, by omega⟩
      have : (4 * t ^ 2 + 1) % 2 = (2 * x₁ ^ 3) % 2 := by rw [← h1]; ring_nf
      omega
    · exact e
  obtain ⟨j, hj⟩ : ∃ j, y₁ = 2 * j + 1 := ⟨y₁ / 2, by omega⟩
  -- `w = (j + 1) - j i` and its conjugate: coprime, product `x₁^3`
  have hww : (⟨j + 1, -j⟩ : GaussianInt) * ⟨j + 1, j⟩ = (⟨x₁, 0⟩ : GaussianInt) ^ 3 := by
    rw [cube_mk]; ext
    · simp [Zsqrtd.mul_re]; rw [hj] at h1; nlinarith
    · simp [Zsqrtd.mul_im]; ring
  have hcop : IsCoprime (⟨j + 1, -j⟩ : GaussianInt) ⟨j + 1, j⟩ := by
    refine ⟨⟨j + 1, j⟩ - ⟨j, 0⟩, -(⟨j, 0⟩ : GaussianInt), ?_⟩
    ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
  obtain ⟨⟨a, b⟩, he⟩ := cube_of_coprime hcop hww
  rw [cube_mk] at he
  obtain ⟨hre, him⟩ := Zsqrtd.mk.inj he
  -- Thue: `(a - b)(a^2 + 4ab + b^2) = 1`
  have hthue : (a - b) * (a ^ 2 + 4 * a * b + b ^ 2) = 1 := by linear_combination hre + him
  have hj01 : j = 0 ∨ j = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hthue with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · obtain rfl : a = b + 1 := by linarith
      have : b * (b + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with hb | hb
      · subst hb; left; linarith
      · have : b = -1 := by linarith
        subst this; right; linarith
    · exfalso
      obtain rfl : a = b - 1 := by linarith
      nlinarith [sq_nonneg (2 * b - 1)]
  have hy : y₁ = 1 ∨ y₁ = -1 := by rcases hj01 with rfl | rfl <;> [left; right] <;> linarith
  have hx : x₁ ^ 3 = 1 ^ 3 := by rcases hy with rfl | rfl <;> linarith
  refine ⟨by linarith [cube_inj hx], ?_⟩
  rcases hy with rfl | rfl <;> simp

/-- **The integral points of `y^2 = x^3 - 4` are `(2, ± 2)` and `(5, ± 11)`.** -/
theorem points (x y : ℤ) :
    y ^ 2 = x ^ 3 - 4 ↔ (x = 2 ∧ (y = 2 ∨ y = -2)) ∨ (x = 5 ∧ (y = 11 ∨ y = -11)) := by
  constructor
  · intro h
    rcases Int.emod_two_eq_zero_or_one y with e | e
    · exact Or.inl (even_case x y h e)
    · obtain ⟨k, hk⟩ : ∃ k, y = 2 * k + 1 := ⟨y / 2, by omega⟩
      exact Or.inr (odd_case x y k h hk)
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩) <;> norm_num

/-- **Complete hit list.**  For `n ≥ 1`, `n^3 - 4` is a perfect square iff `n ∈ {2, 5}`. -/
theorem hitSet (n : ℕ) : IsHit 2 ((n : ℤ) ^ 3 - 4) ↔ n = 2 ∨ n = 5 := by
  constructor
  · rintro ⟨m, hm⟩
    rcases (points n m).mp hm.symm with ⟨h, -⟩ | ⟨h, -⟩
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · rintro (rfl | rfl)
    · exact ⟨2, by norm_num⟩
    · exact ⟨11, by norm_num⟩

end PerfectPower.MordellMinus4
