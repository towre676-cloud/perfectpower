import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.ZMod.Basic
import PerfectPower.Basic

/-!
# A rank-one curve, completely: the integral points of `y^2 = x^3 - 2`

The curve `y^2 = x^3 - 2` has rank one (infinitely many rational points), so neither a congruence
obstruction nor a finite-group argument can settle it.  Its integral points are `(3, ± 5)`
(Fermat's claim; Euler).  The proof is the classical one in `ℤ[√-2]`:

1. `ℤ[√-2]` is Euclidean for the norm `a^2 + 2 b^2`: we give the division with integer rounding
   (`rdiv`), so the remainder has norm at most `3/4` of the divisor's.
2. `y` is odd (mod 4), so `y + √-2` and `y - √-2` are coprime: an explicit Bézout identity.
3. Their product is `x^3`, so `y + √-2 = ± d^3`; the units are `± 1`, both cubes.
4. Writing the cube root as `a + b√-2`, the `√-2`-coefficient gives `b (3a^2 - 2b^2) = 1`,
   hence `b = 1`, `a = ± 1`, `y = ∓ 5`, `x = 3`.

This reproves in Lean 4 / Mathlib a result formalised in Lean 3 by Baanen, Best, Coppola and
Dahmen (CPP 2023) by class-group methods; the proof here is independent and elementary.
-/

namespace PerfectPower.MordellMinus2

/-- `ℤ[√-2]`. -/
abbrev R := ℤ√(-2)

/-! ### Euclidean division in `ℤ[√-2]` -/

/-- Nearest-integer division, `⌊p / N + 1/2⌋`. -/
def rdiv (p N : ℤ) : ℤ := (2 * p + N) / (2 * N)

lemma rdiv_spec (p N : ℤ) (hN : 0 < N) : 4 * (p - N * rdiv p N) ^ 2 ≤ N ^ 2 := by
  have h2N : 0 < 2 * N := by linarith
  have h1 := Int.ediv_mul_le (2 * p + N) h2N.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (2 * p + N) h2N
  unfold rdiv
  set q := (2 * p + N) / (2 * N)
  have hlo : 0 ≤ N + 2 * (p - N * q) := by nlinarith
  have hhi : 0 ≤ N - 2 * (p - N * q) := by nlinarith
  nlinarith [mul_nonneg hlo hhi]

lemma norm_eq (z : R) : z.norm = z.re ^ 2 + 2 * z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

lemma norm_nonneg' (z : R) : 0 ≤ z.norm := by rw [norm_eq]; positivity

lemma norm_pos' {z : R} (hz : z ≠ 0) : 0 < z.norm := by
  rcases (norm_nonneg' z).lt_or_eq with h | h
  · exact h
  · exfalso; apply hz
    rw [norm_eq] at h
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    exact Zsqrtd.ext hre him

instance : Div R :=
  ⟨fun x y => ⟨rdiv (x * star y).re y.norm, rdiv (x * star y).im y.norm⟩⟩

instance : Mod R := ⟨fun x y => x - y * (x / y)⟩

lemma div_def (x y : R) : x / y = ⟨rdiv (x * star y).re y.norm, rdiv (x * star y).im y.norm⟩ :=
  rfl

lemma mod_def (x y : R) : x % y = x - y * (x / y) := rfl

lemma norm_rem (x y : R) (q1 q2 : ℤ) :
    y.norm * (x - y * ⟨q1, q2⟩).norm
      = ((x * star y).re - y.norm * q1) ^ 2 + 2 * ((x * star y).im - y.norm * q2) ^ 2 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, e⟩ := y
  simp only [norm_eq, Zsqrtd.sub_re, Zsqrtd.sub_im, Zsqrtd.mul_re, Zsqrtd.mul_im,
    Zsqrtd.star_re, Zsqrtd.star_im]
  ring

lemma norm_mod_lt (x : R) {y : R} (hy : y ≠ 0) : (x % y).norm < y.norm := by
  have hN := norm_pos' hy
  have s1 := rdiv_spec (x * star y).re y.norm hN
  have s2 := rdiv_spec (x * star y).im y.norm hN
  have iden := norm_rem x y (rdiv (x * star y).re y.norm) (rdiv (x * star y).im y.norm)
  rw [mod_def, div_def]
  nlinarith

lemma natAbs_norm_mod_lt (x : R) {y : R} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
  Int.natAbs_lt_natAbs_of_nonneg_of_lt (norm_nonneg' _) (norm_mod_lt x hy)

lemma norm_le_norm_mul_left (a : R) {b : R} (hb : b ≠ 0) :
    a.norm.natAbs ≤ (a * b).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have : 0 < b.norm.natAbs := Int.natAbs_pos.mpr (norm_pos' hb).ne'
  exact Nat.le_mul_of_pos_right _ this

instance euclideanDomain : EuclideanDomain R :=
  { (inferInstance : CommRing R), (inferInstance : Nontrivial R) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := fun x => by
      rw [div_def]; ext <;> simp [rdiv, Zsqrtd.norm_def]
    quotient_mul_add_remainder_eq := fun x y => by
      show y * (x / y) + (x - y * (x / y)) = x
      ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := fun x _ hy => natAbs_norm_mod_lt x hy
    mul_left_not_lt := fun a _ hb => not_lt_of_ge (norm_le_norm_mul_left a hb) }

/-! ### Units, cubes -/

lemma unit_eq (u : Rˣ) : (u : R) = 1 ∨ (u : R) = -1 := by
  have hn : (u : R).norm = 1 := (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr u.isUnit
  rw [norm_eq] at hn
  have him : (u : R).im = 0 := by nlinarith [sq_nonneg (u : R).re, sq_nonneg (u : R).im]
  have hre : (u : R).re ^ 2 = 1 := by rw [him] at hn; linarith
  have : ((u : R).re - 1) * ((u : R).re + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp this with h | h
  · left; ext <;> simp [him]; linarith
  · right; ext <;> simp [him]; linarith

lemma cube_inj {a b : ℤ} (h : a ^ 3 = b ^ 3) : a = b :=
  (Odd.pow_inj (⟨1, rfl⟩ : Odd 3)).mp h

lemma cube_mk (a b : ℤ) :
    (⟨a, b⟩ : R) ^ 3 = ⟨a ^ 3 - 6 * a * b ^ 2, 3 * a ^ 2 * b - 2 * b ^ 3⟩ := by
  ext <;> simp [pow_succ, Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring

/-! ### The theorem -/

/-- **The integral points of `y^2 = x^3 - 2` are `(3, ± 5)`.** -/
theorem points (x y : ℤ) : y ^ 2 = x ^ 3 - 2 ↔ x = 3 ∧ (y = 5 ∨ y = -5) := by
  constructor
  swap
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num
  intro h
  -- `y` is odd
  have hodd : y % 2 = 1 := by
    have key : ∀ X Y : ZMod 4, Y ^ 2 = X ^ 3 - 2 → Y = 1 ∨ Y = 3 := by decide
    have h4 := congrArg (Int.cast : ℤ → ZMod 4) h
    push_cast at h4
    rcases key _ _ h4 with hc | hc
    · have : ((y - 1 : ℤ) : ZMod 4) = 0 := by push_cast; rw [hc]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
      omega
    · have : ((y - 3 : ℤ) : ZMod 4) = 0 := by push_cast; rw [hc]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
      omega
  obtain ⟨k, hk⟩ : ∃ k, y = 2 * k + 1 := ⟨y / 2, by omega⟩
  -- factor `x^3 = (y + √-2)(y - √-2)`
  set A : R := ⟨y, 1⟩ with hA
  have hAB : A * (⟨y, -1⟩ : R) = (⟨x, 0⟩ : R) ^ 3 := by
    rw [cube_mk, hA]
    ext
    · simp [Zsqrtd.mul_re]; linear_combination h
    · simp [Zsqrtd.mul_im]
  have hcop : IsCoprime A (⟨y, -1⟩ : R) := by
    refine ⟨-(⟨y, -1⟩ : R) - (⟨0, k ^ 2 + k + 1⟩ : R), (⟨0, k ^ 2 + k + 1⟩ : R), ?_⟩
    rw [hA, hk]
    ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
  -- `y + √-2` is a cube
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hcop hAB
  obtain ⟨e, he⟩ : ∃ e : R, e ^ 3 = A := by
    rcases unit_eq u with h1 | h1
    · exact ⟨d, by rw [← hu, h1, mul_one]⟩
    · exact ⟨-d, by rw [← hu, h1]; ring⟩
  obtain ⟨a, b⟩ := e
  rw [cube_mk, hA] at he
  obtain ⟨hre, him⟩ := Zsqrtd.mk.inj he
  -- `b (3 a^2 - 2 b^2) = 1`
  have hb : b * (3 * a ^ 2 - 2 * b ^ 2) = 1 := by linear_combination him
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hb with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · have ha2 : a ^ 2 = 1 := by nlinarith
    have ha : (a - 1) * (a + 1) = 0 := by linear_combination ha2
    have hx3 : x ^ 3 = 3 ^ 3 := by
      rcases mul_eq_zero.mp ha with ha | ha
      · have : a = 1 := by linarith
        subst this; nlinarith
      · have : a = -1 := by linarith
        subst this; nlinarith
    refine ⟨cube_inj hx3, ?_⟩
    rcases mul_eq_zero.mp ha with ha | ha
    · right; have : a = 1 := by linarith
      subst this; linarith
    · left; have : a = -1 := by linarith
      subst this; linarith
  · exfalso
    have h3 : 3 * a ^ 2 = 1 := by linarith
    generalize a ^ 2 = t at h3
    omega

/-- **Complete hit list.**  For `n ≥ 1`, `n^3 - 2` is a perfect square iff `n = 3`. -/
theorem hitSet (n : ℕ) : IsHit 2 ((n : ℤ) ^ 3 - 2) ↔ n = 3 := by
  constructor
  · rintro ⟨m, hm⟩
    have := ((points n m).mp hm.symm).1
    exact_mod_cast this
  · rintro rfl
    exact ⟨5, by norm_num⟩

end PerfectPower.MordellMinus2
