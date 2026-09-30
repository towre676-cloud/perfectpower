import PerfectPower.SqrtTwoBatch
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence

/-!
# Reusable bridges: continued fractions of `√2`, Euclid's triples, and a shifted duplicate

* **Continued fraction of `√2`** (`cf_sqrt2_s`, `contsAux_sqrt2`).  In Mathlib's
  `GenContFract.of √2`, every partial quotient after `⌊√2⌋ = 1` is `2`, because the fractional
  part of `√2 + 1` is again `√2 - 1`.  The continuants are the orbit coordinates:
  `contsAux n = ⟨A_n, B_n⟩`, from `contsAux 0 = ⟨1, 0⟩` (the formal convergent `1/0`).  So the
  `n`-th convergent is `A_{n+1} / B_{n+1}` (`convs_sqrt2`), in lowest terms (`coprime_AB`, from the
  norm `A_n^2 - 2 B_n^2 = (-1)^n`).
  - **A001333** ("numerators of continued fraction convergents to `sqrt(2)`", offset 0) is
    `(contsAux n).a`, the numerator sequence *including* `p_{-1} = 1`, which is what the entry
    lists (`1, 1, 3, 7, …`): `A001333_eq`.
* **Euclid's primitive triples** (`euclid_primitive`).  For `a, b, c > 0` with `a^2 + b^2 = c^2`,
  `gcd(a, b) = 1` and `a` odd (the leg convention), there are unique-up-to-nothing integers
  `m > n > 0`, coprime, of opposite parity, with `a = m^2 - n^2`, `b = 2 m n`, `c = m^2 + n^2`;
  conversely every such `(m, n)` gives a primitive triple (`euclid_converse`).
  - **Consecutive legs** (`euclid_consecutive`): for the triples of A046090, `|a - b| = 1` makes
    the Euclid parameters an orbit point: `(m - n)^2 - 2 n^2 = ± 1`.
* **A048624** is a dead entry whose whole definition is "Essentially a duplicate of A000129".  The
  text does not fix the shift; its listed terms do, uniquely: `a(n) = A000129(n + 2)`.  The Lean
  statement records that reading (`A048624_eq`).
-/

namespace PerfectPower.SqrtTwoBridges

open PerfectPower SqrtTwoOrbit

/-! ### The continued fraction of `√2` -/

lemma sqrt2_bounds : (1 : ℝ) < √2 ∧ √2 < 2 :=
  ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num), (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)⟩

lemma floor_sqrt2 : ⌊(√2 : ℝ)⌋ = 1 := by
  rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [sqrt2_bounds.1, sqrt2_bounds.2]

lemma fract_sqrt2 : Int.fract (√2 : ℝ) = √2 - 1 := by
  rw [Int.fract, floor_sqrt2]; push_cast; ring

lemma inv_fract_sqrt2 : (Int.fract (√2 : ℝ))⁻¹ = √2 + 1 := by
  rw [fract_sqrt2]
  have h2 : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact inv_eq_of_mul_eq_one_right (by linear_combination h2)

lemma floor_w : ⌊(√2 + 1 : ℝ)⌋ = 2 := by
  rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [sqrt2_bounds.1, sqrt2_bounds.2]

lemma fract_w : Int.fract (√2 + 1 : ℝ) = √2 - 1 := by
  rw [Int.fract, floor_w]; push_cast; ring

lemma fract_w_ne : Int.fract (√2 + 1 : ℝ) ≠ 0 := by
  rw [fract_w]; linarith [sqrt2_bounds.1]

lemma inv_fract_w : (Int.fract (√2 + 1 : ℝ))⁻¹ = √2 + 1 := by
  rw [fract_w, ← fract_sqrt2, inv_fract_sqrt2]

/-- The periodic part: every term of `of (√2 + 1)` is `⟨1, 2⟩`. -/
lemma cf_w_s (n : ℕ) : (GenContFract.of (√2 + 1 : ℝ)).s.get? n = some ⟨1, 2⟩ := by
  induction n with
  | zero =>
    have := GenContFract.of_s_head fract_w_ne
    rw [Stream'.Seq.head] at this
    rw [this, inv_fract_w, floor_w]; norm_num
  | succ n ih => rw [GenContFract.of_s_succ, inv_fract_w, ih]

/-- **The partial quotients of `√2`**: every term of `of √2` is `⟨1, 2⟩`. -/
theorem cf_sqrt2_s (n : ℕ) : (GenContFract.of (√2 : ℝ)).s.get? n = some ⟨1, 2⟩ := by
  cases n with
  | zero =>
    have hne : Int.fract (√2 : ℝ) ≠ 0 := by rw [fract_sqrt2]; linarith [sqrt2_bounds.1]
    have := GenContFract.of_s_head hne
    rw [Stream'.Seq.head] at this
    rw [this, inv_fract_sqrt2, floor_w]; norm_num
  | succ n => rw [GenContFract.of_s_succ, inv_fract_sqrt2, cf_w_s]

theorem cf_sqrt2_h : (GenContFract.of (√2 : ℝ)).h = 1 := by
  rw [GenContFract.of_h_eq_floor, floor_sqrt2]; norm_num

/-- **The continuants of `√2` are the orbit coordinates.** -/
theorem contsAux_sqrt2 (n : ℕ) :
    (GenContFract.of (√2 : ℝ)).contsAux n = ⟨(SqrtTwoOrbit.A n : ℝ), (B n : ℝ)⟩ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [GenContFract.zeroth_contAux_eq_one_zero]; simp [SqrtTwoOrbit.A, B, AB]
    | 1 => rw [GenContFract.first_contAux_eq_h_one, cf_sqrt2_h]; simp [SqrtTwoOrbit.A, B, AB]
    | n + 2 =>
      rw [GenContFract.contsAux_recurrence (cf_sqrt2_s n) (ih n (by omega)) (ih (n + 1) (by omega))]
      simp only [GenContFract.Pair.mk.injEq]
      rw [SqrtTwoOrbit.A_rec, B_rec]; push_cast; constructor <;> ring

/-- **The `n`-th convergent of `√2` is `A_{n+1} / B_{n+1}`.** -/
theorem convs_sqrt2 (n : ℕ) :
    (GenContFract.of (√2 : ℝ)).convs n = (SqrtTwoOrbit.A (n + 1) : ℝ) / (B (n + 1) : ℝ) := by
  rw [GenContFract.conv_eq_conts_a_div_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux,
    contsAux_sqrt2]

/-- The convergents are in lowest terms. -/
theorem coprime_AB (n : ℕ) : IsCoprime (SqrtTwoOrbit.A n) (B n) := by
  refine ⟨(-1) ^ n * SqrtTwoOrbit.A n, (-1) ^ n * (-2 * B n), ?_⟩
  have h := norm_AB n
  have hs : ((-1 : ℤ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  linear_combination (-1 : ℤ) ^ n * h + hs

/-- A001333: "Pell-Lucas numbers: numerators of continued fraction convergents to sqrt(2)"
(offset 0: `a(0) = p_{-1} = 1`, then the numerators of the convergents). -/
noncomputable def A001333 (n : ℕ) : ℝ := ((GenContFract.of (√2 : ℝ)).contsAux n).a

theorem A001333_eq (n : ℕ) : A001333 n = (SqrtTwoOrbit.A n : ℝ) := by
  rw [A001333, contsAux_sqrt2]

/-- For `n ≥ 1`, `A001333(n)` is the numerator of the `(n-1)`-th convergent. -/
theorem A001333_num (n : ℕ) : A001333 (n + 1) = (GenContFract.of (√2 : ℝ)).nums n := by
  rw [A001333, GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux]

/-! ### Euclid's primitive Pythagorean triples -/

/-- **Euclid's classification, with its conventions**: positive legs, `gcd(a, b) = 1`, `a` odd. -/
theorem euclid_primitive {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 = c ^ 2) (hcop : Int.gcd a b = 1) (hodd : a % 2 = 1) :
    ∃ m n : ℤ, 0 < n ∧ n < m ∧ Int.gcd m n = 1 ∧ (m + n) % 2 = 1 ∧
      a = m ^ 2 - n ^ 2 ∧ b = 2 * m * n ∧ c = m ^ 2 + n ^ 2 := by
  have ht : PythagoreanTriple a b c := by
    unfold PythagoreanTriple; linear_combination h
  obtain ⟨m, n, h1, h2, h3, hmn, hpar, hm0⟩ := ht.coprime_classification' hcop hodd hc
  -- normalize the sign of `n` using `b > 0`
  have hm : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · subst h; nlinarith
  have hn : 0 < n := by
    by_contra hn; push_neg at hn; nlinarith
  refine ⟨m, n, hn, ?_, hmn, by omega, h1, h2, h3⟩
  by_contra hc'; push_neg at hc'
  nlinarith

/-- The converse: every such `(m, n)` gives a primitive triple with `a` odd. -/
theorem euclid_converse {m n : ℤ} (hn : 0 < n) (hmn : n < m) (hcop : Int.gcd m n = 1)
    (hpar : (m + n) % 2 = 1) :
    0 < m ^ 2 - n ^ 2 ∧ 0 < 2 * m * n ∧ (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 ∧
      (m ^ 2 - n ^ 2) % 2 = 1 ∧ Int.gcd (m ^ 2 - n ^ 2) (2 * m * n) = 1 := by
  refine ⟨by nlinarith, mul_pos (mul_pos two_pos (by linarith)) hn, by ring, ?_, ?_⟩
  · have : m ^ 2 - n ^ 2 = (m + n) * (m - n) := by ring
    rw [this, Int.mul_emod]
    have : (m - n) % 2 = 1 := by omega
    rw [hpar, this]; norm_num
  · have := (PythagoreanTriple.coprime_classification (x := m ^ 2 - n ^ 2) (y := 2 * m * n)
      (z := m ^ 2 + n ^ 2)).mpr ⟨m, n, Or.inl ⟨rfl, rfl⟩, Or.inl rfl, hcop, by omega⟩
    exact this.2

/-- **Consecutive legs are an orbit**: for Euclid parameters of a triple whose legs differ by
one, `(m - n)^2 - 2 n^2 = ± 1`. -/
theorem euclid_consecutive {m n : ℤ} (h : (m ^ 2 - n ^ 2) - 2 * m * n = 1 ∨
    (m ^ 2 - n ^ 2) - 2 * m * n = -1) :
    (m - n) ^ 2 - 2 * n ^ 2 = 1 ∨ (m - n) ^ 2 - 2 * n ^ 2 = -1 := by
  rcases h with h | h
  · left; linear_combination h
  · right; linear_combination h

/-! ### A048624, a shifted duplicate -/

/-- A048624 (dead; "Essentially a duplicate of A000129", offset 0), with the shift its listed
terms determine: `a(n) = A000129(n + 2)`. -/
def A048624 (n : ℕ) : ℤ := A000129 (n + 2)

theorem A048624_eq (n : ℕ) : A048624 n = B (n + 2) := A000129_eq (n + 2)

end PerfectPower.SqrtTwoBridges
