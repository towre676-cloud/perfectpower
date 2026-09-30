import PerfectPower.SqrtTwoOrbit
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Int.Basic

/-!
# More entries of the `1 + √2` orbit, from their own definitions

Entries whose definitions need machinery beyond recurrences and generating functions, each
defined here from the text of its OEIS entry (with its offset) and proved equal to a coordinate
of `(1 + √2)^k = A_k + B_k √2`:

* **Pythagorean triples** `(X, X + 1, Z)` ordered by increasing `Z` (A046090, A115598,
  A115599): the parametrization `(2X + 1)^2 - 2 Z^2 = -1` puts them on the odd orbit
  (`triple_iff`).  A046090 lists the degenerate triple `(0, 1, 1)`; A115598/9 start at
  `(3, 4, 5)`: the two domains are both formalized.
* **A matrix orbit** (A090390): `(1, 0, 0)` repeatedly multiplied by the Berggren-type matrix
  `[[1,2,2],[2,1,2],[2,2,3]]` is `(A_n^2, 2 B_n^2, 2 A_n B_n)`.
* **A coprime splitting** (A078522): `(k + 1)(2k + 1)` is a square iff both coprime factors are,
  which is the odd orbit.
* **A finite exceptional set** (A055792): `a` and `⌊a/2⌋` both squares means `a = x^2` with
  `x^2 - 2y^2 ∈ {0, 1}`; `0` comes from `x^2 = 2y^2` (irrationality of `√2`), the rest from the
  even orbit.
* **Residue filter** (A046176): `k^2 = m(2m - 1)` is `(4m - 1)^2 - 2(2k)^2 = 1` with
  `4m - 1 ≡ 3 (mod 4)`, i.e. the even orbit on every other index.
* **Squares and products of entries** (A008843, A008844, A098602), read through the entries they
  name.
-/

namespace PerfectPower.SqrtTwoBatch

open PerfectPower PellExact SqrtTwoOrbit

lemma B_odd_pos (j : ℕ) : 0 < B (2 * j + 1) := by
  have h1 := B_parity (2 * j + 1)
  have h2 := B_nonneg (2 * j + 1)
  push_cast at h1
  omega

lemma A_odd_mono : StrictMono (fun n => SqrtTwoOrbit.A (2 * n + 1)) :=
  strictMono_nat_of_lt_succ fun n => by
    show SqrtTwoOrbit.A (2 * n + 1) < SqrtTwoOrbit.A (2 * (n + 1) + 1)
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring]; exact A_step _

/-- `a(n)`, `n ≥ off`, lists the pairs `S` by strictly increasing second coordinate. -/
def ListsBySnd (f : ℕ → ℤ × ℤ) (off : ℕ) (S : Set (ℤ × ℤ)) : Prop :=
  StrictMono (fun n => (f (n + off)).2) ∧ ∀ t, t ∈ S ↔ ∃ n, f (n + off) = t

/-! ### Pythagorean triples `(X, X + 1, Z)` -/

/-- Triples `X^2 + (X + 1)^2 = Z^2` with `X ≥ 0`, `Z > 0`, as pairs `(X, Z)`. -/
def PythTriples : Set (ℤ × ℤ) := {t | 0 ≤ t.1 ∧ 0 < t.2 ∧ t.1 ^ 2 + (t.1 + 1) ^ 2 = t.2 ^ 2}

/-- The positive ones, `X ≥ 1`. -/
def PosPythTriples : Set (ℤ × ℤ) := {t | 1 ≤ t.1 ∧ 0 < t.2 ∧ t.1 ^ 2 + (t.1 + 1) ^ 2 = t.2 ^ 2}

/-- The `j`-th triple: `2X + 1 = A_{2j+1}`, `Z = B_{2j+1}`. -/
def triple (j : ℕ) : ℤ × ℤ := ((SqrtTwoOrbit.A (2 * j + 1) - 1) / 2, B (2 * j + 1))

lemma two_X (j : ℕ) : 2 * (triple j).1 + 1 = SqrtTwoOrbit.A (2 * j + 1) := by
  have := (parity (2 * j + 1)).1
  simp only [triple]; omega

lemma triple_mem (j : ℕ) : triple j ∈ PythTriples := by
  have h2 := two_X j
  have hn := norm_odd j
  have hA := A_pos (2 * j + 1)
  refine ⟨by omega, show 0 < B (2 * j + 1) from B_odd_pos j, ?_⟩
  have : 2 * ((triple j).1 ^ 2 + ((triple j).1 + 1) ^ 2) = 2 * (triple j).2 ^ 2 := by
    rw [← h2] at hn; simp only [triple] at hn ⊢; linear_combination hn
  linarith

/-- **The triples are exactly the odd orbit.** -/
theorem triple_iff (t : ℤ × ℤ) : t ∈ PythTriples ↔ ∃ j, triple j = t := by
  constructor
  · rintro ⟨hX, hZ, h⟩
    have hp : Sol 2 (-1) (2 * t.1 + 1, t.2) :=
      ⟨by omega, hZ.le, by show (2 * t.1 + 1) ^ 2 - 2 * t.2 ^ 2 = -1; linear_combination 2 * h⟩
    obtain ⟨j, hj⟩ := (odd_sol_iff _).mp hp
    have h1 : SqrtTwoOrbit.A (2 * j + 1) = 2 * t.1 + 1 := by rw [SqrtTwoOrbit.A, hj]
    have h2 : B (2 * j + 1) = t.2 := by rw [B, hj]
    exact ⟨j, Prod.ext (by simp only [triple]; omega) h2⟩
  · rintro ⟨j, rfl⟩; exact triple_mem j

lemma triple_zero : triple 0 = (0, 1) := by decide

/-- **Ordered by increasing `Z`, from the degenerate triple `(0, 1, 1)`.** -/
theorem triples_listed : ListsBySnd triple 0 PythTriples :=
  ⟨fun a b h => show B (2 * (a + 0) + 1) < B (2 * (b + 0) + 1) from B_odd_mono h,
    fun t => by simpa using triple_iff t⟩

/-- **The positive triples, ordered by increasing `Z`, from `(3, 4, 5)`.** -/
theorem pos_triples_listed : ListsBySnd triple 1 PosPythTriples := by
  refine ⟨fun a b h => show B (2 * (a + 1) + 1) < B (2 * (b + 1) + 1) from
    B_odd_mono (show a + 1 < b + 1 by omega), fun t => ⟨?_, ?_⟩⟩
  · rintro ⟨hX, hZ, h⟩
    obtain ⟨j, hj⟩ := (triple_iff t).mp ⟨by omega, hZ, h⟩
    rcases j with _ | n
    · rw [triple_zero] at hj; rw [← hj] at hX; norm_num at hX
    · exact ⟨n, hj⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨hX, hZ, h⟩ := triple_mem (n + 1)
    refine ⟨?_, hZ, h⟩
    have h1 := two_X (n + 1)
    have h3 : SqrtTwoOrbit.A (2 * 0 + 1) < SqrtTwoOrbit.A (2 * (n + 1) + 1) := A_odd_mono (by omega)
    have h4 : SqrtTwoOrbit.A (2 * 0 + 1) = 1 := by decide
    omega

/-- A046090: "Consider all Pythagorean triples `(X, X+1, Z)` ordered by increasing `Z`;
sequence gives `X+1` values" (offset 0: the triple `(0, 1, 1)` is listed). -/
def A046090 (n : ℕ) : ℤ := (triple n).1 + 1

/-- A115598: the same triples (offset 1, from `(3, 4, 5)`), `Z - (X+1)` values. -/
def A115598 (n : ℕ) : ℤ := (triple (n - 1 + 1)).2 - ((triple (n - 1 + 1)).1 + 1)

/-- A115599: the same triples (offset 1), `Z - X` values. -/
def A115599 (n : ℕ) : ℤ := (triple (n - 1 + 1)).2 - (triple (n - 1 + 1)).1

theorem A046090_eq (n : ℕ) : 2 * A046090 n = SqrtTwoOrbit.A (2 * n + 1) + 1 := by
  have := two_X n; simp only [A046090]; omega

theorem A115598_eq (n : ℕ) : 2 * A115598 (n + 1) = 2 * B (2 * (n + 1) + 1) - SqrtTwoOrbit.A (2 * (n + 1) + 1) - 1 := by
  have := two_X (n + 1); simp only [A115598, Nat.add_sub_cancel]
  simp only [triple] at this ⊢; omega

theorem A115599_eq (n : ℕ) : 2 * A115599 (n + 1) = 2 * B (2 * (n + 1) + 1) - SqrtTwoOrbit.A (2 * (n + 1) + 1) + 1 := by
  have := two_X (n + 1); simp only [A115599, Nat.add_sub_cancel]
  simp only [triple] at this ⊢; omega

/-- A098602: `a(n) = A001652(n) * A046090(n)`. -/
def A098602 (n : ℕ) : ℤ := A001652 n * A046090 n

theorem A098602_eq (n : ℕ) : 4 * A098602 n = SqrtTwoOrbit.A (2 * n + 1) ^ 2 - 1 := by
  have h1 := A001652_eq n
  have h2 := A046090_eq n
  simp only [A098602]
  linear_combination (2 * A046090 n) * h1 + (SqrtTwoOrbit.A (2 * n + 1) - 1) * h2

/-! ### A matrix orbit -/

/-- The matrix of A090390. -/
def M3 : Matrix (Fin 3) (Fin 3) ℤ := !![1, 2, 2; 2, 1, 2; 2, 2, 3]

/-- `(1, 0, 0)` multiplied `n` times by `M3`. -/
def vM : ℕ → (Fin 3 → ℤ)
  | 0 => ![1, 0, 0]
  | n + 1 => Matrix.vecMul (vM n) M3

/-- A090390: "Repeatedly multiply `(1,0,0)` by `([1,2,2],[2,1,2],[2,2,3])`; sequence gives
leading entry" (offset 0). -/
def A090390 (n : ℕ) : ℤ := vM n 0

theorem vM_eq (n : ℕ) : vM n = ![SqrtTwoOrbit.A n ^ 2, 2 * B n ^ 2, 2 * SqrtTwoOrbit.A n * B n] := by
  induction n with
  | zero => ext i; fin_cases i <;> rfl
  | succ n ih =>
    ext i
    fin_cases i <;>
    simp [vM, ih, Matrix.vecMul, dotProduct, Fin.sum_univ_three, M3, A_succ, B_succ] <;> ring

theorem A090390_eq (n : ℕ) : A090390 n = SqrtTwoOrbit.A n ^ 2 := by
  simp [A090390, vM_eq]

/-! ### A coprime splitting -/

/-- A078522's definition: numbers `k` with `(k + 1)(2k + 1)` a perfect square. -/
def A078522Set : Set ℤ := {k | 0 ≤ k ∧ ∃ m, (k + 1) * (2 * k + 1) = m ^ 2}

/-- A078522 (offset 1). -/
def A078522 (n : ℕ) : ℤ := B (2 * n - 1) ^ 2 - 1

theorem A078522_enumerates : Enumerates A078522 1 A078522Set := by
  have e : ∀ n, A078522 (n + 1) = B (2 * n + 1) ^ 2 - 1 := fun n => by
    show B (2 * (n + 1) - 1) ^ 2 - 1 = _
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  refine ⟨fun a b hab => ?_, fun k => ⟨?_, ?_⟩⟩
  · simp only [e]
    have := B_odd_mono hab
    have := B_odd_pos a
    simp only at *
    nlinarith
  · rintro ⟨hk, m, hm⟩
    have hc : IsCoprime (k + 1) (2 * k + 1) := ⟨2, -1, by ring⟩
    obtain ⟨a, ha | ha⟩ := Int.sq_of_isCoprime hc hm
    · obtain ⟨b, hb | hb⟩ := Int.sq_of_isCoprime hc.symm (by rw [mul_comm]; exact hm)
      · have hp : Sol 2 (-1) (|b|, |a|) := ⟨abs_pos.mpr (by rintro rfl; nlinarith), abs_nonneg _,
          by show |b| ^ 2 - 2 * |a| ^ 2 = -1; rw [sq_abs, sq_abs]; linarith⟩
        obtain ⟨j, hj⟩ := (odd_sol_iff _).mp hp
        refine ⟨j, ?_⟩
        rw [e, show B (2 * j + 1) = |a| by rw [B, hj], sq_abs]; linarith
      · nlinarith [sq_nonneg b]
    · nlinarith [sq_nonneg a]
  · rintro ⟨n, rfl⟩
    rw [e]
    have hn := norm_odd n
    refine ⟨by nlinarith, B (2 * n + 1) * SqrtTwoOrbit.A (2 * n + 1), ?_⟩
    linear_combination (-(B (2 * n + 1)) ^ 2) * hn

/-! ### A finite exceptional set -/

lemma sq_eq_two_sq {x y : ℤ} (h : x ^ 2 = 2 * y ^ 2) : x = 0 := by
  by_contra hx
  have hy : y ≠ 0 := by rintro rfl; simp at h; exact hx h
  apply irrational_sqrt_two
  refine ⟨(|x| : ℚ) / |y|, ?_⟩
  push_cast
  symm
  rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity), div_mul_div_comm,
    ← sq, ← sq, sq_abs, sq_abs, eq_div_iff (by positivity)]
  exact_mod_cast h.symm

/-- A055792's definition: `a` and `⌊a/2⌋` both squares. -/
def A055792Set : Set ℤ := {a | 0 ≤ a ∧ (∃ x, a = x ^ 2) ∧ ∃ y, a / 2 = y ^ 2}

/-- A055792 (offset 0): `0`, then `A_{2n}^2`. -/
def A055792 : ℕ → ℤ
  | 0 => 0
  | n + 1 => SqrtTwoOrbit.A (2 * n) ^ 2

theorem A055792_enumerates : Enumerates A055792 0 A055792Set := by
  have hpos := fun n => A_pos (2 * n)
  refine ⟨strictMono_nat_of_lt_succ fun n => ?_, fun a => ⟨?_, ?_⟩⟩
  · rcases n with _ | n
    · show (0 : ℤ) < SqrtTwoOrbit.A (2 * 0) ^ 2; exact pow_pos (hpos 0) 2
    · show SqrtTwoOrbit.A (2 * n) ^ 2 < SqrtTwoOrbit.A (2 * (n + 1)) ^ 2
      have := A_even_mono (Nat.lt_succ_self n)
      simp only at this
      nlinarith [hpos n]
  · rintro ⟨ha, ⟨x, rfl⟩, y, hy⟩
    have hdiv := Int.ediv_add_emod (x ^ 2) 2
    rcases Int.emod_two_eq_zero_or_one (x ^ 2) with hr | hr
    · rw [hr, hy] at hdiv
      have := sq_eq_two_sq (x := x) (y := y) (by linarith)
      exact ⟨0, by simp [A055792, this]⟩
    · rw [hr, hy] at hdiv
      have hx : x ≠ 0 := by
        rintro rfl
        have : (2 : ℤ) ∣ 1 := ⟨-y ^ 2, by linarith⟩
        norm_num at this
      have hp : Sol 2 1 (|x|, |y|) := ⟨abs_pos.mpr hx, abs_nonneg _,
        by show |x| ^ 2 - 2 * |y| ^ 2 = 1; rw [sq_abs, sq_abs]; linarith⟩
      obtain ⟨j, hj⟩ := (even_sol_iff _).mp hp
      exact ⟨j + 1, by show SqrtTwoOrbit.A (2 * j) ^ 2 = _; rw [SqrtTwoOrbit.A, hj, sq_abs]⟩
  · rintro ⟨n, rfl⟩
    rcases n with _ | n
    · exact ⟨le_rfl, ⟨0, by simp [A055792]⟩, 0, by simp [A055792]⟩
    · show 0 ≤ SqrtTwoOrbit.A (2 * n) ^ 2 ∧ (∃ x, SqrtTwoOrbit.A (2 * n) ^ 2 = x ^ 2) ∧ ∃ y, SqrtTwoOrbit.A (2 * n) ^ 2 / 2 = y ^ 2
      refine ⟨sq_nonneg _, ⟨_, rfl⟩, B (2 * n), ?_⟩
      have := norm_even n
      omega

/-! ### A residue filter -/

lemma A_mod4 (i : ℕ) : SqrtTwoOrbit.A (4 * i) % 4 = 1 ∧ SqrtTwoOrbit.A (4 * i + 2) % 4 = 3 := by
  induction i with
  | zero => decide
  | succ i ih =>
    have h1 := A_rec2 (4 * i)
    have h2 := A_rec2 (4 * i + 2)
    rw [show 4 * i + 2 + 2 = 4 * i + 4 by ring] at h2
    rw [show 4 * (i + 1) + 2 = 4 * i + 2 + 4 by ring, show 4 * (i + 1) = 4 * i + 4 by ring]
    omega

/-- A046176's definition: indices `k ≥ 1` of squares that are hexagonal, `k^2 = m(2m - 1)`,
`m ≥ 1`. -/
def A046176Set : Set ℤ := {k | 1 ≤ k ∧ ∃ m, 1 ≤ m ∧ k ^ 2 = m * (2 * m - 1)}

/-- A046176 (offset 1): `B_{4n-2}/2`. -/
def A046176 (n : ℕ) : ℤ := B (4 * n - 2) / 2

theorem A046176_enumerates : Enumerates A046176 1 A046176Set := by
  have e : ∀ n, A046176 (n + 1) = B (2 * (2 * n + 1)) / 2 := fun n => by
    show B (4 * (n + 1) - 2) / 2 = _
    rw [show 4 * (n + 1) - 2 = 2 * (2 * n + 1) by omega]
  have hev := fun n => B_even_even n
  refine ⟨fun a b hab => ?_, fun k => ⟨?_, ?_⟩⟩
  · simp only [e]
    have := B_even_mono (show 2 * a + 1 < 2 * b + 1 by omega)
    obtain ⟨c, hc⟩ := hev (2 * a + 1)
    obtain ⟨d, hd⟩ := hev (2 * b + 1)
    simp only at this
    rw [hc, hd] at this ⊢; omega
  · rintro ⟨hk, m, hm, h⟩
    have hp : Sol 2 1 (4 * m - 1, 2 * k) := ⟨by omega, by omega,
      by show (4 * m - 1) ^ 2 - 2 * (2 * k) ^ 2 = 1; linear_combination (-8) * h⟩
    obtain ⟨j, hj⟩ := (even_sol_iff _).mp hp
    have h1 : SqrtTwoOrbit.A (2 * j) = 4 * m - 1 := by rw [SqrtTwoOrbit.A, hj]
    have h2 : B (2 * j) = 2 * k := by rw [B, hj]
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · have := (A_mod4 i).1
      rw [show 2 * (2 * i) = 4 * i by ring] at h1; omega
    · refine ⟨i, ?_⟩
      rw [e, h2]; omega
  · rintro ⟨n, rfl⟩
    rw [e]
    obtain ⟨c, hc⟩ := hev (2 * n + 1)
    have hn := norm_even (2 * n + 1)
    have h3 := (A_mod4 n).2
    rw [show 4 * n + 2 = 2 * (2 * n + 1) by ring] at h3
    have hA := A_pos (2 * (2 * n + 1))
    have hBpos : 0 < B (2 * (2 * n + 1)) := by
      rcases (B_nonneg (2 * (2 * n + 1))).lt_or_eq with h | h
      · exact h
      · rw [← h] at hn
        have : SqrtTwoOrbit.A (2 * (2 * n + 1)) = 1 := by nlinarith
        omega
    rw [hc] at hn hBpos ⊢
    refine ⟨by omega, (SqrtTwoOrbit.A (2 * (2 * n + 1)) + 1) / 4, by omega, ?_⟩
    have h4 : SqrtTwoOrbit.A (2 * (2 * n + 1)) = 4 * ((SqrtTwoOrbit.A (2 * (2 * n + 1)) + 1) / 4) - 1 := by omega
    rw [show 2 * c / 2 = c by omega]
    rw [h4] at hn
    linarith

/-! ### Squares of entries, read as sets -/

/-- A008843's definition: "`x^2` such that `x^2 - 2y^2 = -1` for some `y`" (squares of the NSW
numbers A002315). -/
def A008843Set : Set ℤ := {v | ∃ x y : ℤ, 0 < x ∧ v = x ^ 2 ∧ x ^ 2 - 2 * y ^ 2 = -1}

/-- A008843 (offset 0). -/
def A008843 (n : ℕ) : ℤ := SqrtTwoOrbit.A (2 * n + 1) ^ 2

theorem A008843_enumerates : Enumerates A008843 0 A008843Set := by
  refine ⟨fun a b hab => ?_, fun v => ⟨?_, ?_⟩⟩
  · have := A_odd_mono hab
    have := A_pos (2 * a + 1)
    simp only [A008843, add_zero] at *
    nlinarith
  · rintro ⟨x, y, hx, rfl, h⟩
    have hp : Sol 2 (-1) (x, |y|) := ⟨hx, abs_nonneg _, by
      show x ^ 2 - 2 * |y| ^ 2 = -1; rw [sq_abs]; exact h⟩
    obtain ⟨j, hj⟩ := (odd_sol_iff _).mp hp
    exact ⟨j, by simp only [A008843, add_zero]; rw [SqrtTwoOrbit.A, hj]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨_, B (2 * n + 1), A_pos _, by simp [A008843], norm_odd n⟩

/-- A008843 is the square of A002315, as its name says. -/
theorem A008843_A002315 (n : ℕ) : A008843 n = A002315 n ^ 2 := by
  rw [A008843, A002315_eq]

/-- A008844's definition: "`y^2` such that `x^2 - 2y^2 = -1` for some `x`" (squares of A001653). -/
def A008844Set : Set ℤ := {v | ∃ x y : ℤ, 0 ≤ y ∧ v = y ^ 2 ∧ x ^ 2 - 2 * y ^ 2 = -1}

/-- A008844 (offset 0). -/
def A008844 (n : ℕ) : ℤ := B (2 * n + 1) ^ 2

theorem A008844_enumerates : Enumerates A008844 0 A008844Set := by
  refine ⟨fun a b hab => ?_, fun v => ⟨?_, ?_⟩⟩
  · have := B_odd_mono hab
    have := B_odd_pos a
    simp only [A008844, add_zero] at *
    nlinarith
  · rintro ⟨x, y, hy, rfl, h⟩
    have hx : x ≠ 0 := by
      rintro rfl
      have : (2 : ℤ) ∣ 1 := ⟨y ^ 2, by linarith⟩
      norm_num at this
    have hp : Sol 2 (-1) (|x|, y) := ⟨abs_pos.mpr hx, hy, by
      show |x| ^ 2 - 2 * y ^ 2 = -1; rw [sq_abs]; exact h⟩
    obtain ⟨j, hj⟩ := (odd_sol_iff _).mp hp
    exact ⟨j, by simp only [A008844, add_zero]; rw [B, hj]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨SqrtTwoOrbit.A (2 * n + 1), _, B_nonneg _, by simp [A008844], norm_odd n⟩

/-- A008844 is the square of A001653, shifted by its offset. -/
theorem A008844_A001653 (n : ℕ) : A008844 n = SqrtTwoOrbit.A001653 (n + 1) ^ 2 := by
  simp only [A008844, SqrtTwoOrbit.A001653, show 2 * (n + 1) - 1 = 2 * n + 1 by omega]

end PerfectPower.SqrtTwoBatch
