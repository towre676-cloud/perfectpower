import PerfectPower.SquareTriangular

/-!
# One orbit behind thirteen OEIS entries: `(1 + √2)^k`

Write `(1 + √2)^k = A_k + B_k √2`.  The even powers are the orbit of `(1, 0)` on the norm-`+1`
equation `x^2 - 2y^2 = 1`, the odd powers the orbit of `(1, 1)` on `x^2 - 2y^2 = -1`, both under the
unit `3 + 2√2` (`even_sol_iff`, `odd_sol_iff`: nothing else solves either equation).

Each entry below is defined **from the text of its OEIS entry** (the official `oeisdata` export,
see `data/oeis/`), with the entry's offset, and proved equal to an exact coordinate of the orbit:

| entry | OEIS definition (`%N`, offset) | coordinate |
|---|---|---|
| A000129 | Pell numbers, `a(n) = 2a(n-1) + a(n-2)`, `0, 1` (offset 0) | `B_n` |
| A001541 | `a(n) = 6a(n-1) - a(n-2)`, `1, 3` (offset 0) | `A_{2n}` |
| A001542 | `a(n) = 6a(n-1) - a(n-2)`, `0, 2` (offset 0) | `B_{2n}` |
| A001109 | `a(n)^2` triangular; `6, -1` with `0, 1` (offset 0) | `B_{2n} / 2` |
| A001108 | `a(n)`-th triangular number a square; `a(n+1) = 6a(n) - a(n-1) + 2`, `0, 1` | `(A_{2n} - 1)/2` |
| A001652 | `a(n) = 6a(n-1) - a(n-2) + 2`, `0, 3` (offset 0) | `(A_{2n+1} - 1)/2` |
| A002315 | NSW numbers, `6, -1` (initial `1, 7` from its terms) | `A_{2n+1}` |
| A005319 | `a(n) = 6a(n-1) - a(n-2)` (initial `0, 4` from its terms) | `2 B_{2n}` |
| A001110 | square triangular numbers (offset 0) | `(B_{2n}/2)^2` |
| A001653 | `k` with `2k^2 - 1` a square (offset 1) | `B_{2n-1}` |
| A055997 | `k` with `k(k-1)/2` a square (offset 1) | `(A_{2n-2} + 1)/2` |
| A084703 | squares `k` with `2k + 1` a square (offset 0) | `B_{2n}^2` |
| A075870 | `k` with `2k^2 - 4` a square (offset 1) | `2 B_{2n-1}` |

Recurrence definitions are proved by `rec_unique` (same recurrence, same initial values).  Set
definitions are proved as **increasing enumerations** (`Enumerates`): the coordinate is strictly
increasing from the offset and its values are exactly the set.  The domain conventions (which
`k`, whether `0` is listed) are the entries' own, read from their offsets and first terms.

`pell_count`: the Pell numbers are the union of **two** observed orbits (even and odd powers),
disjoint by parity, so `Observation.observed_count` gives
`#{Pell numbers ≤ N} = 2 log N / log(3 + 2√2) + O(1) = log N / log(1 + √2) + O(1)`.
-/

namespace PerfectPower.SqrtTwoOrbit

open PerfectPower PellExact Finset Observation
open scoped Classical

/-! ### The orbit -/

/-- `(1 + √2)^k = A_k + B_k √2`. -/
def AB : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 => ((AB k).1 + 2 * (AB k).2, (AB k).1 + (AB k).2)

/-- `A_k`. -/
def A (k : ℕ) : ℤ := (AB k).1
/-- `B_k`. -/
def B (k : ℕ) : ℤ := (AB k).2

lemma A_succ (k : ℕ) : A (k + 1) = A k + 2 * B k := rfl
lemma B_succ (k : ℕ) : B (k + 1) = A k + B k := rfl

lemma A_rec (k : ℕ) : A (k + 2) = 2 * A (k + 1) + A k := by
  simp only [A_succ, B_succ]; ring
lemma B_rec (k : ℕ) : B (k + 2) = 2 * B (k + 1) + B k := by
  simp only [A_succ, B_succ]; ring

lemma A_rec2 (k : ℕ) : A (k + 4) = 6 * A (k + 2) - A k := by
  simp only [A_succ, B_succ]; ring
lemma B_rec2 (k : ℕ) : B (k + 4) = 6 * B (k + 2) - B k := by
  simp only [A_succ, B_succ]; ring

lemma norm_AB (k : ℕ) : A k ^ 2 - 2 * B k ^ 2 = (-1) ^ k := by
  induction k with
  | zero => simp [A, B, AB]
  | succ k ih => rw [A_succ, B_succ, pow_succ]; linear_combination (-1 : ℤ) * ih

lemma AB_pos (k : ℕ) : 0 < A k ∧ 0 ≤ B k := by
  induction k with
  | zero => simp [A, B, AB]
  | succ k ih => rw [A_succ, B_succ]; omega

lemma A_pos (k : ℕ) : 0 < A k := (AB_pos k).1
lemma B_nonneg (k : ℕ) : 0 ≤ B k := (AB_pos k).2

lemma B_mono : StrictMono (fun k => B (k + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  show B (k + 1) < B (k + 1 + 1)
  rw [B_succ (k + 1)]; have := A_pos (k + 1); omega

lemma A_step (k : ℕ) : A k < A (k + 2) := by
  rw [A_rec]; have := A_pos (k + 1); omega

lemma B_step2 (k : ℕ) : B k < B (k + 2) := by
  rw [B_rec]; have : 0 < B (k + 1) := by
    rw [B_succ]; have := A_pos k; have := B_nonneg k; omega
  omega

lemma parity (k : ℕ) : A k % 2 = 1 ∧ B k % 2 = (k : ℤ) % 2 := by
  induction k with
  | zero => simp [A, B, AB]
  | succ k ih => rw [A_succ, B_succ]; push_cast; omega

lemma B_parity (k : ℕ) : B k % 2 = (k : ℤ) % 2 := (parity k).2

lemma norm_even (n : ℕ) : A (2 * n) ^ 2 - 2 * B (2 * n) ^ 2 = 1 := by
  have := norm_AB (2 * n)
  rwa [show ((-1 : ℤ)) ^ (2 * n) = 1 by rw [pow_mul]; norm_num] at this

lemma norm_odd (n : ℕ) : A (2 * n + 1) ^ 2 - 2 * B (2 * n + 1) ^ 2 = -1 := by
  have := norm_AB (2 * n + 1)
  rwa [show ((-1 : ℤ)) ^ (2 * n + 1) = -1 by rw [pow_succ, pow_mul]; norm_num] at this

/-! ### The two orbits of `3 + 2√2`, and completeness -/

lemma unit2 : (3 : ℤ) ^ 2 - 2 * 2 ^ 2 = 1 := by norm_num

lemma orbit_even (j : ℕ) : unitOrbit 2 3 2 (1, 0) j = AB (2 * j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [orbit_succ, ih, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    simp only [unitAct, AB]
    ext <;> ring

lemma orbit_odd (j : ℕ) : unitOrbit 2 3 2 (1, 1) j = AB (2 * j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [orbit_succ, ih, show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring]
    simp only [unitAct, AB]
    ext <;> ring

/-- **Every positive solution of `x^2 - 2y^2 = 1` is an even power.** -/
theorem even_sol_iff (p : ℤ × ℤ) : Sol 2 1 p ↔ ∃ j, AB (2 * j) = p := by
  constructor
  · intro hp
    obtain ⟨ρ, j, hρ, hj⟩ := exists_root (D := 2) (u := 3) (v := 2) (Δ := 1) (by norm_num)
      (by norm_num) (by norm_num) unit2 p.1 p rfl hp
    have hbox := root_in_box (by norm_num) (by norm_num) (by norm_num) unit2 hρ
    obtain ⟨⟨h1, h2, h3⟩, hpred⟩ := hρ
    norm_num at hbox
    have hY : ρ.2 = 0 ∨ ρ.2 = 1 ∨ ρ.2 = 2 := by
      have : ρ.2 ≤ 2 := by nlinarith
      omega
    rcases hY with hY | hY | hY
    · have hX : ρ.1 = 1 := by rw [hY] at h3; nlinarith
      refine ⟨j, ?_⟩
      rw [← orbit_even, ← hj]
      congr 1
      exact (Prod.ext hX hY).symm
    · exfalso; rw [hY] at h3
      have : ρ.1 ≤ 1 ∨ 2 ≤ ρ.1 := by omega
      rcases this with h | h <;> nlinarith
    · exfalso
      have hX : ρ.1 = 3 := by rw [hY] at h3; nlinarith
      apply hpred
      simp only [pred, hX, hY]
      exact ⟨by norm_num, by norm_num, by norm_num⟩
  · rintro ⟨j, rfl⟩
    exact ⟨A_pos _, B_nonneg _, norm_even j⟩

/-- **Every positive solution of `x^2 - 2y^2 = -1` is an odd power.** -/
theorem odd_sol_iff (p : ℤ × ℤ) : Sol 2 (-1) p ↔ ∃ j, AB (2 * j + 1) = p := by
  constructor
  · intro hp
    obtain ⟨ρ, j, hρ, hj⟩ := exists_root (D := 2) (u := 3) (v := 2) (Δ := -1) (by norm_num)
      (by norm_num) (by norm_num) unit2 p.1 p rfl hp
    have hbox := root_in_box (by norm_num) (by norm_num) (by norm_num) unit2 hρ
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := hρ
    norm_num at hbox
    have hY : ρ.2 = 0 ∨ ρ.2 = 1 ∨ ρ.2 = 2 := by
      have : ρ.2 ≤ 2 := by nlinarith
      omega
    rcases hY with hY | hY | hY
    · exfalso; rw [hY] at h3; nlinarith
    · have hX : ρ.1 = 1 := by rw [hY] at h3; nlinarith
      refine ⟨j, ?_⟩
      rw [← orbit_odd, ← hj]
      congr 1
      exact (Prod.ext hX hY).symm
    · exfalso; rw [hY] at h3
      have : ρ.1 ≤ 2 ∨ 3 ≤ ρ.1 := by omega
      rcases this with h | h <;> nlinarith
  · rintro ⟨j, rfl⟩
    exact ⟨A_pos _, B_nonneg _, norm_odd j⟩

/-! ### Recurrence definitions -/

/-- Two sequences with the same recurrence and the same two initial values agree. -/
lemma rec_unique {f g : ℕ → ℤ} (c d e : ℤ) (hf : ∀ n, f (n + 2) = c * f (n + 1) + d * f n + e)
    (hg : ∀ n, g (n + 2) = c * g (n + 1) + d * g n + e) (h0 : f 0 = g 0) (h1 : f 1 = g 1) :
    ∀ n, f n = g n := by
  have key : ∀ n, f n = g n ∧ f (n + 1) = g (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih => exact ⟨ih.2, by rw [hf, hg, ih.1, ih.2]⟩
  exact fun n => (key n).1

/-- A000129, Pell numbers: `a(0) = 0, a(1) = 1`; `a(n) = 2 a(n-1) + a(n-2)`. -/
def A000129 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * A000129 (n + 1) + A000129 n

/-- A001541: `a(0) = 1, a(1) = 3`; `a(n) = 6 a(n-1) - a(n-2)`. -/
def A001541 : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | n + 2 => 6 * A001541 (n + 1) - A001541 n

/-- A001542: `a(n) = 6 a(n-1) - a(n-2)`, `a(0) = 0`, `a(1) = 2`. -/
def A001542 : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | n + 2 => 6 * A001542 (n + 1) - A001542 n

/-- A001109: `a(n) = 6 a(n-1) - a(n-2)` with `a(0) = 0`, `a(1) = 1`. -/
def A001109 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 6 * A001109 (n + 1) - A001109 n

/-- A001108: `a(n+1) = 6 a(n) - a(n-1) + 2`, `a(0) = 0`, `a(1) = 1`. -/
def A001108 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 6 * A001108 (n + 1) - A001108 n + 2

/-- A001652: `a(n) = 6 a(n-1) - a(n-2) + 2` with `a(0) = 0`, `a(1) = 3`. -/
def A001652 : ℕ → ℤ
  | 0 => 0
  | 1 => 3
  | n + 2 => 6 * A001652 (n + 1) - A001652 n + 2

/-- A002315, NSW numbers: `a(n) = 6 a(n-1) - a(n-2)`; initial `1, 7` from the entry's terms. -/
def A002315 : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | n + 2 => 6 * A002315 (n + 1) - A002315 n

/-- A005319: `a(n) = 6 a(n-1) - a(n-2)`; initial `0, 4` from the entry's terms. -/
def A005319 : ℕ → ℤ
  | 0 => 0
  | 1 => 4
  | n + 2 => 6 * A005319 (n + 1) - A005319 n

theorem A000129_eq : ∀ n, A000129 n = B n :=
  rec_unique 2 1 0 (fun n => by simp [A000129]) (fun n => by rw [B_rec]; ring) rfl rfl

theorem A001541_eq : ∀ n, A001541 n = A (2 * n) :=
  rec_unique 6 (-1) 0 (fun n => by simp [A001541]; ring)
    (fun n => by rw [show 2 * (n + 2) = 2 * n + 4 by ring, A_rec2,
      show 2 * (n + 1) = 2 * n + 2 by ring]; ring) rfl rfl

theorem A001542_eq : ∀ n, A001542 n = B (2 * n) :=
  rec_unique 6 (-1) 0 (fun n => by simp [A001542]; ring)
    (fun n => by rw [show 2 * (n + 2) = 2 * n + 4 by ring, B_rec2,
      show 2 * (n + 1) = 2 * n + 2 by ring]; ring) rfl rfl

theorem A001109_eq : ∀ n, 2 * A001109 n = B (2 * n) :=
  rec_unique 6 (-1) 0 (fun n => by simp [A001109]; ring)
    (fun n => by rw [show 2 * (n + 2) = 2 * n + 4 by ring, B_rec2,
      show 2 * (n + 1) = 2 * n + 2 by ring]; ring) rfl rfl

theorem A001108_eq : ∀ n, 2 * A001108 n + 1 = A (2 * n) :=
  rec_unique 6 (-1) 0 (fun n => by simp [A001108]; ring)
    (fun n => by rw [show 2 * (n + 2) = 2 * n + 4 by ring, A_rec2,
      show 2 * (n + 1) = 2 * n + 2 by ring]; ring) rfl rfl

theorem A001652_eq : ∀ n, 2 * A001652 n + 1 = A (2 * n + 1) :=
  rec_unique 6 (-1) 0 (fun n => by simp [A001652]; ring)
    (fun n => by rw [show 2 * (n + 2) + 1 = 2 * n + 1 + 4 by ring, A_rec2,
      show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring]; ring) rfl rfl

theorem A002315_eq : ∀ n, A002315 n = A (2 * n + 1) :=
  rec_unique 6 (-1) 0 (fun n => by simp [A002315]; ring)
    (fun n => by rw [show 2 * (n + 2) + 1 = 2 * n + 1 + 4 by ring, A_rec2,
      show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring]; ring) rfl rfl

theorem A005319_eq : ∀ n, A005319 n = 2 * B (2 * n) :=
  rec_unique 6 (-1) 0 (fun n => by simp [A005319]; ring)
    (fun n => by rw [show 2 * (n + 2) = 2 * n + 4 by ring, B_rec2,
      show 2 * (n + 1) = 2 * n + 2 by ring]; ring) rfl rfl

/-! ### Set definitions, as increasing enumerations -/

/-- `a(n)`, `n ≥ off`, lists `S` in increasing order. -/
def Enumerates (a : ℕ → ℤ) (off : ℕ) (S : Set ℤ) : Prop :=
  StrictMono (fun n => a (n + off)) ∧ ∀ v, v ∈ S ↔ ∃ n, a (n + off) = v

lemma B_even_mono : StrictMono (fun n => B (2 * n)) :=
  strictMono_nat_of_lt_succ fun n => by
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]; exact B_step2 _

lemma B_odd_mono : StrictMono (fun n => B (2 * n + 1)) :=
  strictMono_nat_of_lt_succ fun n => by
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring]; exact B_step2 _

lemma A_even_mono : StrictMono (fun n => A (2 * n)) :=
  strictMono_nat_of_lt_succ fun n => by
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]; exact A_step _

lemma B_even_even (n : ℕ) : 2 ∣ B (2 * n) := by
  have := B_parity (2 * n); push_cast at this; omega

lemma A_even_odd (n : ℕ) : A (2 * n) % 2 = 1 := (parity _).1

lemma key_even (a b : ℤ) (h : (2 * a + 1) ^ 2 - 2 * (2 * b) ^ 2 = 1) : 2 * b ^ 2 = a * (a + 1) := by
  have h4 : 4 * (2 * b ^ 2) = 4 * (a * (a + 1)) := by linear_combination (-1 : ℤ) * h
  exact mul_left_cancel₀ (by norm_num) h4

/-- Square triangular numbers (A001110's definition): `t^2` equal to some `u(u+1)/2`. -/
def SqTriZ : Set ℤ := {v | ∃ t, v = t ^ 2 ∧ ∃ u, 0 ≤ u ∧ 2 * v = u * (u + 1)}

/-- A001110, as the increasing enumeration of square triangular numbers from offset 0. -/
def A001110 (n : ℕ) : ℤ := (B (2 * n) / 2) ^ 2

theorem A001110_enumerates : Enumerates A001110 0 SqTriZ := by
  have hB : ∀ n, 2 * (B (2 * n) / 2) = B (2 * n) := fun n => Int.mul_ediv_cancel' (B_even_even n)
  refine ⟨fun a b hab => ?_, fun v => ⟨?_, ?_⟩⟩
  · show A001110 (a + 0) < A001110 (b + 0)
    simp only [add_zero, A001110]
    have h := B_even_mono hab
    simp only at h
    have h0 := B_nonneg (2 * a)
    have := hB a; have := hB b
    have : B (2 * a) / 2 < B (2 * b) / 2 := by omega
    exact pow_lt_pow_left₀ this (by omega) two_ne_zero
  · rintro ⟨t, rfl, u, hu, htu⟩
    have hp : Sol 2 1 (2 * u + 1, 2 * |t|) := ⟨by show (0 : ℤ) < 2 * u + 1; omega,
      by show (0 : ℤ) ≤ 2 * |t|; positivity, by
      show (2 * u + 1) ^ 2 - 2 * (2 * |t|) ^ 2 = 1
      rw [mul_pow, sq_abs]; linear_combination (-4) * htu⟩
    obtain ⟨j, hj⟩ := (even_sol_iff _).mp hp
    refine ⟨j, ?_⟩
    simp only [add_zero, A001110]
    have hBj : B (2 * j) = 2 * |t| := by rw [B, hj]
    rw [hBj, Int.mul_ediv_cancel_left _ two_ne_zero, sq_abs]
  · rintro ⟨n, rfl⟩
    simp only [add_zero, A001110]
    refine ⟨B (2 * n) / 2, rfl, (A (2 * n) - 1) / 2, ?_, ?_⟩
    · have := A_pos (2 * n); omega
    · have hA := A_even_odd n
      have ha : 2 * ((A (2 * n) - 1) / 2) + 1 = A (2 * n) := by omega
      exact key_even _ _ (by rw [ha, hB]; exact norm_even n)

/-- A001653's definition: numbers `k` with `2k^2 - 1` a square. -/
def A001653Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x, x ^ 2 = 2 * k ^ 2 - 1}

/-- A001653 from offset 1: `a(n) = B_{2n-1}`. -/
def A001653 (n : ℕ) : ℤ := B (2 * n - 1)

theorem A001653_enumerates : Enumerates A001653 1 A001653Set := by
  have e : ∀ n, A001653 (n + 1) = B (2 * n + 1) := fun n => by
    show B (2 * (n + 1) - 1) = B (2 * n + 1)
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  refine ⟨fun a b hab => by simp only [e]; exact B_odd_mono hab, fun k => ⟨?_, ?_⟩⟩
  · rintro ⟨hk, x, hx⟩
    have hp : Sol 2 (-1) (|x|, k) := ⟨by
      rcases (abs_nonneg x).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← sq_abs, ← h] at hx
        have : (2 : ℤ) ∣ 1 := ⟨k ^ 2, by linarith⟩
        norm_num at this, hk, by show |x| ^ 2 - 2 * k ^ 2 = -1; rw [sq_abs]; linarith⟩
    obtain ⟨j, hj⟩ := (odd_sol_iff _).mp hp
    exact ⟨j, by rw [e, B, hj]⟩
  · rintro ⟨n, rfl⟩
    rw [e]
    refine ⟨B_nonneg _, A (2 * n + 1), ?_⟩
    have := norm_odd n
    linarith

/-- A075870's definition: numbers `k` with `2k^2 - 4` a square. -/
def A075870Set : Set ℤ := {k | 0 ≤ k ∧ ∃ x, x ^ 2 = 2 * k ^ 2 - 4}

/-- A075870 from offset 1: `a(n) = 2 B_{2n-1}`. -/
def A075870 (n : ℕ) : ℤ := 2 * B (2 * n - 1)

theorem A075870_enumerates : Enumerates A075870 1 A075870Set := by
  have e : ∀ n, A075870 (n + 1) = 2 * B (2 * n + 1) := fun n => by
    show 2 * B (2 * (n + 1) - 1) = 2 * B (2 * n + 1)
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  refine ⟨fun a b hab => by
    simp only [e]; have := B_odd_mono hab; simp only at this; omega, fun k => ⟨?_, ?_⟩⟩
  · rintro ⟨hk, x, hx⟩
    -- x and k are even: x = 2x', k = 2k', and x'^2 = 2k'^2 - 1
    have hx2 : 2 ∣ x := by
      rcases Int.emod_two_eq_zero_or_one x with h | h
      · exact Int.dvd_of_emod_eq_zero h
      · exfalso
        obtain ⟨c, hc⟩ : ∃ c, x = 2 * c + 1 := ⟨x / 2, by omega⟩
        rw [hc] at hx
        have : (2 * c + 1) ^ 2 % 2 = (2 * k ^ 2 - 4) % 2 := by rw [hx]
        ring_nf at this; omega
    obtain ⟨x', rfl⟩ := hx2
    have hk2 : 2 ∣ k := by
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · exact Int.dvd_of_emod_eq_zero h
      · exfalso
        obtain ⟨c, hc⟩ : ∃ c, k = 2 * c + 1 := ⟨k / 2, by omega⟩
        rw [hc] at hx
        have : (2 * x') ^ 2 % 4 = (2 * (2 * c + 1) ^ 2 - 4) % 4 := by rw [hx]
        ring_nf at this; omega
    obtain ⟨k', rfl⟩ := hk2
    obtain ⟨n, hn⟩ := A001653_enumerates.2 k' |>.mp ⟨by omega, x', by linarith⟩
    refine ⟨n, ?_⟩
    rw [e]; rw [A001653] at hn; simp only [show 2 * (n + 1) - 1 = 2 * n + 1 by omega] at hn
    rw [hn]
  · rintro ⟨n, rfl⟩
    rw [e]
    refine ⟨by have := B_nonneg (2 * n + 1); omega, 2 * A (2 * n + 1), ?_⟩
    have := norm_odd n
    linarith

/-- A055997's definition: numbers `k ≥ 1` with `k(k-1)/2` a square. -/
def A055997Set : Set ℤ := {k | 1 ≤ k ∧ ∃ t, k * (k - 1) = 2 * t ^ 2}

/-- A055997 from offset 1: `a(n) = (A_{2n-2} + 1)/2`. -/
def A055997 (n : ℕ) : ℤ := (A (2 * n - 2) + 1) / 2

theorem A055997_enumerates : Enumerates A055997 1 A055997Set := by
  have e : ∀ n, A055997 (n + 1) = (A (2 * n) + 1) / 2 := fun n => by
    show (A (2 * (n + 1) - 2) + 1) / 2 = (A (2 * n) + 1) / 2
    rw [show 2 * (n + 1) - 2 = 2 * n by omega]
  have hodd : ∀ n, (A (2 * n) + 1) / 2 * 2 = A (2 * n) + 1 := fun n => by
    have := A_even_odd n; omega
  refine ⟨fun a b hab => ?_, fun k => ⟨?_, ?_⟩⟩
  · simp only [e]; have := A_even_mono hab; simp only at this; have := hodd a; have := hodd b; omega
  · rintro ⟨hk, t, ht⟩
    have hp : Sol 2 1 (2 * k - 1, 2 * |t|) := ⟨by show (0 : ℤ) < 2 * k - 1; omega,
      by show (0 : ℤ) ≤ 2 * |t|; positivity, by
      show (2 * k - 1) ^ 2 - 2 * (2 * |t|) ^ 2 = 1
      rw [mul_pow, sq_abs]; linear_combination 4 * ht⟩
    obtain ⟨j, hj⟩ := (even_sol_iff _).mp hp
    refine ⟨j, ?_⟩
    rw [e, show A (2 * j) = 2 * k - 1 by rw [A, hj]]
    omega
  · rintro ⟨n, rfl⟩
    rw [e]
    have := hodd n; have hA := A_pos (2 * n)
    refine ⟨by omega, B (2 * n) / 2, ?_⟩
    have hB : 2 * (B (2 * n) / 2) = B (2 * n) := Int.mul_ediv_cancel' (B_even_even n)
    have ha : 2 * ((A (2 * n) + 1) / 2) - 1 = A (2 * n) := by omega
    have hn := norm_even n
    rw [← ha, ← hB] at hn
    have h4 : 4 * ((A (2 * n) + 1) / 2 * ((A (2 * n) + 1) / 2 - 1)) = 4 * (2 * (B (2 * n) / 2) ^ 2) := by
      linear_combination hn
    exact mul_left_cancel₀ (by norm_num) h4

/-- A084703's definition: squares `k` with `2k + 1` a square. -/
def A084703Set : Set ℤ := {k | ∃ t, k = t ^ 2 ∧ ∃ m, m ^ 2 = 2 * k + 1}

/-- A084703 from offset 0: `a(n) = B_{2n}^2`. -/
def A084703 (n : ℕ) : ℤ := B (2 * n) ^ 2

theorem A084703_enumerates : Enumerates A084703 0 A084703Set := by
  refine ⟨fun a b hab => ?_, fun k => ⟨?_, ?_⟩⟩
  · simp only [add_zero, A084703]
    exact pow_lt_pow_left₀ (B_even_mono hab) (B_nonneg _) two_ne_zero
  · rintro ⟨t, rfl, m, hm⟩
    have hp : Sol 2 1 (|m|, |t|) := ⟨by
      rcases (abs_nonneg m).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← sq_abs, ← h] at hm; nlinarith [sq_nonneg t], abs_nonneg _, by
      show |m| ^ 2 - 2 * |t| ^ 2 = 1
      rw [sq_abs, sq_abs]; linarith⟩
    obtain ⟨j, hj⟩ := (even_sol_iff _).mp hp
    refine ⟨j, ?_⟩
    simp only [add_zero, A084703]
    rw [show B (2 * j) = |t| by rw [B, hj], sq_abs]
  · rintro ⟨n, rfl⟩
    simp only [add_zero, A084703]
    refine ⟨B (2 * n), rfl, A (2 * n), ?_⟩
    have hn := norm_even n
    linarith

/-! ### Relations the entries state about each other, now theorems -/

/-- A002315's name: `a(n)^2 - 2 b(n)^2 = -1` with `b(n) = A001653(n+1)`. -/
theorem A002315_A001653 (n : ℕ) : A002315 n ^ 2 - 2 * A001653 (n + 1) ^ 2 = -1 := by
  rw [A002315_eq, A001653, show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  exact norm_odd n

/-- `A001541(n)^2 - 2 A001542(n)^2 = 1`, `A001542 = 2 A001109`, `A001110 = A001109^2`,
`2 A001108 + 1 = A001541`: the square triangular cluster. -/
theorem cluster (n : ℕ) :
    A001541 n ^ 2 - 2 * A001542 n ^ 2 = 1 ∧ A001542 n = 2 * A001109 n ∧
      A001110 n = A001109 n ^ 2 ∧ 2 * A001108 n + 1 = A001541 n ∧
      A000129 (2 * n) = A001542 n ∧ A000129 (2 * n + 1) = A001653 (n + 1) := by
  have hn := norm_even n
  refine ⟨by rw [A001541_eq, A001542_eq]; exact hn, by rw [A001542_eq, A001109_eq], ?_,
    by rw [A001108_eq, A001541_eq], by rw [A000129_eq, A001542_eq], ?_⟩
  · simp only [A001110, ← A001109_eq, Int.mul_ediv_cancel_left _ two_ne_zero]
  · rw [A000129_eq, A001653, show 2 * (n + 1) - 1 = 2 * n + 1 by omega]

/-! ### Counting the Pell numbers: two observed orbits -/

/-- The positive Pell numbers, as a set of naturals. -/
def PellSet : Set ℕ := {v | 1 ≤ v ∧ ∃ n, A000129 n = v}

lemma eps2 : eps 2 3 2 = eps 8 3 1 := by
  rw [SquareTriangular.eps_eq]
  simp only [eps]; push_cast; linarith

lemma B_bounds_odd (j : ℕ) : eps 8 3 1 ^ j / 2 ≤ (B (2 * j + 1) : ℝ) ∧
    (B (2 * j + 1) : ℝ) ≤ 3 * eps 8 3 1 ^ j := by
  have hb := orbit_fst_bracket (D := 2) (u := 3) (v := 2) (by norm_num) unit2 (by norm_num)
    (by norm_num) (1, 1) j
  rw [orbit_odd, eps2] at hb
  have he : eta 2 (1, 1) = 1 + Real.sqrt 2 := by simp [eta]
  have hb' : etaBar 2 (1, 1) = 1 - Real.sqrt 2 := by simp [etaBar]
  rw [he, hb'] at hb
  have hs1 : 1 ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have habs : |1 - Real.sqrt 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hpow : 1 ≤ eps 8 3 1 ^ j := one_le_pow₀ (by linarith [SquareTriangular.eps_ge])
  have hA' : ((AB (2 * j + 1)).1 : ℝ) = (A (2 * j + 1) : ℝ) := rfl
  rw [hA'] at hb
  have hab := abs_le.mp hb
  have hsl : eps 8 3 1 ^ j ≤ Real.sqrt 2 * eps 8 3 1 ^ j := by nlinarith
  have hsu : Real.sqrt 2 * eps 8 3 1 ^ j ≤ 3 / 2 * eps 8 3 1 ^ j := by nlinarith
  have hn := norm_odd j
  have hn' : (A (2 * j + 1) : ℝ) ^ 2 - 2 * (B (2 * j + 1) : ℝ) ^ 2 = -1 := by exact_mod_cast hn
  have hA : (1 : ℝ) ≤ A (2 * j + 1) := by exact_mod_cast A_pos (2 * j + 1)
  have hB0 : (0 : ℝ) ≤ B (2 * j + 1) := by exact_mod_cast B_nonneg (2 * j + 1)
  constructor <;> nlinarith

lemma B_bounds_even (j : ℕ) : eps 8 3 1 ^ j / 6 ≤ (B (2 * j + 2) : ℝ) ∧
    (B (2 * j + 2) : ℝ) ≤ eps 8 3 1 * eps 8 3 1 ^ j := by
  have h := A001542_eq (j + 1)
  have h2 := (cluster (j + 1)).2.1
  have hY : A001109 (j + 1) = (SquareTriangular.orb (j + 1)).2 := by
    have := rec_unique (f := A001109) (g := fun n => (SquareTriangular.orb n).2) 6 (-1) 0
      (fun n => by simp [A001109]; ring)
      (fun n => by
        simp only [SquareTriangular.orb_succ]; ring) rfl rfl (j + 1)
    exact this
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at h
  rw [← h, h2, hY]
  have := SquareTriangular.X_bounds j
  have := SquareTriangular.Y_bounds j
  push_cast
  constructor <;> nlinarith

theorem pell_count : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |((#{v ∈ Icc 1 N | v ∈ PellSet} : ℕ) : ℝ) - 2 * Real.log N / Real.log (3 + 2 * Real.sqrt 2)| ≤ K := by
  -- the two observations: odd powers `B_{2j+1}` and even powers `B_{2j+2}`
  let obs : Bool → ℕ → ℕ := fun b j => (B (2 * j + if b then 1 else 2)).toNat
  have hcast : ∀ b j, ((obs b j : ℕ) : ℤ) = B (2 * j + if b then 1 else 2) :=
    fun b j => Int.toNat_of_nonneg (B_nonneg _)
  have hreal : ∀ b j, ((obs b j : ℕ) : ℝ) = (B (2 * j + if b then 1 else 2) : ℝ) := by
    intro b j; rw [← hcast]; rfl
  have hε := SquareTriangular.eps_ge
  obtain ⟨K, hK⟩ := observed_count (Finset.univ : Finset Bool) obs (fun _ => eps 8 3 1)
    (fun _ => 1 / 6) (fun _ => 3 * eps 8 3 1) (fun _ _ => by linarith) (fun _ _ => by norm_num)
    (fun _ _ => by positivity)
    (fun b _ j => by
      rw [hreal]; cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]; have := (B_bounds_even j).1; linarith
      · simp only [↓reduceIte]; have := (B_bounds_odd j).1
        have : (0 : ℝ) ≤ eps 8 3 1 ^ j := by positivity
        linarith)
    (fun b _ j => by
      rw [hreal]; cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]; have := (B_bounds_even j).2
        have : (0 : ℝ) ≤ eps 8 3 1 ^ j := by positivity
        nlinarith
      · simp only [↓reduceIte]; have := (B_bounds_odd j).2
        have : (0 : ℝ) ≤ eps 8 3 1 ^ j := by positivity
        nlinarith)
    (fun _ => 1) (fun _ _ => one_pos) (fun _ _ => True) (fun _ _ _ => Iff.rfl)
    (fun b _ => by
      apply strictMono_nat_of_lt_succ
      intro j
      have key : ∀ c, B (2 * j + c) < B (2 * (j + 1) + c) := fun c => by
        rw [show 2 * (j + 1) + c = 2 * j + c + 2 by ring]; exact B_step2 _
      have h1 := hcast b j; have h2 := hcast b (j + 1); have := key (if b then 1 else 2)
      omega)
    0 (fun b _ c _ i j _ _ hij _ => by
      have h1 := hcast b i; have h2 := hcast c j
      have p1 := B_parity (2 * i + if b then 1 else 2)
      have p2 := B_parity (2 * j + if c then 1 else 2)
      cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
        push_cast at p1 p2 <;> omega)
    PellSet (fun v => by
      constructor
      · rintro ⟨hv, n, hn⟩
        rw [A000129_eq] at hn
        -- n ≥ 1 since B_0 = 0
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
          rcases Nat.eq_zero_or_pos n with h | h
          · subst h; simp [B, AB] at hn; omega
          · omega⟩
        rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
        · refine ⟨true, Finset.mem_univ _, j, trivial, ?_⟩
          have := hcast true j
          simp only [↓reduceIte] at this
          rw [show m + 1 = 2 * j + 1 by omega] at hn
          omega
        · refine ⟨false, Finset.mem_univ _, j, trivial, ?_⟩
          have := hcast false j
          simp only [Bool.false_eq_true, ↓reduceIte] at this
          rw [show m + 1 = 2 * j + 2 by omega] at hn
          omega
      · rintro ⟨b, -, j, -, rfl⟩
        have h := hcast b j
        refine ⟨?_, 2 * j + if b then 1 else 2, by rw [A000129_eq, h]⟩
        have : 0 < B (2 * j + if b then 1 else 2) := by
          cases b
          · show 0 < B (2 * j + 1 + 1)
            have := B_mono (show 0 < 2 * j + 1 by omega)
            simp only at this
            have h0 : B (0 + 1) = 1 := rfl
            rw [h0] at this; omega
          · show 0 < B (2 * j + 1)
            rcases Nat.eq_zero_or_pos j with h0 | h0
            · subst h0; decide
            · have := B_mono (show 0 < 2 * j by omega)
              simp only at this
              have h1 : B (0 + 1) = 1 := rfl
              rw [h1] at this; omega
        omega)
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  have hsum : (∑ ρ ∈ (Finset.univ : Finset Bool),
      (#((range ((fun _ => 1) ρ)).filter ((fun _ _ => True) ρ)) : ℝ) /
        ((((fun _ => 1) ρ : ℕ) : ℝ) * Real.log ((fun _ => eps 8 3 1) ρ))) =
      2 / Real.log (eps 8 3 1) := by
    simp [Finset.sum_const]; ring
  rw [hsum, SquareTriangular.eps_eq] at this
  have e : 2 * Real.log N / Real.log (3 + 2 * Real.sqrt 2) =
      2 / Real.log (3 + 2 * Real.sqrt 2) * Real.log N := by ring
  rw [e]; exact this

/-- `log(3 + 2√2) = 2 log(1 + √2)`: the Pell numbers count at the rate of `1 + √2`. -/
lemma log_eps_eq : Real.log (3 + 2 * Real.sqrt 2) = 2 * Real.log (1 + Real.sqrt 2) := by
  have h : (3 + 2 * Real.sqrt 2) = (1 + Real.sqrt 2) ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num); nlinarith
  rw [h, Real.log_pow]; norm_num

end PerfectPower.SqrtTwoOrbit
