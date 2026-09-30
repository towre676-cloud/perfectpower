import PerfectPower.QuadOrbit
import PerfectPower.Observation
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Real.GoldenRatio

/-!
# A second discriminant: `√5`, where the ring of integers is larger than `ℤ[√5]`

The natural orbit is `φ^n` in `ℤ[φ]`, `φ = (1 + √5)/2`:
`2 φ^n = L_n + F_n √5` (Lucas and Fibonacci numbers).  The engine works in `ℤ[√5]` with a unit of
norm `+1`; the smallest is `9 + 4√5 = φ^6`.  Seen from `ℤ[√5]`, the one `φ`-orbit therefore
splits into **six** seed orbits:
* three on `x^2 - 5y^2 = 4` (seeds `(L_0, F_0), (L_2, F_2), (L_4, F_4)`);
* three on `x^2 - 5y^2 = -4` (seeds `(L_1, F_1), (L_3, F_3), (L_5, F_5)`).

The seed lists are certified complete by `QuadOrbit.seedCheck` (`cert_pos`, `cert_neg`).

* `F` is Mathlib's `Nat.fib`, an independently written definition; `L` is A000032's recurrence.
* `pos_iff`, `neg_iff`: the positive solutions of `x^2 - 5y^2 = ±4` are exactly
  `(L_n, F_n)`, `n` even or odd.
* `fib_collision`: `F_i = F_j` only for `i = j` or `{i, j} = {1, 2}`.  The collision is the
  engine's `cross_collision` between `Δ = 4` (`(3, 1)`) and `Δ = -4` (`(1, 1)`); the index parity,
  that is the sign of the norm, repairs it (`fib_parity_inj`).
* `fib_count`: the Fibonacci numbers up to `N` number `log N / log φ + O(1)`.  This is
  `observed_count_eventually` with six orbits, rate `ε = φ^6`, and collisions only at the value `1`
  (`V₀ = 1`).
* `even_fib_count`: `F_n` is even iff `3 ∣ n`, a filter compiled from residues mod 2
  (`even_iff`); the even Fibonacci numbers number `log N / (3 log φ) + O(1)`.
-/

namespace PerfectPower.FibOrbit

open PerfectPower PellExact QuadOrbit Observation Finset
open scoped Classical

/-- Fibonacci numbers: Mathlib's `Nat.fib`, as integers (A000045). -/
def F (n : ℕ) : ℤ := (Nat.fib n : ℤ)

/-- Lucas numbers, A000032: `L(0) = 2`, `L(1) = 1`, `L(n) = L(n-1) + L(n-2)`. -/
def L : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => L (n + 1) + L n

lemma F_rec (n : ℕ) : F (n + 2) = F (n + 1) + F n := by
  simp only [F, Nat.fib_add_two]; push_cast; ring

lemma L_rec (n : ℕ) : L (n + 2) = L (n + 1) + L n := rfl

lemma F_zero : F 0 = 0 := by simp [F]
lemma F_one : F 1 = 1 := by simp [F]

/-- `2 F_{n+1} = L_n + F_n` and `2 L_{n+1} = L_n + 5 F_n`: multiplication by `φ`. -/
lemma step (n : ℕ) : 2 * F (n + 1) = L n + F n ∧ 2 * L (n + 1) = L n + 5 * F n := by
  have key : ∀ n, (2 * F (n + 1) = L n + F n ∧ 2 * L (n + 1) = L n + 5 * F n) ∧
      (2 * F (n + 2) = L (n + 1) + F (n + 1) ∧ 2 * L (n + 2) = L (n + 1) + 5 * F (n + 1)) := by
    intro n
    induction n with
    | zero => simp [F, L, Nat.fib_add_two]
    | succ n ih =>
      refine ⟨ih.2, ?_, ?_⟩
      · rw [F_rec (n + 1), L_rec n]; linarith [ih.1.1, ih.2.1]
      · rw [L_rec (n + 1), F_rec n] at *; linarith [ih.1.2, ih.2.2]
  exact (key n).1

lemma norm (n : ℕ) : L n ^ 2 - 5 * F n ^ 2 = 4 * (-1) ^ n := by
  induction n with
  | zero => simp [F, L]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := step n
    have : 4 * (L (n + 1) ^ 2 - 5 * F (n + 1) ^ 2) = 4 * (4 * (-1) ^ (n + 1)) := by
      have e1 : 4 * L (n + 1) ^ 2 = (L n + 5 * F n) ^ 2 := by rw [← h2]; ring
      have e2 : 4 * F (n + 1) ^ 2 = (L n + F n) ^ 2 := by rw [← h1]; ring
      rw [pow_succ]
      linear_combination e1 - 5 * e2 - 4 * ih
    linarith

lemma F_nonneg (n : ℕ) : 0 ≤ F n := by simp [F]

lemma L_pos (n : ℕ) : 1 ≤ L n := by
  have key : ∀ n, 1 ≤ L n ∧ 1 ≤ L (n + 1) := by
    intro n
    induction n with
    | zero => simp [L]
    | succ n ih => exact ⟨ih.2, by rw [L_rec]; omega⟩
  exact (key n).1

/-- Six steps of `φ` are the unit `9 + 4√5` of `ℤ[√5]`. -/
lemma shift6 (n : ℕ) : L (n + 6) = 9 * L n + 20 * F n ∧ F (n + 6) = 4 * L n + 9 * F n := by
  constructor
  · exact rec_unique (f := fun n => L (n + 6)) (g := fun n => 9 * L n + 20 * F n) 1 1 0
      (fun n => by simp only [show n + 2 + 6 = (n + 6) + 2 by ring, L_rec]; ring_nf)
      (fun n => by
        show 9 * L (n + 2) + 20 * F (n + 2) = 1 * (9 * L (n + 1) + 20 * F (n + 1)) + 1 * (9 * L n + 20 * F n) + 0
        rw [L_rec, F_rec]; ring) (by simp [L, F, Nat.fib_add_two])
      (by simp [L, F, Nat.fib_add_two]) n
  · exact rec_unique (f := fun n => F (n + 6)) (g := fun n => 4 * L n + 9 * F n) 1 1 0
      (fun n => by simp only [show n + 2 + 6 = (n + 6) + 2 by ring, F_rec]; ring_nf)
      (fun n => by
        show 4 * L (n + 2) + 9 * F (n + 2) = 1 * (4 * L (n + 1) + 9 * F (n + 1)) + 1 * (4 * L n + 9 * F n) + 0
        rw [L_rec, F_rec]; ring) (by simp [L, F, Nat.fib_add_two])
      (by simp [L, F, Nat.fib_add_two]) n

lemma unit5 : (9 : ℤ) ^ 2 - 5 * 4 ^ 2 = 1 := by norm_num

lemma orbit (r j : ℕ) : unitOrbit 5 9 4 (L r, F r) j = (L (6 * j + r), F (6 * j + r)) := by
  induction j with
  | zero => show (L r, F r) = (L (6 * 0 + r), F (6 * 0 + r)); simp
  | succ j ih =>
    rw [orbit_succ, ih, show 6 * (j + 1) + r = (6 * j + r) + 6 by ring, (shift6 _).1, (shift6 _).2]
    simp only [unitAct]
    ext <;> ring

/-! ### Completeness, certified by the engine -/

theorem cert_pos : seedCheck 5 9 4 4 [(2, 0), (3, 1), (7, 3)] 8 = true := by decide +kernel
theorem cert_neg : seedCheck 5 9 4 (-4) [(1, 1), (4, 2), (11, 5)] 8 = true := by decide +kernel

lemma sol_LF (n : ℕ) : Sol 5 (4 * (-1) ^ n) (L n, F n) :=
  ⟨by have := L_pos n; show 0 < L n; omega, F_nonneg n, norm n⟩

/-- **The positive solutions of `x^2 - 5y^2 = 4` are the even-index Lucas-Fibonacci pairs.** -/
theorem pos_iff (p : ℤ × ℤ) : Sol 5 4 p ↔ ∃ n, (L (2 * n), F (2 * n)) = p := by
  rw [complete (by norm_num) (by norm_num) (by norm_num) unit5 cert_pos]
  constructor
  · rintro ⟨ρ, hρ, j, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl
    · refine ⟨3 * j, ?_⟩
      rw [show ((2 : ℤ), (0 : ℤ)) = (L 0, F 0) by simp [L, F], orbit]
      congr 2 <;> ring
    · refine ⟨3 * j + 1, ?_⟩
      rw [show ((3 : ℤ), (1 : ℤ)) = (L 2, F 2) by simp [L, F, Nat.fib_add_two], orbit]
      congr 2 <;> ring
    · refine ⟨3 * j + 2, ?_⟩
      rw [show ((7 : ℤ), (3 : ℤ)) = (L 4, F 4) by
        simp [L, F, Nat.fib_add_two], orbit]
      congr 2 <;> ring
  · rintro ⟨n, rfl⟩
    have := sol_LF (2 * n)
    rw [pow_mul] at this; norm_num at this
    rw [complete (by norm_num) (by norm_num) (by norm_num) unit5 cert_pos] at this
    exact this

/-- **The positive solutions of `x^2 - 5y^2 = -4` are the odd-index pairs.** -/
theorem neg_iff (p : ℤ × ℤ) : Sol 5 (-4) p ↔ ∃ n, (L (2 * n + 1), F (2 * n + 1)) = p := by
  constructor
  · intro hp
    rw [complete (by norm_num) (by norm_num) (by norm_num) unit5 cert_neg] at hp
    obtain ⟨ρ, hρ, j, rfl⟩ := hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl
    · refine ⟨3 * j, ?_⟩
      rw [show ((1 : ℤ), (1 : ℤ)) = (L 1, F 1) by simp [L, F], orbit]
      congr 2 <;> ring
    · refine ⟨3 * j + 1, ?_⟩
      rw [show ((4 : ℤ), (2 : ℤ)) = (L 3, F 3) by simp [L, F, Nat.fib_add_two], orbit]
      congr 2 <;> ring
    · refine ⟨3 * j + 2, ?_⟩
      rw [show ((11 : ℤ), (5 : ℤ)) = (L 5, F 5) by
        simp [L, F, Nat.fib_add_two], orbit]
      congr 2 <;> ring
  · rintro ⟨n, rfl⟩
    have := sol_LF (2 * n + 1)
    rw [pow_succ, pow_mul] at this; norm_num at this
    exact this

/-! ### Collisions and inversion -/

lemma F_mono (n : ℕ) : F (n + 2) < F (n + 3) := by
  have h := F_rec (n + 1)
  simp only [show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at h
  have : 0 < F (n + 1) := by
    simp only [F]; exact_mod_cast Nat.fib_pos.mpr (by omega)
  omega

lemma F_strictMono : StrictMono (fun n => F (n + 2)) :=
  strictMono_nat_of_lt_succ fun n => F_mono n

/-- **The only collision of `F` is `F_1 = F_2`.** -/
theorem fib_collision {i j : ℕ} (h : F i = F j) : i = j ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
  have small : ∀ k, k ≤ 1 → F k ≤ 1 := by
    intro k hk; interval_cases k <;> simp [F]
  have big : ∀ k, 2 ≤ k → 1 ≤ F k ∧ (3 ≤ k → 2 ≤ F k) := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    refine ⟨?_, fun h3 => ?_⟩
    · have := F_strictMono.monotone (Nat.zero_le m); simp [F] at this ⊢; omega
    · have := F_strictMono (show 0 < m by omega); simp [F] at this ⊢; omega
  rcases Nat.lt_or_ge i 2 with hi | hi <;> rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases i <;> interval_cases j <;> simp [F] at h ⊢
  · rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · interval_cases i <;> interval_cases j <;> simp [F] at h ⊢
    · have := (big j hj).2 hj3; have := small i (by omega); omega
  · rcases Nat.lt_or_ge i 3 with hi3 | hi3
    · interval_cases j <;> interval_cases i <;> simp [F] at h ⊢
    · have := (big i hi).2 hi3; have := small j (by omega); omega
  · left
    obtain ⟨a, rfl⟩ : ∃ a, i = a + 2 := ⟨i - 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, j = b + 2 := ⟨j - 2, by omega⟩
    have := F_strictMono.injective h
    omega

/-- **The repair**: the value and the index parity (the sign of the norm) determine the index. -/
theorem fib_parity_inj {i j : ℕ} (h : F i = F j) (hp : i % 2 = j % 2) : i = j := by
  rcases fib_collision h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · simp at hp
  · simp at hp

/-! ### The compiled parity filter -/

/-- `F_n` is even iff `3 ∣ n` (the residues of `(L, F)` mod 2 have period 3). -/
theorem even_iff (n : ℕ) : F n % 2 = 0 ↔ n % 3 = 0 := by
  have key : ∀ n, (F n % 2 = 0 ↔ n % 3 = 0) ∧ (F (n + 1) % 2 = 0 ↔ (n + 1) % 3 = 0) := by
    intro n
    induction n with
    | zero => simp [F]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 1 = n + 2 by ring, F_rec]
      constructor
      · intro h
        have := ih.1; have := ih.2
        omega
      · intro h
        have := ih.1; have := ih.2
        omega
  exact (key n).1

/-! ### Counting -/

/-- `9 + 4√5 = φ^6`. -/
lemma eps_eq : eps 5 9 4 = goldenRatio ^ 6 := by
  have hφ : goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  simp only [eps, hφ]
  push_cast
  linear_combination (-(Real.sqrt 5 ^ 4 + 6 * Real.sqrt 5 ^ 3 + 20 * Real.sqrt 5 ^ 2 +
    50 * Real.sqrt 5 + 115) / 64) * h5

/-- The Fibonacci numbers (the count below only looks at `[1, N]`). -/
def FibSet : Set ℕ := {v | ∃ n, Nat.fib n = v}

lemma seedSol (r : ℕ) : Sol 5 (4 * (-1) ^ r) (L r, F r) := sol_LF r

/-- **The Fibonacci numbers count at `log N / log φ`**: six observed orbits of `φ^6`. -/
theorem fib_count : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |((#{v ∈ Icc 1 N | v ∈ FibSet} : ℕ) : ℝ) - Real.log N / Real.log goldenRatio| ≤ K := by
  -- the observations: `F (6 j + r)`, one orbit for each residue `r < 6`
  let obs : ℕ → ℕ → ℕ := fun r j => Nat.fib (6 * j + r)
  have hobs : ∀ r j, ((obs r j : ℕ) : ℤ) = (unitOrbit 5 9 4 (L r, F r) j).2 := by
    intro r j; rw [orbit]; rfl
  -- growth, from the engine, from index 1 on
  have hgrowth : ∀ r, ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ j,
      c₁ * eps 5 9 4 ^ j ≤ (obs r (j + 1) : ℝ) ∧ (obs r (j + 1) : ℝ) ≤ c₂ * eps 5 9 4 ^ j := by
    intro r
    obtain ⟨c₁, c₂, h1, h2, h⟩ := snd_between (by norm_num) unit5 (by norm_num) (by norm_num)
      (seedSol r)
    refine ⟨c₁, c₂, h1, h2, fun j => ?_⟩
    have e : (obs r (j + 1) : ℝ) = ((unitOrbit 5 9 4 (L r, F r) (j + 1)).2 : ℝ) := by
      rw [← hobs]; rfl
    rw [e]; exact h j
  choose c₁ c₂ hc₁ hc₂ hc using hgrowth
  have hε : 1 < eps 5 9 4 := one_lt_eps (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := observed_count_eventually (range 6) obs (fun _ => 1) (fun _ => eps 5 9 4)
    c₁ c₂ (fun _ _ => hε) (fun r _ => hc₁ r) (fun r _ => hc₂ r)
    (fun r _ j => (hc r j).1) (fun r _ j => (hc r j).2) (fun _ => 1) (fun _ _ => one_pos)
    (fun _ _ => True) (fun _ _ _ => Iff.rfl)
    (fun r _ => by
      apply strictMono_nat_of_lt_succ
      intro j
      show Nat.fib (6 * (j + 1) + r) < Nat.fib (6 * (j + 1 + 1) + r)
      exact (Nat.fib_lt_fib (by omega)).mpr (by omega))
    1 (fun r hr s hs i j _ _ hij hv => by
      simp only [mem_range] at hr hs
      simp only [obs] at hij hv
      have h := fib_collision (i := 6 * (i + 1) + r) (j := 6 * (j + 1) + s)
        (by simp only [F]; exact_mod_cast hij)
      omega)
    FibSet (fun v => by
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n % 6, mem_range.mpr (Nat.mod_lt _ (by norm_num)), n / 6, trivial,
          by simp only [obs]; congr 1; omega⟩
      · rintro ⟨r, -, j, -, rfl⟩
        exact ⟨_, rfl⟩)
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  have hsum : (∑ ρ ∈ range 6, (#((range ((fun _ => 1) ρ)).filter ((fun _ _ => True) ρ)) : ℝ) /
      ((((fun _ => 1) ρ : ℕ) : ℝ) * Real.log ((fun _ => eps 5 9 4) ρ))) =
      1 / Real.log goldenRatio := by
    simp only [range_one, filter_True, card_singleton, Nat.cast_one, one_mul, sum_const,
      card_range, nsmul_eq_mul, eps_eq, Real.log_pow]
    have : Real.log goldenRatio ≠ 0 := (Real.log_pos one_lt_gold).ne'
    field_simp
  rw [hsum] at this
  rw [div_eq_mul_one_div, mul_comm]
  exact this

/-- The even Fibonacci numbers. -/
def EvenFibSet : Set ℕ := {v | ∃ n, Nat.fib n = v ∧ v % 2 = 0}

/-- **The even Fibonacci numbers count at `log N / (3 log φ)`**: the parity filter keeps the
two seed orbits `r = 0, 3` of the six. -/
theorem even_fib_count : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |((#{v ∈ Icc 1 N | v ∈ EvenFibSet} : ℕ) : ℝ) - Real.log N / (3 * Real.log goldenRatio)| ≤ K := by
  let obs : ℕ → ℕ → ℕ := fun r j => Nat.fib (6 * j + r)
  have hobs : ∀ r j, ((obs r j : ℕ) : ℤ) = (unitOrbit 5 9 4 (L r, F r) j).2 := by
    intro r j; rw [orbit]; rfl
  have hgrowth : ∀ r, ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ j,
      c₁ * eps 5 9 4 ^ j ≤ (obs r (j + 1) : ℝ) ∧ (obs r (j + 1) : ℝ) ≤ c₂ * eps 5 9 4 ^ j := by
    intro r
    obtain ⟨c₁, c₂, h1, h2, h⟩ := snd_between (by norm_num) unit5 (by norm_num) (by norm_num)
      (seedSol r)
    refine ⟨c₁, c₂, h1, h2, fun j => ?_⟩
    have e : (obs r (j + 1) : ℝ) = ((unitOrbit 5 9 4 (L r, F r) (j + 1)).2 : ℝ) := by
      rw [← hobs]; rfl
    rw [e]; exact h j
  choose c₁ c₂ hc₁ hc₂ hc using hgrowth
  have hε : 1 < eps 5 9 4 := one_lt_eps (by norm_num) (by norm_num)
  have hev : ∀ n, Nat.fib n % 2 = 0 ↔ n % 3 = 0 := by
    intro n; have := even_iff n; simp only [F] at this; omega
  obtain ⟨K, hK⟩ := observed_count_eventually ({0, 3} : Finset ℕ) obs (fun _ => 1) (fun _ => eps 5 9 4)
    c₁ c₂ (fun _ _ => hε) (fun r _ => hc₁ r) (fun r _ => hc₂ r)
    (fun r _ j => (hc r j).1) (fun r _ j => (hc r j).2) (fun _ => 1) (fun _ _ => one_pos)
    (fun _ _ => True) (fun _ _ _ => Iff.rfl)
    (fun r _ => by
      apply strictMono_nat_of_lt_succ
      intro j
      show Nat.fib (6 * (j + 1) + r) < Nat.fib (6 * (j + 1 + 1) + r)
      exact (Nat.fib_lt_fib (by omega)).mpr (by omega))
    1 (fun r hr s hs i j _ _ hij hv => by
      simp only [obs] at hij hv
      have h := fib_collision (i := 6 * (i + 1) + r) (j := 6 * (j + 1) + s)
        (by simp only [F]; exact_mod_cast hij)
      simp only [mem_insert, mem_singleton] at hr hs
      omega)
    EvenFibSet (fun v => by
      constructor
      · rintro ⟨n, rfl, hv⟩
        have h3 := (hev n).mp hv
        refine ⟨n % 6, ?_, n / 6, trivial, by simp only [obs]; congr 1; omega⟩
        simp only [mem_insert, mem_singleton]; omega
      · rintro ⟨r, hr, j, -, rfl⟩
        refine ⟨_, rfl, (hev _).mpr ?_⟩
        simp only [mem_insert, mem_singleton] at hr; omega)
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  have hsum : (∑ ρ ∈ ({0, 3} : Finset ℕ), (#((range ((fun _ => 1) ρ)).filter ((fun _ _ => True) ρ)) : ℝ) /
      ((((fun _ => 1) ρ : ℕ) : ℝ) * Real.log ((fun _ => eps 5 9 4) ρ))) =
      1 / (3 * Real.log goldenRatio) := by
    simp only [range_one, filter_True, card_singleton, Nat.cast_one, one_mul, sum_const,
      eps_eq, Real.log_pow]
    have : Real.log goldenRatio ≠ 0 := (Real.log_pos one_lt_gold).ne'
    rw [card_insert_of_notMem (by decide), card_singleton]
    field_simp; ring
  rw [hsum] at this
  rw [div_eq_mul_one_div, mul_comm]
  exact this

end PerfectPower.FibOrbit
