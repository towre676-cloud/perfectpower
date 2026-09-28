import PerfectPower.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic

namespace PerfectPower

/-! ### Interfaces for the Pell type (research notes, Theorem Q)

For `P(n) = A n^2 + B n + C` the Pell-type count is `A(N) = κ log N + O(1)` with
`κ = Σ_orbits R / (P log u)`: `R` good residue classes among the `P` orbit indices of one period
modulo `2A`, each class growing geometrically with ratio `u^P`.  This file proves the four pieces
of that statement which do not need the (classical, unformalised here) finiteness of the orbit
set of a norm equation:

* `quadratic_isHit_iff_norm`: `P(n)` is a square iff `X^2 - 4A Y^2 = B^2 - 4AC` with `X = 2An + B`;
* `unitAct_norm`: the unit `(x₁, y₁)`, `x₁^2 - D y₁^2 = 1`, preserves the norm form;
* `unitOrbit_periodic`: the orbit of any point is *purely* periodic modulo every `M > 0`;
* `goodClass_hits`: a good residue class (`X ≡ B mod 2A`) stays good along the period, and each
  of its orbit points is a hit;
* `geometric_count_le` / `le_geometric_count`: a sequence between `c₁ E^j` and `c₂ E^j` has
  `log N / log E + O(1)` terms below `N`, which is where the factor `1 / (P log u)` comes from. -/

/-- **Norm-equation form.** `A n^2 + B n + C` is a square iff `(2An + B)^2 - 4A Y^2 = B^2 - 4AC`
for some `Y`. -/
theorem quadratic_isHit_iff_norm {A : ℤ} (hA : A ≠ 0) (B C n : ℤ) :
    IsHit 2 (A * n ^ 2 + B * n + C) ↔
      ∃ Y : ℤ, (2 * A * n + B) ^ 2 - 4 * A * Y ^ 2 = B ^ 2 - 4 * A * C := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by linear_combination (4 * A) * hm⟩
  · rintro ⟨Y, hY⟩
    refine ⟨Y, ?_⟩
    have h4 : (4 * A) * (A * n ^ 2 + B * n + C) = (4 * A) * Y ^ 2 := by linear_combination hY
    exact mul_left_cancel₀ (by simpa using hA) h4

/-- The action of a unit `x₁ + y₁ √D` on `X + Y √D`. -/
def unitAct (D x₁ y₁ : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * x₁ + D * p.2 * y₁, p.1 * y₁ + p.2 * x₁)

/-- The orbit `(X_j, Y_j) = (X₀ + Y₀√D)(x₁ + y₁√D)^j`. -/
def unitOrbit (D x₁ y₁ : ℤ) (p₀ : ℤ × ℤ) (j : ℕ) : ℤ × ℤ := (unitAct D x₁ y₁)^[j] p₀

/-- A unit of norm one preserves the norm form `X^2 - D Y^2`. -/
theorem unitAct_norm {D x₁ y₁ : ℤ} (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1) (p : ℤ × ℤ) :
    (unitAct D x₁ y₁ p).1 ^ 2 - D * (unitAct D x₁ y₁ p).2 ^ 2 = p.1 ^ 2 - D * p.2 ^ 2 := by
  simp only [unitAct]
  linear_combination (p.1 ^ 2 - D * p.2 ^ 2) * hu

theorem unitOrbit_norm {D x₁ y₁ : ℤ} (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1) (p₀ : ℤ × ℤ) (j : ℕ) :
    (unitOrbit D x₁ y₁ p₀ j).1 ^ 2 - D * (unitOrbit D x₁ y₁ p₀ j).2 ^ 2 =
      p₀.1 ^ 2 - D * p₀.2 ^ 2 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [unitOrbit, Function.iterate_succ_apply', ← unitOrbit, unitAct_norm hu, ih]

lemma unit_cast (M : ℕ) {D x₁ y₁ : ℤ} (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1) :
    (x₁ : ZMod M) ^ 2 - (D : ZMod M) * (y₁ : ZMod M) ^ 2 = 1 := by
  have := congrArg (Int.cast : ℤ → ZMod M) hu
  push_cast at this
  exact this

/-- The unit action modulo `M`, as a permutation of `(ZMod M)²` (its inverse is the conjugate
unit `x₁ - y₁ √D`). -/
def unitPerm (M : ℕ) (D x₁ y₁ : ℤ) (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1) :
    Equiv.Perm (ZMod M × ZMod M) where
  toFun p := (p.1 * x₁ + D * p.2 * y₁, p.1 * y₁ + p.2 * x₁)
  invFun p := (p.1 * x₁ - D * p.2 * y₁, -p.1 * y₁ + p.2 * x₁)
  left_inv p := by
    have hu' := unit_cast M hu
    ext
    · show (p.1 * x₁ + D * p.2 * y₁) * x₁ - D * (p.1 * y₁ + p.2 * x₁) * y₁ = p.1
      linear_combination p.1 * hu'
    · show -(p.1 * x₁ + D * p.2 * y₁) * y₁ + (p.1 * y₁ + p.2 * x₁) * x₁ = p.2
      linear_combination p.2 * hu'
  right_inv p := by
    have hu' := unit_cast M hu
    ext
    · show (p.1 * x₁ - D * p.2 * y₁) * x₁ + D * (-p.1 * y₁ + p.2 * x₁) * y₁ = p.1
      linear_combination p.1 * hu'
    · show (p.1 * x₁ - D * p.2 * y₁) * y₁ + (-p.1 * y₁ + p.2 * x₁) * x₁ = p.2
      linear_combination p.2 * hu'

lemma cast_unitOrbit (M : ℕ) {D x₁ y₁ : ℤ} (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1) (p₀ : ℤ × ℤ) (j : ℕ) :
    (((unitOrbit D x₁ y₁ p₀ j).1 : ZMod M), ((unitOrbit D x₁ y₁ p₀ j).2 : ZMod M)) =
      (unitPerm M D x₁ y₁ hu ^ j) ((p₀.1 : ZMod M), (p₀.2 : ZMod M)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ← ih, unitOrbit, Function.iterate_succ_apply', ← unitOrbit]
    simp [unitAct, unitPerm]

/-- **Pure periodicity modulo `M`.** For `M > 0` there is a period `P > 0` with
`(X_{j+P}, Y_{j+P}) ≡ (X_j, Y_j) (mod M)` for every `j`. -/
theorem unitOrbit_periodic (M : ℕ) [NeZero M] {D x₁ y₁ : ℤ} (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1)
    (p₀ : ℤ × ℤ) :
    ∃ P, 0 < P ∧ ∀ j, (M : ℤ) ∣ (unitOrbit D x₁ y₁ p₀ (j + P)).1 - (unitOrbit D x₁ y₁ p₀ j).1 ∧
      (M : ℤ) ∣ (unitOrbit D x₁ y₁ p₀ (j + P)).2 - (unitOrbit D x₁ y₁ p₀ j).2 := by
  set σ := unitPerm M D x₁ y₁ hu
  refine ⟨orderOf σ, orderOf_pos σ, fun j => ?_⟩
  have h := cast_unitOrbit M hu p₀ (j + orderOf σ)
  rw [pow_add, pow_orderOf_eq_one, mul_one, ← cast_unitOrbit M hu p₀ j] at h
  simp only [Prod.mk.injEq] at h
  exact ⟨(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h.1.symm,
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h.2.symm⟩

/-- **Good classes.** Let `(X₀, Y₀)` solve `X^2 - 4A Y^2 = B^2 - 4AC`, let `(x₁, y₁)` be a unit
for `D = 4A`, and let `P` be a period of the orbit modulo `2A`.  If the orbit index `r` is good
(`X_r ≡ B mod 2A`), then so is every `r + kP`, and `n = (X_{r+kP} - B) / (2A)` is a hit. -/
theorem goodClass_hits {A B C : ℤ} (hA : A ≠ 0) {x₁ y₁ : ℤ} (hu : x₁ ^ 2 - 4 * A * y₁ ^ 2 = 1)
    {p₀ : ℤ × ℤ} (h₀ : p₀.1 ^ 2 - 4 * A * p₀.2 ^ 2 = B ^ 2 - 4 * A * C) {P r : ℕ}
    (hP : ∀ j, (2 * A) ∣ (unitOrbit (4 * A) x₁ y₁ p₀ (j + P)).1 - (unitOrbit (4 * A) x₁ y₁ p₀ j).1)
    (hr : (2 * A) ∣ (unitOrbit (4 * A) x₁ y₁ p₀ r).1 - B) (k : ℕ) :
    ∃ n : ℤ, 2 * A * n + B = (unitOrbit (4 * A) x₁ y₁ p₀ (r + k * P)).1 ∧
      IsHit 2 (A * n ^ 2 + B * n + C) := by
  have hgood : (2 * A) ∣ (unitOrbit (4 * A) x₁ y₁ p₀ (r + k * P)).1 - B := by
    induction k with
    | zero => simpa using hr
    | succ k ih =>
      have := dvd_add (hP (r + k * P)) ih
      rw [show r + (k + 1) * P = r + k * P + P by ring]
      simpa using this
  obtain ⟨n, hn⟩ := hgood
  refine ⟨n, by linarith, (quadratic_isHit_iff_norm hA B C n).mpr
    ⟨(unitOrbit (4 * A) x₁ y₁ p₀ (r + k * P)).2, ?_⟩⟩
  rw [show 2 * A * n + B = (unitOrbit (4 * A) x₁ y₁ p₀ (r + k * P)).1 by linarith,
    unitOrbit_norm hu, h₀]

/-! #### Geometric growth gives `log N / log E` terms -/

/-- Terms of a sequence with `c₁ E^j ≤ f j` that are `≤ N` have `j ≤ log (N / c₁) / log E`. -/
theorem index_le_of_geometric {f : ℕ → ℝ} {E c₁ N : ℝ} (hE : 1 < E) (hc₁ : 0 < c₁)
    (hf : ∀ j, c₁ * E ^ j ≤ f j) {j : ℕ} (hj : f j ≤ N) :
    (j : ℝ) ≤ Real.log (N / c₁) / Real.log E := by
  have hlogE : 0 < Real.log E := Real.log_pos hE
  have hpow : E ^ j ≤ N / c₁ := by rw [le_div_iff₀ hc₁]; linarith [hf j]
  have hEj : 0 < E ^ j := pow_pos (by linarith) j
  rw [le_div_iff₀ hlogE, ← Real.log_pow]
  exact Real.log_le_log hEj hpow

/-- Terms with `j ≤ log (N / c₂) / log E` satisfy `f j ≤ N` when `f j ≤ c₂ E^j`. -/
theorem le_of_index_le_geometric {f : ℕ → ℝ} {E c₂ N : ℝ} (hE : 1 < E) (hc₂ : 0 < c₂) (hN : 0 < N)
    (hf : ∀ j, f j ≤ c₂ * E ^ j) {j : ℕ} (hj : (j : ℝ) ≤ Real.log (N / c₂) / Real.log E) :
    f j ≤ N := by
  have hlogE : 0 < Real.log E := Real.log_pos hE
  rw [le_div_iff₀ hlogE, ← Real.log_pow] at hj
  have hpow : E ^ j ≤ N / c₂ :=
    (Real.log_le_log_iff (pow_pos (by linarith) j) (div_pos hN hc₂)).mp hj
  have := hf j
  rw [le_div_iff₀ hc₂] at hpow
  linarith

/-- **Upper count.** At most `log (N / c₁) / log E + 1` terms of a sequence with
`c₁ E^j ≤ f j` are `≤ N` (`c₁ ≤ N`). -/
theorem geometric_count_le {f : ℕ → ℝ} {E c₁ N : ℝ} (hE : 1 < E) (hc₁ : 0 < c₁) (hN : c₁ ≤ N)
    (hf : ∀ j, c₁ * E ^ j ≤ f j) (L : ℕ) :
    (((Finset.range L).filter (fun j => f j ≤ N)).card : ℝ) ≤
      Real.log (N / c₁) / Real.log E + 1 := by
  set b := Real.log (N / c₁) / Real.log E
  have hb : 0 ≤ b := div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hc₁]; linarith))
    (Real.log_pos hE).le
  have hsub : (Finset.range L).filter (fun j => f j ≤ N) ⊆ Finset.range (⌊b⌋₊ + 1) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    have := index_le_of_geometric hE hc₁ hf hj.2
    exact Nat.lt_succ_of_le (Nat.le_floor this)
  calc (((Finset.range L).filter (fun j => f j ≤ N)).card : ℝ)
      ≤ ((Finset.range (⌊b⌋₊ + 1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = ⌊b⌋₊ + 1 := by simp
    _ ≤ b + 1 := by linarith [Nat.floor_le hb]

/-- **Lower count.** If `L` exceeds `log (N / c₂) / log E`, at least `log (N / c₂) / log E` terms
of a sequence with `f j ≤ c₂ E^j` are `≤ N`. -/
theorem le_geometric_count {f : ℕ → ℝ} {E c₂ N : ℝ} (hE : 1 < E) (hc₂ : 0 < c₂) (hN : 0 < N)
    (hf : ∀ j, f j ≤ c₂ * E ^ j) (L : ℕ) (hL : Real.log (N / c₂) / Real.log E < L) :
    Real.log (N / c₂) / Real.log E ≤ (((Finset.range L).filter (fun j => f j ≤ N)).card : ℝ) := by
  set b := Real.log (N / c₂) / Real.log E
  rcases lt_or_le b 0 with hb | hb
  · exact hb.le.trans (Nat.cast_nonneg _)
  have hsub : Finset.range (⌊b⌋₊ + 1) ⊆ (Finset.range L).filter (fun j => f j ≤ N) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    have hjb : (j : ℝ) ≤ b := by
      have : j ≤ ⌊b⌋₊ := Nat.lt_succ_iff.mp hj
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le hb)
    refine ⟨?_, le_of_index_le_geometric hE hc₂ hN hf hjb⟩
    exact_mod_cast hjb.trans_lt hL
  calc b ≤ ⌊b⌋₊ + 1 := (Nat.lt_floor_add_one b).le
    _ = ((Finset.range (⌊b⌋₊ + 1)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

end PerfectPower
