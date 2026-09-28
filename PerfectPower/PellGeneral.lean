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

/-! #### Finitely many orbit representatives

Every solution of `X^2 - D Y^2 = Δ` with `X > 0`, `Y ≥ 0` is the image, under a nonnegative power of
the unit, of a solution in the box `D Y₀^2 ≤ |Δ| x₁^2`; the box is finite.  The descent step is the
inverse unit, `(X, Y) ↦ (X x₁ - D Y y₁, x₁ Y - y₁ X)`, which keeps `X > 0`, `Y ≥ 0` and strictly
decreases `X` outside the box.  (This is a weak form of Nagell's bound, enough for finiteness.) -/

/-- From squares to values: `0 ≤ b` and `a^2 < b^2` give `a < b`. -/
lemma lt_of_sq_lt_sq' {a b : ℤ} (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
  by_contra hab; push_neg at hab
  nlinarith [mul_le_mul hab hab hb (le_trans hb hab)]

/-- The unit applied to the descended point gives back the point. -/
lemma unitAct_descend {D x₁ y₁ : ℤ} (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1) (X Y : ℤ) :
    unitAct D x₁ y₁ (X * x₁ - D * Y * y₁, x₁ * Y - y₁ * X) = (X, Y) := by
  simp only [unitAct, Prod.mk.injEq]
  constructor
  · linear_combination X * hu
  · linear_combination Y * hu

/-- **Descent to the box.** -/
theorem pell_descent_box {D x₁ y₁ Δ : ℤ} (hD : 0 < D) (hx₁ : 1 < x₁) (hy₁ : 0 < y₁)
    (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1) :
    ∀ (X Y : ℤ), 0 < X → 0 ≤ Y → X ^ 2 - D * Y ^ 2 = Δ →
      ∃ (k : ℕ) (X₀ Y₀ : ℤ), 0 < X₀ ∧ 0 ≤ Y₀ ∧ X₀ ^ 2 - D * Y₀ ^ 2 = Δ ∧
        D * Y₀ ^ 2 ≤ |Δ| * x₁ ^ 2 ∧ unitOrbit D x₁ y₁ (X₀, Y₀) k = (X, Y) := by
  intro X
  induction X using Int.strongRec (m := 1) with
  | lt X hX => intro Y hX0; omega
  | ge X _ ih =>
    intro Y hX0 hY0 hN
    by_cases hbox : D * Y ^ 2 ≤ |Δ| * x₁ ^ 2
    · exact ⟨0, X, Y, hX0, hY0, hN, hbox, rfl⟩
    push_neg at hbox
    have habs : -|Δ| ≤ Δ ∧ Δ ≤ |Δ| := ⟨neg_abs_le Δ, le_abs_self Δ⟩
    have hDy : D * y₁ ^ 2 < x₁ ^ 2 := by linarith
    have hA0 : 0 ≤ |Δ| := abs_nonneg Δ
    -- consequences of being outside the box
    have c2 : -Δ * x₁ ^ 2 < D * Y ^ 2 := by nlinarith
    have c3 : y₁ ^ 2 * Δ ≤ Y ^ 2 := by
      have h1 : |Δ| * (D * y₁ ^ 2) ≤ |Δ| * x₁ ^ 2 := mul_le_mul_of_nonneg_left hDy.le hA0
      have h2 : |Δ| * y₁ ^ 2 < Y ^ 2 := by
        by_contra h; push_neg at h
        have := mul_le_mul_of_nonneg_left h hD.le
        nlinarith
      have h3 : y₁ ^ 2 * Δ ≤ y₁ ^ 2 * |Δ| := mul_le_mul_of_nonneg_left habs.2 (sq_nonneg _)
      linarith
    set X' := X * x₁ - D * Y * y₁
    set Y' := x₁ * Y - y₁ * X
    have hX'pos : 0 < X' := by
      have h := lt_of_sq_lt_sq' (a := D * Y * y₁) (b := X * x₁) (by positivity) (by
        have e1 : (D * Y * y₁) ^ 2 = D * Y ^ 2 * (x₁ ^ 2 - 1) := by linear_combination (-(D * Y ^ 2)) * hu
        have e2 : (X * x₁) ^ 2 = (Δ + D * Y ^ 2) * x₁ ^ 2 := by rw [mul_pow, ← hN]; ring
        rw [e1, e2]; nlinarith)
      simp only [X']; linarith
    have hX'lt : X' < X := by
      have h := lt_of_sq_lt_sq' (a := X * (x₁ - 1)) (b := D * Y * y₁) (by positivity) (by
        have e1 : (D * Y * y₁) ^ 2 = D * Y ^ 2 * (x₁ ^ 2 - 1) := by linear_combination (-(D * Y ^ 2)) * hu
        have e2 : (X * (x₁ - 1)) ^ 2 = (Δ + D * Y ^ 2) * (x₁ - 1) ^ 2 := by rw [mul_pow, ← hN]; ring
        rw [e1, e2]
        nlinarith)
      simp only [X']; linarith
    have hY' : 0 ≤ Y' := by
      have hle : y₁ * X ≤ x₁ * Y := by
        by_contra hlt; push_neg at hlt
        have h0 : 0 ≤ x₁ * Y := by positivity
        have hsq : (x₁ * Y) ^ 2 < (y₁ * X) ^ 2 := by nlinarith
        have e2 : (y₁ * X) ^ 2 = y₁ ^ 2 * (Δ + D * Y ^ 2) := by rw [mul_pow, ← hN]; ring
        have e1 : (x₁ * Y) ^ 2 = (1 + D * y₁ ^ 2) * Y ^ 2 := by
          rw [mul_pow]; linear_combination Y ^ 2 * hu
        rw [e1, e2] at hsq
        nlinarith
      simp only [Y']; linarith
    have hN' : X' ^ 2 - D * Y' ^ 2 = Δ := by
      simp only [X', Y']; linear_combination (X ^ 2 - D * Y ^ 2) * hu + hN
    obtain ⟨k, X₀, Y₀, h1, h2, h3, h4, h5⟩ := ih X' hX'lt Y' hX'pos hY' hN'
    refine ⟨k + 1, X₀, Y₀, h1, h2, h3, h4, ?_⟩
    rw [unitOrbit, Function.iterate_succ_apply', ← unitOrbit, h5]
    exact unitAct_descend hu X Y

/-- **The box is finite**, so there are finitely many orbit representatives. -/
theorem pell_box_finite {D x₁ Δ : ℤ} (hD : 0 < D) :
    {p : ℤ × ℤ | 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 - D * p.2 ^ 2 = Δ ∧
      D * p.2 ^ 2 ≤ |Δ| * x₁ ^ 2}.Finite := by
  set B := |Δ| * x₁ ^ 2
  refine (Set.finite_Icc (0 : ℤ) (B + |Δ|) |>.prod (Set.finite_Icc (0 : ℤ) B)).subset ?_
  rintro ⟨X, Y⟩ ⟨hX, hY, hN, hbox⟩
  simp only [Set.mem_prod, Set.mem_Icc]
  have hY2 : Y ≤ Y ^ 2 := by nlinarith
  have hDY : Y ^ 2 ≤ D * Y ^ 2 := by nlinarith
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hΔ : Δ ≤ |Δ| := le_abs_self Δ
  refine ⟨⟨hX.le, by nlinarith⟩, ⟨hY, by nlinarith⟩⟩

/-- **Orbit exhaustion.**  The solutions with `X > 0`, `Y ≥ 0` are covered by the forward orbits of
a finite set of representatives. -/
theorem pell_orbits_exhaust {D x₁ y₁ Δ : ℤ} (hD : 0 < D) (hx₁ : 1 < x₁) (hy₁ : 0 < y₁)
    (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1) :
    ∃ R : Finset (ℤ × ℤ), (∀ p ∈ R, 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 - D * p.2 ^ 2 = Δ) ∧
      ∀ X Y : ℤ, 0 < X → 0 ≤ Y → X ^ 2 - D * Y ^ 2 = Δ →
        ∃ p ∈ R, ∃ k : ℕ, unitOrbit D x₁ y₁ p k = (X, Y) := by
  set S := {p : ℤ × ℤ | 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 - D * p.2 ^ 2 = Δ ∧
      D * p.2 ^ 2 ≤ |Δ| * x₁ ^ 2}
  have hS : S.Finite := pell_box_finite hD
  refine ⟨hS.toFinset, fun p hp => by
    obtain ⟨h1, h2, h3, -⟩ := (hS.mem_toFinset).mp hp
    exact ⟨h1, h2, h3⟩, ?_⟩
  intro X Y hX hY hN
  obtain ⟨k, X₀, Y₀, h1, h2, h3, h4, h5⟩ := pell_descent_box hD hx₁ hy₁ hu X Y hX hY hN
  exact ⟨(X₀, Y₀), (hS.mem_toFinset).mpr ⟨h1, h2, h3, h4⟩, k, h5⟩

/-! #### The Pell count is `O(log N)`

Along a forward orbit with `X₀ > 0`, `Y₀ ≥ 0` the coordinates stay nonnegative and
`X_j ≥ X₀ x₁^j`, so at most `log_{x₁} M + 1` orbit points have `X ≤ M`.  With finitely many
orbits (`pell_orbits_exhaust`) this bounds the number of hits `n ≤ N` of a Pell-type quadratic by
`K (log_{x₁}(2AN + |B|) + 1) + |B|`: the upper half of `A(N) = κ log N + O(1)`. -/

/-- Growth along a forward orbit. -/
lemma unitOrbit_growth {D x₁ y₁ : ℤ} (hD : 0 ≤ D) (hx₁ : 1 ≤ x₁) (hy₁ : 0 ≤ y₁) {p₀ : ℤ × ℤ}
    (hX : 0 < p₀.1) (hY : 0 ≤ p₀.2) :
    ∀ j : ℕ, p₀.1 * x₁ ^ j ≤ (unitOrbit D x₁ y₁ p₀ j).1 ∧ 0 ≤ (unitOrbit D x₁ y₁ p₀ j).2
  | 0 => by simp [unitOrbit, hY]
  | j + 1 => by
    obtain ⟨h1, h2⟩ := unitOrbit_growth hD hx₁ hy₁ hX hY j
    rw [unitOrbit, Function.iterate_succ_apply', ← unitOrbit]
    simp only [unitAct]
    set X := (unitOrbit D x₁ y₁ p₀ j).1
    set Y := (unitOrbit D x₁ y₁ p₀ j).2
    have hpow : 0 < p₀.1 * x₁ ^ j := mul_pos hX (pow_pos (by omega) j)
    have hDY : 0 ≤ D * Y * y₁ := mul_nonneg (mul_nonneg hD h2) hy₁
    constructor
    · rw [pow_succ, ← mul_assoc]
      nlinarith
    · nlinarith

open scoped Classical in
/-- **Hits of a Pell-type quadratic: `O(log N)`.** -/
theorem pell_count_log {A B C x₁ y₁ : ℤ} (hA : 0 < A) (hx₁ : 1 < x₁) (hy₁ : 0 < y₁)
    (hu : x₁ ^ 2 - 4 * A * y₁ ^ 2 = 1) :
    ∃ K : ℕ, ∀ N : ℕ,
      (Finset.filter (fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) (Finset.Icc 1 N)).card ≤
        K * (Nat.log x₁.toNat (2 * A * N + |B|).toNat + 1) + B.natAbs := by
  classical
  obtain ⟨R, hR, hex⟩ := pell_orbits_exhaust (Δ := B ^ 2 - 4 * A * C) (by positivity) hx₁ hy₁ hu
  refine ⟨R.card, fun N => ?_⟩
  set M : ℤ := 2 * A * N + |B|
  set L := Nat.log x₁.toNat M.toNat
  set hits := Finset.filter (fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) (Finset.Icc 1 N)
  set g : (ℤ × ℤ) × ℕ → ℕ := fun q => (((unitOrbit (4 * A) x₁ y₁ q.1 q.2).1 - B) / (2 * A)).toNat
  -- hits with `2An + B ≤ 0` lie in `[1, |B|]`
  have hsmall : (hits.filter fun n : ℕ => 2 * A * n + B ≤ 0) ⊆ Finset.Icc 1 B.natAbs := by
    intro n hn
    simp only [hits, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    refine ⟨hn.1.1.1, ?_⟩
    have : (n : ℤ) ≤ |B| := by nlinarith [neg_abs_le B, (by exact_mod_cast hn.1.1.1 : (1 : ℤ) ≤ n)]
    have hB : (|B| : ℤ) = (B.natAbs : ℤ) := Int.abs_eq_natAbs B
    omega
  -- the others come from orbit points with `X ≤ M`, i.e. orbit index `≤ L`
  have hbig : (hits.filter fun n : ℕ => ¬ 2 * A * n + B ≤ 0) ⊆
      (R ×ˢ Finset.range (L + 1)).image g := by
    intro n hn
    simp only [hits, Finset.mem_filter, Finset.mem_Icc, not_le] at hn
    obtain ⟨⟨⟨hn1, hnN⟩, hhit⟩, hX⟩ := hn
    obtain ⟨Y, hY⟩ := (quadratic_isHit_iff_norm hA.ne' B C n).mp hhit
    obtain ⟨p, hp, j, hj⟩ := hex (2 * A * n + B) |Y| hX (abs_nonneg Y) (by rw [sq_abs]; exact hY)
    obtain ⟨hp1, hp2, -⟩ := hR p hp
    have hgrow := (unitOrbit_growth (D := 4 * A) (by positivity) hx₁.le hy₁.le hp1 hp2 j).1
    rw [hj] at hgrow
    simp only at hgrow
    have hXM : 2 * A * n + B ≤ M := by
      simp only [M]; have := le_abs_self B; nlinarith
    have hpow : x₁ ^ j ≤ M := by nlinarith [pow_pos (show (0 : ℤ) < x₁ by omega) j]
    have hjL : j ≤ L := by
      apply Nat.le_log_of_pow_le (by omega)
      have h1 : ((x₁.toNat ^ j : ℕ) : ℤ) = x₁ ^ j := by
        push_cast; rw [Int.toNat_of_nonneg (by omega)]
      have h2 : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg (by linarith [pow_pos (show (0 : ℤ) < x₁ by omega) j])
      exact_mod_cast (show ((x₁.toNat ^ j : ℕ) : ℤ) ≤ (M.toNat : ℤ) by rw [h1, h2]; exact hpow)
    refine Finset.mem_image.mpr ⟨(p, j), Finset.mem_product.mpr ⟨hp, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    simp only [g, hj]
    rw [show 2 * A * (n : ℤ) + B - B = 2 * A * n by ring, Int.mul_ediv_cancel_left _ (by positivity)]
    simp
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := hits)
    (fun n : ℕ => 2 * A * n + B ≤ 0)
  have c1 := Finset.card_le_card hsmall
  have c2 := (Finset.card_le_card hbig).trans Finset.card_image_le
  rw [Finset.card_product, Finset.card_range] at c2
  simp only [Nat.card_Icc, add_tsub_cancel_right] at c1
  omega

end PerfectPower
