import PerfectPower.QueryNative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PerfectPower.PellOrbitCore

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


/-- Undoing a forward step is exact in both coordinates. -/
def descend (D A B : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (A*p.1-D*B*p.2,A*p.2-B*p.1)

theorem descend_act {D A B : ℤ} (hu : A^2-D*B^2=1) (p : ℤ × ℤ) :
    descend D A B (unitAct D A B p) = p := by
  apply Prod.ext
  · simp only [descend,unitAct]; linear_combination p.1 * hu
  · simp only [descend,unitAct]; linear_combination p.2 * hu

theorem orbit_succ (D A B : ℤ) (p : ℤ × ℤ) (k : ℕ) :
    unitOrbit D A B p (k+1)=unitAct D A B (unitOrbit D A B p k) := by
  exact Function.iterate_succ_apply' _ _ _

theorem orbit_nonneg {D A B : ℤ} (hD : 0 < D) (hA : 1 < A) (hB : 0 < B)
    (p : ℤ × ℤ) (hx : 0 < p.1) (hy : 0 ≤ p.2) (k : ℕ) :
    0 < (unitOrbit D A B p k).1 ∧ 0 ≤ (unitOrbit D A B p k).2 := by
  induction k with
  | zero => exact ⟨hx,hy⟩
  | succ k ih =>
    obtain ⟨h1,h2⟩ := ih
    rw [orbit_succ]
    simp only [unitAct]
    constructor <;> positivity

theorem orbit_input_strictMono {D A B : ℤ} (hD : 0 < D) (hA : 1 < A) (hB : 0 < B)
    (p : ℤ × ℤ) (hx : 0 < p.1) (hy : 0 ≤ p.2) :
    StrictMono (fun k => (unitOrbit D A B p k).2) := by
  apply strictMono_nat_of_lt_succ
  intro k
  obtain ⟨h1,h2⟩ := orbit_nonneg hD hA hB p hx hy k
  rw [orbit_succ]
  simp only [unitAct]
  nlinarith

def terminal (D A B : ℤ) (p : ℤ × ℤ) : Prop :=
  (descend D A B p).1 ≤ 0 ∨ (descend D A B p).2 < 0

instance (D A B : ℤ) (p : ℤ × ℤ) : Decidable (terminal D A B p) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A terminal positive-quadrant seed lies in the proved finite descent box. -/
theorem terminal_bound {D A B N : ℤ} (hD : 0 < D) (hA : 1 < A) (hB : 0 < B)
    (hu : A^2-D*B^2=1) (p : ℤ × ℤ) (hx : 0 < p.1) (hy : 0 ≤ p.2)
    (hn : p.1^2-D*p.2^2=N) (ht : terminal D A B p) : D*p.2^2 ≤ |N| *A^2 := by
  obtain ⟨k,X,Y,hX,hY,hN,hbound,he⟩ := pell_descent_box hD hA hB hu p.1 p.2 hx hy hn
  cases k with
  | zero =>
    have he1 : X=p.1 := congrArg Prod.fst he
    have he2 : Y=p.2 := congrArg Prod.snd he
    simpa only [he2] using hbound
  | succ k =>
    have hprev := orbit_nonneg hD hA hB (X,Y) hX hY k
    have hd : descend D A B p = unitOrbit D A B (X,Y) k := by
      have hep : unitOrbit D A B (X,Y) (k+1)=p := he.trans (Prod.eta p)
      rw [← hep]
      rw [orbit_succ]
      exact descend_act hu _
    rcases ht with ht | ht <;> rw [hd] at ht <;> omega

/-- Terminal seeds cover every positive-root, nonnegative-input solution. -/
theorem terminal_exhaust {D A B N : ℤ} (hD : 0 < D) (hA : 1 < A) (hB : 0 < B)
    (hu : A^2-D*B^2=1) : ∀ X Y : ℤ, 0 < X → 0 ≤ Y → X^2-D*Y^2=N →
    ∃ p : ℤ × ℤ, 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1^2-D*p.2^2=N ∧
      D*p.2^2 ≤ |N| *A^2 ∧ terminal D A B p ∧ ∃ k, unitOrbit D A B p k=(X,Y) := by
  intro X
  induction X using Int.strongRec (m := 1) with
  | lt X hX => intro Y hx; omega
  | ge X _ ih =>
    intro Y hx hy hn
    by_cases ht : terminal D A B (X,Y)
    · exact ⟨(X,Y),hx,hy,hn,terminal_bound hD hA hB hu (X,Y) hx hy hn ht,ht,0,rfl⟩
    · have hdX : 0 < (descend D A B (X,Y)).1 := by
        simp only [terminal,not_or,not_le,not_lt] at ht
        exact ht.1
      have hdY : 0 ≤ (descend D A B (X,Y)).2 := by
        simp only [terminal,not_or,not_le,not_lt] at ht
        exact ht.2
      have he : unitAct D A B (descend D A B (X,Y))=(X,Y) := by
        convert unitAct_descend hu X Y using 1 <;> simp only [descend] <;> ring
      have hl : (descend D A B (X,Y)).1 < X := by
        have heX := congrArg Prod.fst he
        simp only [unitAct,Prod.fst] at heX
        have hdpos := mul_nonneg (mul_nonneg hD.le hdY) hB.le
        nlinarith
      have hnorm : (descend D A B (X,Y)).1^2-D*(descend D A B (X,Y)).2^2=N := by
        have hh := unitAct_norm hu (descend D A B (X,Y))
        rw [he] at hh
        exact hh.symm.trans hn
      obtain ⟨p,h1,h2,h3,h4,h5,k,hk⟩ := ih _ hl _ hdX hdY hnorm
      refine ⟨p,h1,h2,h3,h4,h5,k+1,?_⟩
      rw [unitOrbit,Function.iterate_succ_apply',← unitOrbit,hk,he]

end PerfectPower.PellOrbitCore
