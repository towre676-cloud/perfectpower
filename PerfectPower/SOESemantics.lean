import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.Basic

namespace PerfectPower.SOESemantics

/-- A deterministic partial action preserves disabled-action information. -/
def run {S A : Type*} (step : S → A → Option S) (s : S) : List A → Option S
  | [] => some s
  | a :: w => (step s a).bind (fun t => run step t w)

def behavior {S A O : Type*} (step : S → A → Option S) (obs : S → O)
    (s : S) (w : List A) : Option O := (run step s w).map obs

def Equivalent {S A O : Type*} (step : S → A → Option S) (obs : S → O)
    (s t : S) : Prop := ∀ w, behavior step obs s w = behavior step obs t w

/-- Homomorphism replay covers every future action word, without a depth cutoff. -/
theorem run_transport {S T A : Type*} (step : S → A → Option S)
    (target : T → A → Option T) (q : S → T)
    (h : ∀ s a, (step s a).map q = target (q s) a) (s : S) (w : List A) :
    (run step s w).map q = run target (q s) w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp only [run]
    rw [← h s a]
    cases hs : step s a with
    | none => rfl
    | some t => simpa using ih t

/-- Observations and action legality commute with the quotient for arbitrary words. -/
theorem behavior_transport {S T A O : Type*} (step : S → A → Option S)
    (target : T → A → Option T) (obs : S → O) (out : T → O) (q : S → T)
    (ho : ∀ s, obs s = out (q s))
    (ht : ∀ s a, (step s a).map q = target (q s) a) (s : S) (w : List A) :
    behavior step obs s w = behavior target out (q s) w := by
  unfold behavior
  rw [← run_transport step target q ht s w]
  cases run step s w with
  | none => rfl
  | some t => simpa using ho t

/-- Pair-separating words plus homomorphism replay prove the coarsest quotient. -/
theorem quotient_complete {S T A O : Type*} (step : S → A → Option S)
    (target : T → A → Option T) (obs : S → O) (out : T → O) (q : S → T)
    (ho : ∀ s, obs s = out (q s))
    (ht : ∀ s a, (step s a).map q = target (q s) a)
    (sep : ∀ s t, q s ≠ q t → ∃ w, behavior step obs s w ≠ behavior step obs t w)
    (s t : S) : Equivalent step obs s t ↔ q s = q t := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨w, hw⟩ := sep s t hn
    exact hw (he w)
  · intro hq w
    rw [behavior_transport step target obs out q ho ht,
      behavior_transport step target obs out q ho ht, hq]

/-- A supplied distinguishing word really refutes all-future equivalence. -/
theorem witness_sound {S A O : Type*} (step : S → A → Option S) (obs : S → O)
    (s t : S) (w : List A) (h : behavior step obs s w ≠ behavior step obs t w) :
    ¬ Equivalent step obs s t := by intro he; exact h (he w)

/-- Exact finite-menu Bellman certificates: attainability plus domination. -/
theorem minimum_cost {P : Type*} (legal : P → Prop) (cost : P → ℚ)
    (chosen : P) (hc : legal chosen) (lower : ℚ)
    (attain : cost chosen = lower) (bound : ∀ p, legal p → lower ≤ cost p) :
    legal chosen ∧ ∀ p, legal p → cost chosen ≤ cost p := by
  constructor
  · exact hc
  · intro p hp
    rw [attain]
    exact bound p hp

/-- Sequential semiring valuations preserve both multiplication and alternative sums. -/
theorem valuation_transport {R T : Type*} [Semiring R] [Semiring T]
    (f : R →+* T) (p q r : R) : f (p*q+r) = f p*f q+f r := by simp

end PerfectPower.SOESemantics
