import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import PerfectPower.StructuralSpecies

namespace PerfectPower.AdaptiveDiagnosis

def outcome (probe : Fin 3) (s : Fin 4) : Bool :=
  if probe=0 then decide (2 ≤ s.val)
  else if probe=1 then decide (s=1)
  else decide (s=3)

inductive Policy where
  | leaf : Fin 4 → Policy
  | node : Fin 3 → Policy → Policy → Policy

def predict : Policy → Fin 4 → Fin 4
  | .leaf t, _ => t
  | .node p left right, s => if outcome p s then predict right s else predict left s

def cost : Policy → ℕ
  | .leaf _ => 0
  | .node _ left right => 1+max (cost left) (cost right)

def correct (p : Policy) : Prop := ∀ s, predict p s=s

def optimal : Policy := .node 0 (.node 1 (.leaf 0) (.leaf 1)) (.node 2 (.leaf 2) (.leaf 3))

theorem optimal_correct : correct optimal := by unfold correct; decide

theorem optimal_cost : cost optimal=2 := by rfl

theorem zero_cost_leaf (p : Policy) (h : cost p=0) : ∃ t, p=.leaf t := by
  cases p with
  | leaf t => exact ⟨t,rfl⟩
  | node a l r => simp [cost] at h

/-- Every first probe has a collision, so no one-measurement policy succeeds. -/
theorem lower_bound (p : Policy) (hc : correct p) : 2 ≤ cost p := by
  by_contra h
  have small : cost p ≤ 1 := by omega
  cases p with
  | leaf t =>
    have h0 := hc 0
    have h1 := hc 1
    simp only [predict] at h0 h1
    have : (0 : Fin 4) = 1 := h0.symm.trans h1
    exact (by decide : (0 : Fin 4) ≠ 1) this
  | node a l r =>
    have hl : cost l=0 := by simp only [cost] at small; omega
    have hr : cost r=0 := by simp only [cost] at small; omega
    obtain ⟨x,rfl⟩ := zero_cost_leaf l hl
    obtain ⟨y,rfl⟩ := zero_cost_leaf r hr
    have collision : ∃ s t : Fin 4, s≠t ∧ outcome a s=outcome a t := by
      have all : ∀ a : Fin 3, ∃ s t : Fin 4, s≠t ∧ outcome a s=outcome a t := by decide
      exact all a
    obtain ⟨s,t,hst,ho⟩ := collision
    have hs := hc s
    have ht := hc t
    simp only [predict] at hs ht
    rw [ho] at hs
    exact hst (hs.symm.trans ht)

/-- All three fixed probes identify the state; every two-probe menu has a collision. -/
theorem fixed_three : ∀ s t : Fin 4,
    (outcome 0 s,outcome 1 s,outcome 2 s)=(outcome 0 t,outcome 1 t,outcome 2 t) → s=t := by decide

theorem fixed_two_fail : ∀ a b : Fin 3, ∃ s t : Fin 4,
    s≠t ∧ (outcome a s,outcome b s)=(outcome a t,outcome b t) := by decide

end PerfectPower.AdaptiveDiagnosis
