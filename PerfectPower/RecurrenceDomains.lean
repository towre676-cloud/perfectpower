import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

namespace PerfectPower.RecurrenceDomains

/-- A unit denominator makes the next value unique over any commutative ring. -/
theorem unit_step {R : Type*} [CommRing R] (p q a b : R) (u : Rˣ)
    (hq : (u : R) = q) : q * b = p * a ↔ b = (↑u⁻¹ : R) * (p * a) := by
  subst q
  constructor
  · intro h
    have he := congrArg (fun x : R => (↑u⁻¹ : R) * x) h
    simpa only [← mul_assoc,Units.inv_mul,mul_one,one_mul] using he
  · intro h
    rw [h,← mul_assoc,Units.mul_inv,one_mul]

/-- Every finite repeated deterministic state repeats for all future offsets. -/
theorem repeat_future {α : Type*} (f : α → α) (s : α) (μ T : ℕ)
    (h : f^[μ+T] s = f^[μ] s) (n : ℕ) :
    f^[μ+n+T] s = f^[μ+n] s := by
  have he := congrArg (f^[n]) h
  simpa only [← Function.iterate_add_apply, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using he

/-- Any observable inherits the checked state period. -/
theorem observable_period {α β : Type*} (f : α → α) (s : α) (readout : α → β)
    (μ T : ℕ) (h : f^[μ+T] s = f^[μ] s) (n : ℕ) :
    readout (f^[μ+n+T] s) = readout (f^[μ+n] s) := by
  rw [repeat_future f s μ T h n]

/-- The hit predicate, and not only the numeric value, is periodic. -/
theorem hit_period {α : Type*} (f : α → α) (s : α) (hit : α → Prop)
    (μ T : ℕ) (h : f^[μ+T] s = f^[μ] s) (n : ℕ) :
    hit (f^[μ+n+T] s) ↔ hit (f^[μ+n] s) := by
  rw [repeat_future f s μ T h n]

/-- Index-dependent coefficients require a phase in the state. -/
def phaseStep (m : ℕ) (next : ℕ → ℤ → ℤ) (state : ℕ × ℤ) : ℕ × ℤ :=
  ((state.1+1)%m,next state.1 state.2)

theorem phase_step (m : ℕ) (next : ℕ → ℤ → ℤ) (phase : ℕ) (a : ℤ) :
    (phaseStep m next (phase,a)).1 = (phase+1)%m := rfl

/-- Singular equations can be inconsistent; they do not define a transition. -/
theorem zero_denominator {R : Type*} [Ring R] (rhs b : R) :
    (0 : R) * b = rhs ↔ rhs = 0 := by simp [eq_comm]

/-- Stored fibre evidence composes without identifying different original inputs. -/
theorem image_readout {α β γ : Type*} (T : α → β) (readout : α → γ)
    (u : β) (X : Set α) (cert : ∀ x, T x = u ↔ x ∈ X) (v : γ) :
    (∃ x, T x = u ∧ readout x = v) ↔ ∃ x ∈ X, readout x = v := by
  simp only [cert]

end PerfectPower.RecurrenceDomains
