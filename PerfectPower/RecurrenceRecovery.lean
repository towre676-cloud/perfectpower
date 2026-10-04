import Mathlib
namespace PerfectPower.RecurrenceRecovery

/-- Three initial values and the recurrence prove equality at every index. -/
theorem order_three_unique {R : Type*} [Semiring R] (a b c : R) (f g : ℕ → R)
    (hf : ∀ n, f (n+3)=a*f n+b*f (n+1)+c*f (n+2))
    (hg : ∀ n, g (n+3)=a*g n+b*g (n+1)+c*g (n+2))
    (h0 : f 0=g 0) (h1 : f 1=g 1) (h2 : f 2=g 2) : ∀ n, f n=g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · exact h0
    rcases n with _ | n
    · exact h1
    rcases n with _ | n
    · exact h2
    change f (n+3)=g (n+3)
    rw [hf,hg,ih n (by omega),ih (n+1) (by omega),ih (n+2) (by omega)]

/-- Padovan identification requires a proved recurrence, not a prefix match. -/
theorem padovan_unique {R : Type*} [Semiring R] (f g : ℕ → R)
    (hf : ∀ n, f (n+3)=f (n+1)+f n)
    (hg : ∀ n, g (n+3)=g (n+1)+g n)
    (h0 : f 0=g 0) (h1 : f 1=g 1) (h2 : f 2=g 2) : f=g := by
  funext n
  apply order_three_unique 1 1 0 f g _ _ h0 h1 h2 n
  · intro k; simpa [add_comm] using hf k
  · intro k; simpa [add_comm] using hg k
end PerfectPower.RecurrenceRecovery
