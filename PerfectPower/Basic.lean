import Mathlib

open Filter Topology
open scoped Classical

namespace PerfectPower

/-- `v` is a `d`-th power of an integer (integer-power convention; `d ≥ 2` is imposed by callers). -/
def IsHit (d : ℕ) (v : ℤ) : Prop := ∃ m : ℤ, v = m ^ d

/-- Index set of hits, indexed from `n = 1`. -/
def hitSet (S : ℕ → ℤ) (d : ℕ) (k : ℤ) : Set ℕ := {n | 1 ≤ n ∧ IsHit d (S n + k)}

/-- Cumulative hit count `A_{S,d,k}(N)`. -/
noncomputable def A (S : ℕ → ℤ) (d : ℕ) (k : ℤ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => IsHit d (S n + k))).card

/-- The density sequence `A(N)/N`. -/
noncomputable def ratio (S : ℕ → ℤ) (d : ℕ) (k : ℤ) (N : ℕ) : ℝ := (A S d k N : ℝ) / N

def HasDensity (S : ℕ → ℤ) (d : ℕ) (k : ℤ) (L : ℝ) : Prop :=
  Tendsto (ratio S d k) atTop (𝓝 L)

/-- Upper density `H_d^S(k)`. -/
noncomputable def H (S : ℕ → ℤ) (d : ℕ) (k : ℤ) : ℝ := limsup (ratio S d k) atTop

/-- Convergence bridge: an existing density is the upper density. -/
theorem H_eq_of_hasDensity {S : ℕ → ℤ} {d : ℕ} {k : ℤ} {L : ℝ}
    (h : HasDensity S d k L) : H S d k = L :=
  h.limsup_eq

end PerfectPower
