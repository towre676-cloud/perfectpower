import Mathlib

noncomputable section
namespace PerfectPower.FiniteWeilAlgebra
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K]

/-- A diagonal chirp imposes exact support restrictions on every commuting matrix. -/
theorem diagonal_support (C : Matrix ι ι K) (t : ι → K)
    (h : C*diagonal t=diagonal t*C) (i j : ι) (hne : t i ≠ t j) : C i j=0 := by
  have he := congrFun (congrFun h i) j
  simp only [mul_diagonal,diagonal_mul] at he
  have hz : C i j*(t j-t i)=0 := by rw [mul_sub,he];ring
  rcases mul_eq_zero.mp hz with hz | hz
  · exact hz
  · exact False.elim (hne (sub_eq_zero.mp hz).symm)

/-- A simple clock spectrum makes its whole commutant diagonal. -/
theorem clock_diagonal (C : Matrix ι ι K) (t : ι → K) (ht : Function.Injective t)
    (h : C*diagonal t=diagonal t*C) : C=diagonal (fun i => C i i) := by
  ext i j
  by_cases he : i=j
  · subst j;simp
  · rw [diagonal_apply_ne _ he]
    exact diagonal_support C t h i j (fun hh => he (ht hh))

def shift (σ : ι → ι) : Matrix ι ι K := fun i j => if i=σ j then 1 else 0

/-- Commuting with a shift forces equality along every shift edge. -/
theorem shift_invariance (d : ι → K) (σ : ι → ι)
    (h : diagonal d*(shift σ : Matrix ι ι K)=
      (shift σ : Matrix ι ι K)*diagonal d) : ∀ j,d (σ j)=d j := by
  intro j
  have he := congrFun (congrFun h (σ j)) j
  simpa [diagonal_mul,mul_diagonal,shift] using he

/-- The transitive clock/shift carrier has only scalar commuting matrices. -/
theorem clock_shift_scalar (C : Matrix ι ι K) (t : ι → K) (σ : ι → ι) (base : ι)
    (ht : Function.Injective t) (hT : C*diagonal t=diagonal t*C)
    (hS : C*(shift σ : Matrix ι ι K)=(shift σ : Matrix ι ι K)*C)
    (horbit : ∀ i,∃ n,σ^[n] base=i) : C=diagonal (fun _ => C base base) := by
  have hd := clock_diagonal C t ht hT
  rw [hd] at hS
  have hf := shift_invariance (fun i => C i i) σ hS
  change ∀ j,C (σ j) (σ j)=C j j at hf
  have hi (n : ℕ) (i : ι) : C (σ^[n] i) (σ^[n] i)=C i i := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',hf,ih]
  calc C=diagonal (fun i => C i i) := hd
    _=diagonal (fun _ => C base base) := by
      apply congrArg Matrix.diagonal
      funext i
      obtain ⟨n,hn⟩ := horbit i
      simpa [hn] using hi n base

/-- The recovered CRT section retains its twists; cross terms vanish modulo ab. -/
theorem crt_phase (a b u v s t : ℤ) :
    a*b ∣ (b*u+a*v)*(b*s+a*t)-(b^2*u*s+a^2*v*t) := by
  refine ⟨u*t+v*s,?_⟩
  ring

theorem crt_chirp (a b u v : ℤ) :
    a*b ∣ (b*u+a*v)^2-(b^2*u^2+a^2*v^2) := by
  refine ⟨2*u*v,?_⟩
  ring

end PerfectPower.FiniteWeilAlgebra
