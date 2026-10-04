import Mathlib
namespace PerfectPower.OrbitRecovery
open Matrix

variable {V W Y : Type*}

def orbit (A : V → V) (v : V) : ℕ → V
  | 0 => v
  | n+1 => A (orbit A v n)

/-- A commuting transport carries the entire orbit, not just its first states. -/
theorem transport (A : V → V) (B : W → W) (C : W → V)
    (h : ∀ w, A (C w)=C (B w)) (w : W) :
    ∀ n, orbit A (C w) n=C (orbit B w n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit,ih,h]

/-- Finite-dimensional matrix certificates instantiate this generic invariant
receiver theorem; basis independence is unnecessary for zero-output soundness. -/
theorem zero_output (A : V → V) (B : W → W) (C : W → V) (readout : V → Y)
    (zero : Y) (hC : ∀ w, A (C w)=C (B w))
    (hzero : ∀ w, readout (C w)=zero) (w : W) :
    ∀ n, readout (orbit A (C w) n)=zero := by
  intro n
  rw [transport A B C hC w n,hzero]

/-- An invariant subspace containing the seed and killed by the readout proves
an all-future zero identity. -/
theorem invariant_zero {R : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid Y] [Module R Y] (A : V →ₗ[R] V) (readout : V →ₗ[R] Y)
    (S : Submodule R V) (hstable : ∀ v ∈ S, A v ∈ S)
    (hzero : ∀ v ∈ S, readout v=0) (v : V) (hv : v ∈ S) :
    ∀ n, readout (orbit A v n)=0 := by
  have hs : ∀ n, orbit A v n ∈ S := by
    intro n
    induction n with
    | zero => exact hv
    | succ n ih => exact hstable _ ih
  intro n
  exact hzero _ (hs n)
/-- Finite rational matrices certify every future output by checking two
matrix identities and one seed representation. -/
theorem matrix_zero {n k m : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℚ) (B : Matrix k k ℚ) (C : Matrix n k ℚ)
    (H : Matrix m n ℚ) (z : k → ℚ)
    (hC : A*C=C*B) (hH : H*C=0) :
    ∀ t, H *ᵥ orbit (fun v => A *ᵥ v) (C *ᵥ z) t=0 := by
  apply zero_output (fun v => A *ᵥ v) (fun w => B *ᵥ w)
    (fun w => C *ᵥ w) (fun v => H *ᵥ v) 0 _ _ z
  · intro w
    dsimp only
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hC]
  · intro w
    dsimp only
    rw [Matrix.mulVec_mulVec,hH,Matrix.zero_mulVec]

/-- A left annihilator is an exact obstruction to a supplied task lift. -/
theorem lift_obstruction {R : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    [AddCommMonoid Y] [Module R Y]
    (F : W →ₗ[R] Y) (G : V →ₗ[R] Y) (a : Y →ₗ[R] R) (w : W)
    (hG : a.comp G=0) (hF : a (F w) ≠ 0) :
    ¬ ∃ T : W →ₗ[R] V, G.comp T=F := by
  rintro ⟨T,hT⟩
  apply hF
  have ht := congrArg (fun f : W →ₗ[R] Y => a (f w)) hT
  have hg := congrArg (fun f : V →ₗ[R] R => f (T w)) hG
  simpa using ht.symm.trans hg

end PerfectPower.OrbitRecovery
