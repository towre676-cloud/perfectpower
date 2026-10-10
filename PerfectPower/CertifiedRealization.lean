import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Hankel-factorization lower bounds, with actual determinant hypotheses. -/
namespace PerfectPower.CertifiedRealization
open Matrix

/-- Any realization of a nonsingular r-by-r Hankel block needs at least r states. -/
theorem hankel_dimension_lower_bound {r m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℚ)
    (O : Matrix (Fin r) (Fin m) ℚ) (R : Matrix (Fin m) (Fin r) ℚ)
    (hfactor : H=O*R) (hdet : H.det ≠ 0) : r≤m := by
  have hunit : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hR : Function.Injective R.mulVecLin := by
    intro x y hxy
    apply hinj
    rw [hfactor,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
    exact congrArg O.mulVec hxy
  have hd := LinearMap.finrank_le_finrank_of_injective hR
  simpa using hd

def response {m : ℕ} (A : Matrix (Fin m) (Fin m) ℚ)
    (x C : Fin m → ℚ) (n : ℕ) : ℚ := dotProduct C ((A^n).mulVec x)

def hankel {m : ℕ} (r : ℕ) (A : Matrix (Fin m) (Fin m) ℚ)
    (x C : Fin m → ℚ) : Matrix (Fin r) (Fin r) ℚ :=
  fun i j => response A x C (i.val+j.val)

def observability {m : ℕ} (r : ℕ) (A : Matrix (Fin m) (Fin m) ℚ)
    (C : Fin m → ℚ) : Matrix (Fin r) (Fin m) ℚ :=
  fun i s => (C ᵥ* A^i.val) s

def reachability {m : ℕ} (r : ℕ) (A : Matrix (Fin m) (Fin m) ℚ)
    (x : Fin m → ℚ) : Matrix (Fin m) (Fin r) ℚ :=
  fun s j => ((A^j.val).mulVec x) s

theorem hankel_factorization {m : ℕ} (r : ℕ) (A : Matrix (Fin m) (Fin m) ℚ)
    (x C : Fin m → ℚ) :
    hankel r A x C = observability r A C * reachability r A x := by
  ext i j
  change dotProduct C ((A^(i.val+j.val)).mulVec x) =
    dotProduct (C ᵥ* A^i.val) ((A^j.val).mulVec x)
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,← pow_add]

/-- The lower bound is tied to an actual all-time response sequence. -/
theorem response_hankel_lower_bound {m : ℕ} (r : ℕ) (A : Matrix (Fin m) (Fin m) ℚ)
    (x C : Fin m → ℚ) (h : (hankel r A x C).det ≠ 0) : r≤m := by
  apply hankel_dimension_lower_bound (hankel r A x C)
    (fun i s => (C ᵥ* A^i.val) s) (fun s j => ((A^j.val).mulVec x) s)
    (hankel_factorization r A x C) h

/-- An r-state response with a nonzero r-Hankel determinant is minimal. -/
theorem realization_minimal {r m : ℕ}
    (A : Matrix (Fin r) (Fin r) ℚ) (x C : Fin r → ℚ)
    (T : Matrix (Fin m) (Fin m) ℚ) (y D : Fin m → ℚ)
    (hsame : ∀ n, response A x C n=response T y D n)
    (hdet : (hankel r A x C).det ≠ 0) : r≤m := by
  apply response_hankel_lower_bound r T y D
  have hh : hankel r A x C=hankel r T y D := by
    ext i j
    exact hsame _
  rwa [← hh]

/-- Coordinate encodings commute with every future transition power. -/
theorem all_future_transport {X Y : Type*} (A : X → X) (G : Y → Y) (E : X → Y)
    (h : ∀ x, E (A x)=G (E x)) (x : X) :
    ∀ n, E (A^[n] x)=G^[n] (E x) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',h,ih]

/-- A protected readout preserves the entire sequence, not just a prefix. -/
theorem all_future_readout {X Y Z : Type*} (A : X → X) (G : Y → Y) (E : X → Y)
    (C : X → Z) (D : Y → Z) (hstep : ∀ x, E (A x)=G (E x))
    (hread : ∀ x, C x=D (E x)) (x : X) (n : ℕ) :
    C (A^[n] x)=D (G^[n] (E x)) := by
  rw [hread,all_future_transport A G E hstep x n]

def fibonacciA : Matrix (Fin 2) (Fin 2) ℚ := !![0,1;1,1]
def fibonacciX : Fin 2 → ℚ := ![0,1]
def fibonacciC : Fin 2 → ℚ := ![1,0]

theorem fibonacci_hankel_nonsingular : (hankel 2 fibonacciA fibonacciX fibonacciC).det ≠ 0 := by
  norm_num [hankel,response,fibonacciA,fibonacciX,fibonacciC,Matrix.det_fin_two,
    Matrix.mulVec,dotProduct,Fin.sum_univ_two,pow_succ,Matrix.mul_apply]

theorem fibonacci_minimal {m : ℕ} (T : Matrix (Fin m) (Fin m) ℚ) (y D : Fin m → ℚ)
    (hsame : ∀ n, response fibonacciA fibonacciX fibonacciC n=response T y D n) : 2≤m :=
  realization_minimal fibonacciA fibonacciX fibonacciC T y D hsame fibonacci_hankel_nonsingular

end PerfectPower.CertifiedRealization
