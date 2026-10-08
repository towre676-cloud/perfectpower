import PerfectPower.SpectralMoments
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.ConjTranspose

/-! The exact trace-to-mixing-moment bridge, with explicitly supplied frames.
This proves the matrix algebra; it assumes no measured masses or CKM entries.
-/
namespace PerfectPower.SpectralMoments
open scoped BigOperators
open Matrix

/-- Diagonal spectral traces are weighted moments of entrywise mixing squares. -/
theorem diagonal_trace_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [CommRing K] [StarRing K]
    (a b : ι → K) (U : Matrix ι ι K) :
    trace (diagonal a * U * diagonal b * U.conjTranspose)=
      ∑ i, ∑ j, a i*b j*(U i j*star (U i j)) := by
  simp only [trace,diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- For two supplied spectral frames, the mixing frame is U†V. -/
theorem spectral_frame_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [CommRing K] [StarRing K]
    (a b : ι → K) (U V : Matrix ι ι K) :
    trace ((U * diagonal a * U.conjTranspose)*(V * diagonal b * V.conjTranspose))=
      ∑ i, ∑ j, a i*b j*((U.conjTranspose*V) i j*star ((U.conjTranspose*V) i j)) := by
  have he : (U * diagonal a * U.conjTranspose)*(V * diagonal b * V.conjTranspose)=
      U*(diagonal a*(U.conjTranspose*V)*diagonal b*V.conjTranspose) := by
    simp only [Matrix.mul_assoc]
  rw [he,Matrix.trace_mul_comm]
  have ht : (diagonal a*(U.conjTranspose*V)*diagonal b*V.conjTranspose)*U=
      diagonal a*(U.conjTranspose*V)*diagonal b*(U.conjTranspose*V).conjTranspose := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [ht]
  exact diagonal_trace_moments a b (U.conjTranspose*V)

/-- Powers transport through a supplied unitary frame, including exponent zero. -/
theorem spectral_frame_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [CommRing K] [StarRing K]
    (U D : Matrix ι ι K) (hu : U.conjTranspose*U=1) (uh : U*U.conjTranspose=1)
    (n : ℕ) : (U*D*U.conjTranspose)^n=U*D^n*U.conjTranspose := by
  induction n with
  | zero => simpa using uh.symm
  | succ n ih =>
    rw [pow_succ,ih]
    calc
      _ = U*D^n*(U.conjTranspose*U)*D*U.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = U*D^(n+1)*U.conjTranspose := by
        rw [hu]
        simp only [Matrix.mul_one,pow_succ,Matrix.mul_assoc]

/-- Mixed powers of two diagonalized matrices give exactly the spectral moments.
Diagonalization and unitarity are explicit mathematical hypotheses. -/
theorem diagonalized_power_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [CommRing K] [StarRing K]
    (A B U V : Matrix ι ι K) (a b : ι → K)
    (ha : A=U*diagonal a*U.conjTranspose) (hb : B=V*diagonal b*V.conjTranspose)
    (hu : U.conjTranspose*U=1) (uh : U*U.conjTranspose=1)
    (hv : V.conjTranspose*V=1) (vh : V*V.conjTranspose=1) (p q : ℕ) :
    trace (A^p*B^q)=∑ i, ∑ j, a i^p*b j^q*
      ((U.conjTranspose*V) i j*star ((U.conjTranspose*V) i j)) := by
  rw [ha,hb,spectral_frame_power U (diagonal a) hu uh p,
    spectral_frame_power V (diagonal b) hv vh q,Matrix.diagonal_pow,Matrix.diagonal_pow]
  simpa only [Pi.pow_apply] using spectral_frame_trace (a^p) (b^q) U V

end PerfectPower.SpectralMoments
