import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Exact spectral moment inversion. Algebraic source identities, not a
formalization of the physical mass diagonalization or measurement process.
-/
namespace PerfectPower.SpectralMoments
open Matrix
open scoped Matrix
variable {K : Type*} [Field K]

def vandermonde (a b c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1,1,1; a,b,c; a^2,b^2,c^2]

def lagrange (a b c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![b*c/((a-b)*(a-c)), -(b+c)/((a-b)*(a-c)), 1/((a-b)*(a-c));
     a*c/((b-a)*(b-c)), -(a+c)/((b-a)*(b-c)), 1/((b-a)*(b-c));
     a*b/((c-a)*(c-b)), -(a+b)/((c-a)*(c-b)), 1/((c-a)*(c-b))]

theorem lagrange_vandermonde (a b c : K) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    lagrange a b c * vandermonde a b c = 1 := by
  have hba : b-a≠0 := sub_ne_zero.mpr hab.symm
  have hca : c-a≠0 := sub_ne_zero.mpr hac.symm
  have hcb : c-b≠0 := sub_ne_zero.mpr hbc.symm
  have hab' : a-b≠0 := sub_ne_zero.mpr hab
  have hac' : a-c≠0 := sub_ne_zero.mpr hac
  have hbc' : b-c≠0 := sub_ne_zero.mpr hbc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lagrange,vandermonde,Matrix.mul_apply,Fin.sum_univ_three,Matrix.one_apply] <;>
    field_simp <;> ring

/-- Recover the literal matrix from all nine mixed moments. -/
theorem recover (a b c d e f : K) (P : Matrix (Fin 3) (Fin 3) K)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hde : d≠e) (hdf : d≠f) (hef : e≠f) :
    lagrange a b c * (vandermonde a b c * P * (vandermonde d e f).transpose) *
      (lagrange d e f).transpose = P := by
  have hU := lagrange_vandermonde a b c hab hac hbc
  have hD := lagrange_vandermonde d e f hde hdf hef
  calc
    _ = (lagrange a b c * vandermonde a b c) * P *
        ((vandermonde d e f).transpose * (lagrange d e f).transpose) := by
          simp only [Matrix.mul_assoc]
    _ = P := by rw [hU,← Matrix.transpose_mul,hD]; simp

theorem moments_injective (a b c d e f : K)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hde : d≠e) (hdf : d≠f) (hef : e≠f) :
    Function.Injective (fun P : Matrix (Fin 3) (Fin 3) K =>
      vandermonde a b c * P * (vandermonde d e f).transpose) := by
  intro P Q he
  have h := congrArg (fun M => lagrange a b c * M * (lagrange d e f).transpose) he
  simpa only [recover a b c d e f _ hab hac hbc hde hdf hef] using h

/-- Quartic potentials in one trace moment have a rank-one outer-product Hessian. -/
theorem moment_hessian_vanishes {ι : Type*} [Fintype ι]
    (w v : ι → K) (c : K) (hv : ∑ j,w j*v j=0) (i : ι) :
    (∑ j,(c*w i*w j)*v j)=0 := by
  calc
    _ = c*w i*(∑ j,w j*v j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hv,mul_zero]

end PerfectPower.SpectralMoments
