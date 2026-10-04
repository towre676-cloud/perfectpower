import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

namespace PerfectPower.BranchedGeometry
open Matrix
open scoped ComplexOrder

/-- Exact finite Gauss-Bonnet face charge, with the cell hypotheses explicit. -/
theorem trivalent_charge (V E F q : ℤ) (hv : 3*V=2*E) (hq : q=2*E) :
    6*F-q=6*(V-E+F) := by omega

/-- The arithmetic form of Riemann-Hurwitz, given its ramification inputs. -/
theorem hurwitz_euler (d delta m finite infinity chi : ℤ)
    (hf : finite=m*(d-1)) (hi : infinity=d-delta)
    (hc : chi=2*d-finite-infinity) : chi=d+delta-m*(d-1) := by omega

/-- Finite connection energy has exactly the kernel of its incidence operator. -/
theorem gram_kernel {e v : Type*} [Fintype e] [Fintype v]
    (B : Matrix e v ℂ) (f : v → ℂ) :
    (B.conjTranspose*B) *ᵥ f=0 ↔ B *ᵥ f=0 :=
  Matrix.conjTranspose_mul_self_mulVec_eq_zero B f

theorem gram_energy {e v : Type*} [Fintype e] [Fintype v]
    (B : Matrix e v ℂ) (f : v → ℂ) :
    star f ⬝ᵥ ((B.conjTranspose*B) *ᵥ f) =
      star (B *ᵥ f) ⬝ᵥ (B *ᵥ f) := by
  rw [← mulVec_mulVec,dotProduct_mulVec]
  simp only [vecMul_conjTranspose,star_star]

/-- A nonzero common seed survives all cycle transports exactly when they are trivial. -/
theorem parallel_seed_iff {ι : Type*} (U : ι → ℂ) :
    (∃ z : ℂ, z ≠ 0 ∧ ∀ i, z=U i*z) ↔ ∀ i, U i=1 := by
  constructor
  · rintro ⟨z,hz,h⟩ i
    apply mul_right_cancel₀ hz
    simpa using (h i).symm
  · intro h
    exact ⟨1,one_ne_zero,by intro i; simp [h i]⟩

/-- Faithful root-of-unity holonomy detects divisibility of every multiplicity. -/
theorem cyclic_seed_iff {ι : Type*} (d : ℕ) (zeta : ℂ)
    (hzeta : IsPrimitiveRoot zeta d) (r : ι → ℕ) :
    (∃ z : ℂ, z ≠ 0 ∧ ∀ i, z=zeta^(r i)*z) ↔ ∀ i, d ∣ r i := by
  rw [parallel_seed_iff]
  exact forall_congr' fun i => hzeta.pow_eq_one_iff_dvd (r i)

/-- Polynomial powers satisfy the corresponding first-order holonomic identity. -/
theorem polynomial_power_differential (Q : Polynomial ℂ) (d : ℕ) :
    Polynomial.C (d : ℂ)*(Q^d)*Polynomial.derivative Q =
      Polynomial.derivative (Q^d)*Q := by
  cases d with
  | zero => simp
  | succ n =>
    rw [Polynomial.derivative_pow_succ]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    ring

end PerfectPower.BranchedGeometry

namespace PerfectPower.BranchedGeometry
open Matrix
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev BouquetVertex (ι : Type*) := Option (ι × Fin 2)
def bouquetMatrix (U : ι → ℂ) : Matrix (ι × Fin 3) (BouquetVertex ι) ℂ := fun e =>
  if e.2=0 then Pi.single none 1 - Pi.single (some (e.1,0)) 1
  else if e.2=1 then Pi.single (some (e.1,0)) 1 - Pi.single (some (e.1,1)) 1
  else Pi.single (some (e.1,1)) 1 - Pi.single none (U e.1)

lemma single_sub_dot (a b : BouquetVertex ι) (c : ℂ) (f : BouquetVertex ι → ℂ) :
    (fun j => Pi.single a 1 j-Pi.single b c j) ⬝ᵥ f=f a-c*f b := by
  change (Pi.single a 1-Pi.single b c) ⬝ᵥ f=f a-c*f b
  rw [sub_dotProduct,single_dotProduct,single_dotProduct,one_mul]

 theorem bouquet_kernel (U : ι → ℂ) (f : BouquetVertex ι → ℂ) :
    bouquetMatrix U *ᵥ f=0 ↔ ∀ i,
      f (some (i,0))=f none ∧ f (some (i,1))=f none ∧ f none=U i*f none := by
  constructor
  · intro h i
    have h0 := congrFun h (i,0)
    have h1 := congrFun h (i,1)
    have h2 := congrFun h (i,2)
    simp [bouquetMatrix,Matrix.mulVec,single_sub_dot,sub_eq_zero] at h0 h1 h2
    refine ⟨h0.symm,?_,?_⟩
    · exact h1.symm.trans h0.symm
    · exact h0.trans (h1.trans h2)
  · intro h
    funext e
    rcases e with ⟨i,k⟩
    obtain ⟨h0,h1,h2⟩ := h i
    fin_cases k <;> simp [bouquetMatrix,Matrix.mulVec,single_sub_dot,h0,h1]
    exact sub_eq_zero.mpr h2

/-- The exact faithful connection Laplacian statement on a root-detecting bouquet. -/
theorem bouquet_spectral_iff (U : ι → ℂ) :
    (∃ f : BouquetVertex ι → ℂ, f ≠ 0 ∧
      ((bouquetMatrix U).conjTranspose*bouquetMatrix U) *ᵥ f=0) ↔ ∀ i,U i=1 := by
  constructor
  · rintro ⟨f,hf,hL⟩
    have hp := (bouquet_kernel U f).mp ((gram_kernel _ f).mp hL)
    have hn : f none ≠ 0 := by
      intro hz
      apply hf
      funext v
      cases v with
      | none => exact hz
      | some v =>
        rcases v with ⟨i,k⟩
        fin_cases k
        · exact (hp i).1.trans hz
        · exact (hp i).2.1.trans hz
    exact (parallel_seed_iff U).mp ⟨f none,hn,fun i => (hp i).2.2⟩
  · intro h
    refine ⟨fun _ => 1,?_,?_⟩
    · intro hz
      have he := congrFun hz none
      simpa using he
    · apply (gram_kernel _ _).mpr
      apply (bouquet_kernel _ _).mpr
      intro i
      simp [h i]

 theorem bouquet_cyclic_iff (d : ℕ) (zeta : ℂ) (hzeta : IsPrimitiveRoot zeta d)
    (r : ι → ℕ) :
    (∃ f : BouquetVertex ι → ℂ, f ≠ 0 ∧
      ((bouquetMatrix (fun i => zeta^(r i))).conjTranspose*
        bouquetMatrix (fun i => zeta^(r i))) *ᵥ f=0) ↔ ∀ i,d ∣ r i := by
  rw [bouquet_spectral_iff]
  exact forall_congr' fun i => hzeta.pow_eq_one_iff_dvd (r i)

/-- Finite Hodge harmonicity is exactly closedness and coclosedness. -/
theorem hodge_one_kernel {v e f : Type*} [Fintype v] [Fintype e] [Fintype f]
    (D1 : Matrix v e ℂ) (D2 : Matrix e f ℂ) (x : e → ℂ) :
    (D1.conjTranspose*D1+D2*D2.conjTranspose) *ᵥ x=0 ↔
      D1 *ᵥ x=0 ∧ D2.conjTranspose *ᵥ x=0 := by
  have h := gram_kernel (Matrix.fromRows D1 D2.conjTranspose) x
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows,Matrix.conjTranspose_conjTranspose,
    Matrix.fromRows_mulVec] at h
  rw [h]
  constructor
  · intro hz
    constructor
    · funext i; exact congrFun hz (Sum.inl i)
    · funext i; exact congrFun hz (Sum.inr i)
  · rintro ⟨h1,h2⟩
    ext (i | i) <;> simp [h1,h2]
end PerfectPower.BranchedGeometry
