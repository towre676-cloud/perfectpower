import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Notation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

set_option linter.unusedSectionVars false

noncomputable section
namespace PerfectPower.WeilSpectral
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K]

def Centralizes (C F T : Matrix ι ι K) : Prop := Commute C F ∧ Commute C T

theorem centralizes_mul {A B F T : Matrix ι ι K}
    (hA : Centralizes A F T) (hB : Centralizes B F T) : Centralizes (A*B) F T :=
  ⟨hA.1.mul_left hB.1,hA.2.mul_left hB.2⟩

theorem centralizes_add {A B F T : Matrix ι ι K}
    (hA : Centralizes A F T) (hB : Centralizes B F T) : Centralizes (A+B) F T :=
  ⟨hA.1.add_left hB.1,hA.2.add_left hB.2⟩

theorem centralizes_smul (r : K) {A F T : Matrix ι ι K}
    (hA : Centralizes A F T) : Centralizes (r • A) F T :=
  ⟨hA.1.smul_left r,hA.2.smul_left r⟩

theorem symmetric_product_iff {A B : Matrix ι ι K} (hA : A.IsSymm) (hB : B.IsSymm) :
    (A*B).IsSymm ↔ Commute A B := by
  change (A*B).transpose=A*B ↔ A*B=B*A
  rw [Matrix.transpose_mul,hA,hB]
  exact eq_comm

theorem commutative_of_symmetric (F T : Matrix ι ι K)
    (hs : ∀ C, Centralizes C F T → C.IsSymm)
    {A B : Matrix ι ι K} (hA : Centralizes A F T) (hB : Centralizes B F T) :
    Commute A B :=
  (symmetric_product_iff (hs A hA) (hs B hB)).mp (hs (A*B) (centralizes_mul hA hB))

/-- Gauged Weyl sums depend on x-y through support and x+y through phase. -/
def orbitKernel {R : Type*} [Fintype R] [AddCommGroup R] [DecidableEq R]
    (support : R → R → Bool) (phase : R → R → K) : Matrix R R K :=
  fun x y => ∑ t, if support (x-y) t then phase t (x+y) else 0

theorem reflecting_kernel_symmetric {R : Type*} [Fintype R] [AddCommGroup R] [DecidableEq R]
    (support : R → R → Bool) (phase : R → R → K)
    (hr : ∀ s t, support (-s) t = support s t) : (orbitKernel support phase).IsSymm := by
  ext x y
  change (∑ t, if support (y-x) t then phase t (y+x) else 0) =
    ∑ t, if support (x-y) t then phase t (x+y) else 0
  apply Finset.sum_congr rfl
  intro t _
  rw [show y-x = -(x-y) by abel,hr,add_comm y x]

/-- A polynomial commutator factor gives exact commutation at each root. -/
theorem polynomial_commute_of_factor {A B Q : Matrix ι ι (Polynomial ℚ)}
    (p : Polynomial ℚ) (hf : A*B-B*A=p • Q)
    (f : Polynomial ℚ →+* K) (hp : f p=0) : Commute (A.map f) (B.map f) := by
  have h := congrArg (fun M : Matrix ι ι (Polynomial ℚ) => M.map f) hf
  have hz : (p • Q).map f = 0 := by
    ext i j
    simp only [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,map_mul,hp,zero_mul,
      Matrix.zero_apply]
  change (A*B-B*A).map f=(p • Q).map f at h
  rw [hz] at h
  rw [Matrix.map_sub,Matrix.map_mul,Matrix.map_mul] at h
  · exact sub_eq_zero.mp h
  · intro a b; exact map_sub f a b

theorem centralizes_finset_sum {α : Type*} (s : Finset α) (A : α → Matrix ι ι K)
    (F T : Matrix ι ι K) (h : ∀ i ∈ s, Centralizes (A i) F T) :
    Centralizes (∑ i ∈ s,A i) F T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Centralizes]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact centralizes_add (h a (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem spectral_resolution {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Matrix ι ι K) (c : α → K)
    (hi : ∀ i,P i*P i=P i)
    (ho : ∀ i j,i≠j → P i*P j=0) (j : α) :
    (∑ i,c i • P i)*P j=c j • P j := by
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single j]
  · rw [smul_mul,hi]
  · intro i _ hij
    rw [smul_mul,ho i j hij,smul_zero]
  · simp

theorem projector_partition (P : Matrix ι ι K) : P+(1-P)=1 := by abel

theorem complementary_projectors (P : Matrix ι ι K) (h : P*P=P) :
    (1-P)*(1-P)=1-P ∧ P*(1-P)=0 ∧ (1-P)*P=0 := by
  simp [sub_mul,mul_sub,h]

end PerfectPower.WeilSpectral
