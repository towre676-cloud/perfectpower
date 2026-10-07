/-
Copyright 2026 OpenAI. Adapted for PerfectPower from openai/math
adc7f1241b42e322a6451854ab7e4b4c146bf78a, under Apache-2.0.
See third_party/openai_math/LICENSE and NOTICE.md for provenance.
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace PerfectPower.IntegralKernelWitness
open Matrix
open scoped BigOperators

def integralKernelMatrix {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R) : Matrix β β R :=
  (B * B.transpose).det • 1 - B.transpose * (B * B.transpose).adjugate * B

theorem mul_integralKernelMatrix {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R) :
    B * integralKernelMatrix B = 0 := by
  unfold integralKernelMatrix
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_adjugate,
    Matrix.smul_mul, Matrix.one_mul, sub_self]

theorem integralKernelMatrix_mulVec_of_kernel {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R)
    (x : β → R) (hx : B *ᵥ x = 0) :
    integralKernelMatrix B *ᵥ x = (B * B.transpose).det • x := by
  unfold integralKernelMatrix
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

theorem gram_det_ne_zero_of_linearIndependent {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (B : Matrix α β F) (hB : LinearIndependent F B) :
    (B * B.transpose).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hz : B.transpose *ᵥ x = 0 := by
    rw [← Matrix.mulVec_mulVec] at hker
    have hh := congrArg (fun y => dotProduct x y) hker
    dsimp only at hh
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_zero, dotProduct_self_eq_zero] at hh
    exact hh
  apply hx
  have hinj : Function.Injective (fun x => x ᵥ* B) :=
    Matrix.vecMul_injective_iff.mpr hB
  apply hinj
  simpa only [Matrix.mulVec_transpose, Matrix.zero_vecMul] using hz

theorem mulVec_eq_zero_of_row_mem_span {α β γ F : Type*}
    [Fintype β] [CommSemiring F] [Fintype γ]
    (A : Matrix α β F) (B : Matrix γ β F)
    (hspan : ∀ i, A i ∈ Submodule.span F (Set.range B))
    (x : β → F) (hx : B *ᵥ x = 0) : A *ᵥ x = 0 := by
  ext i
  change dotProduct (A i) x = 0
  refine Submodule.span_induction (p := fun y _ => dotProduct y x = 0)
    ?_ ?_ ?_ ?_ (hspan i)
  · rintro y ⟨j, rfl⟩
    exact congrFun hx j
  · exact zero_dotProduct x
  · intro y z _ _ hy hz
    rw [add_dotProduct, hy, hz, add_zero]
  · intro a y _ hy
    rw [smul_dotProduct, hy, smul_zero]

theorem integralKernelMatrix_column_mem_kernel {α β γ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [CommRing R]
    (A : Matrix γ β R) (B : Matrix α β R)
    (hspan : ∀ i, A i ∈ Submodule.span R (Set.range B)) (j : β) :
    A *ᵥ (fun i => integralKernelMatrix B i j) = 0 := by
  apply mulVec_eq_zero_of_row_mem_span A B hspan
  have hh := mul_integralKernelMatrix B
  ext i
  exact congrArg (fun M => M i j) hh

theorem mem_span_integralKernelMatrix_columns {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Field F]
    (B : Matrix α β F) (hdet : (B * B.transpose).det ≠ 0)
    (x : β → F) (hx : B *ᵥ x = 0) :
    x ∈ Submodule.span F (Set.range (fun j => fun i => integralKernelMatrix B i j)) := by
  have heq := integralKernelMatrix_mulVec_of_kernel B x hx
  have hmem : integralKernelMatrix B *ᵥ x ∈
      Submodule.span F (Set.range (fun j => fun i => integralKernelMatrix B i j)) := by
    rw [Matrix.mulVec_eq_sum]
    apply Submodule.sum_mem
    intro j _
    change (fun i => integralKernelMatrix B i j * x j) ∈ _
    have hh := Submodule.smul_mem
      (Submodule.span F (Set.range (fun j => fun i => integralKernelMatrix B i j)))
      (x j) (Submodule.subset_span (Set.mem_range_self j))
    convert hh using 1
    ext i
    exact mul_comm _ _
  rw [heq] at hmem
  exact (Submodule.smul_mem_iff _ hdet).mp hmem


theorem integralKernelMatrix_map {α β R S : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [CommRing R] [CommRing S] (f : R →+* S) (B : Matrix α β R) :
    (integralKernelMatrix B).map f = integralKernelMatrix (B.map f) := by
  have hadj := f.map_adjugate (B * B.transpose)
  have hdet := f.map_det (B * B.transpose)
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at hadj hdet
  unfold integralKernelMatrix
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.smul_apply,
    smul_eq_mul, map_mul]
  rw [hdet]
  have hone : f ((1 : Matrix β β R) i j) = (1 : Matrix β β S) i j := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [hone]
  change _ - ((B.transpose * (B * B.transpose).adjugate * B).map f) i j = _
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hadj]

end PerfectPower.IntegralKernelWitness
