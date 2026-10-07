import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic.Ring

noncomputable section
namespace PerfectPower.SeparatedDimension
open scoped BigOperators
variable {K I J L : Type*} [Field K] [Fintype I] [Fintype J] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq L]

/-- A rectangular tensor lies in U in each column and in V in each row. -/
def separated (U : Submodule K (I → K)) (V : Submodule K (J → K)) :
    Submodule K (Matrix I J K) where
  carrier := {M | (∀ j, (fun i => M i j) ∈ U) ∧ (∀ i, M i ∈ V)}
  zero_mem' := by exact ⟨fun _ => U.zero_mem, fun _ => V.zero_mem⟩
  add_mem' := by
    rintro M N ⟨hM,hM'⟩ ⟨hN,hN'⟩
    exact ⟨fun j => U.add_mem (hM j) (hN j),fun i => V.add_mem (hM' i) (hN' i)⟩
  smul_mem' := by
    rintro c M ⟨hM,hM'⟩
    exact ⟨fun j => U.smul_mem c (hM j),fun i => V.smul_mem c (hM' i)⟩

/-- Extend a coefficient functional and express it as a combination of rows. -/
theorem row_functional_mem (V : Submodule K (J → K)) (M : Matrix I J K)
    (hM : ∀ i, M i ∈ V) (f : (I → K) →ₗ[K] K) :
    (fun j => f (fun i => M i j)) ∈ V := by
  classical
  have he (j : J) : f (fun i => M i j) =
      ∑ i, (M i j)*f (Pi.single i 1) := by
    rw [← (Pi.basisFun K I).sum_repr (fun i => M i j),map_sum]
    simp
  have hf : (fun j => f (fun i => M i j)) =
      ∑ i, f (Pi.single i 1) • M i := by
    funext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [he]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hf]
  exact V.sum_mem fun i _ => V.smul_mem _ (hM i)

/-- A basis of U assembles independent V-valued coefficient rows. -/
def assemble (U : Submodule K (I → K)) (V : Submodule K (J → K))
    (b : Basis L K U) : (L → V) →ₗ[K] Matrix I J K where
  toFun c := fun i j => ∑ t, (b t : I → K) i * (c t : J → K) j
  map_add' := by
    intro c d
    ext i j
    simp [mul_add,Finset.sum_add_distrib]
  map_smul' := by
    intro r c
    ext i j
    simp [Finset.mul_sum,mul_left_comm,mul_assoc]

theorem assemble_column (U : Submodule K (I → K)) (V : Submodule K (J → K))
    (b : Basis L K U) (c : L → V) (j : J) :
    (fun i => assemble U V b c i j) =
      ((∑ t, (c t : J → K) j • b t : U) : I → K) := by
  ext i
  simp [assemble,mul_comm]

theorem assemble_mem (U : Submodule K (I → K)) (V : Submodule K (J → K))
    (b : Basis L K U) (c : L → V) : assemble U V b c ∈ separated U V := by
  constructor
  · intro j
    rw [assemble_column]
    exact Subtype.mem _
  · intro i
    have he : assemble U V b c i = ∑ t, (b t : I → K) i • (c t : J → K) := by
      ext j
      simp [assemble]
    rw [he]
    exact V.sum_mem fun t _ => V.smul_mem _ (Subtype.mem _)

theorem assemble_injective (U : Submodule K (I → K)) (V : Submodule K (J → K))
    (b : Basis L K U) : Function.Injective (assemble U V b) := by
  intro c d h
  funext t
  apply Subtype.ext
  funext j
  have he : (∑ s, (c s : J → K) j • b s : U) =
      ∑ s, (d s : J → K) j • b s := by
    apply Subtype.ext
    rw [← assemble_column,← assemble_column]
    exact congrArg (fun M : Matrix I J K => fun i => M i j) h
  have hc := congrArg (fun u : U => b.repr u t) he
  simpa only [b.repr_sum_self] using hc

theorem range_assemble (U : Submodule K (I → K)) (V : Submodule K (J → K))
    (b : Basis L K U) : LinearMap.range (assemble U V b) = separated U V := by
  classical
  apply le_antisymm
  · rintro M ⟨c,rfl⟩
    exact assemble_mem U V b c
  · rintro M ⟨hU,hV⟩
    obtain ⟨P,hP⟩ := LinearMap.exists_leftInverse_of_injective U.subtype
      (LinearMap.ker_eq_bot.mpr U.subtype_injective)
    have hP' (u : U) : P (u : I → K)=u := by
      exact congrArg (fun f : U →ₗ[K] U => f u) hP
    let column (j : J) : U := ⟨fun i => M i j,hU j⟩
    let f (t : L) : (I → K) →ₗ[K] K :=
      (Finsupp.lapply t).comp (b.repr.toLinearMap.comp P)
    let c (t : L) : V := ⟨fun j => f t (fun i => M i j),row_functional_mem V M hV (f t)⟩
    refine ⟨c,?_⟩
    ext i j
    change (∑ t, (b t : I → K) i * f t (fun k => M k j)) = M i j
    have hf (t : L) : f t (fun k => M k j)=b.repr (column j) t := by
      change b.repr (P (column j : I → K)) t = _
      rw [hP']
    have hs : (∑ t, (b t : I → K) i * f t (fun k => M k j)) =
        ∑ t, b.repr (column j) t * (b t : I → K) i := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hf]
      exact mul_comm _ _
    rw [hs]
    have he := congrArg (fun u : U => (u : I → K) i) (b.sum_repr (column j))
    simpa using he

/-- The separated tensor has the exact product dimension. -/
theorem finrank_separated (U : Submodule K (I → K)) (V : Submodule K (J → K)) :
    Module.finrank K (separated U V) = Module.finrank K U * Module.finrank K V := by
  classical
  let b := Module.finBasis K U
  have he := LinearEquiv.finrank_eq
    (LinearEquiv.ofInjective (assemble U V b) (assemble_injective U V b))
  rw [range_assemble] at he
  rw [← he,Module.finrank_pi_fintype]
  simp

end PerfectPower.SeparatedDimension
