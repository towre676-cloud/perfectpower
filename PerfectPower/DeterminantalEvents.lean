import Mathlib
noncomputable section
namespace PerfectPower.DeterminantalEvents
open Matrix
open scoped BigOperators
variable {e : Type*} [Fintype e] [DecidableEq e]
variable {R : Type*} [CommRing R]

/-- Identity rows pad the principal restriction to the full index set. -/
def padded (K : Matrix e e R) (S : Finset e) : Matrix e e R :=
  S.piecewise K (1 : Matrix e e R)

/-- A signed row expansion for an arbitrary set of forbidden indices. -/
theorem row_expansion (K : Matrix e e R) (I J : Finset e) :
    det (J.piecewise (padded K I - (1 : Matrix e e R)) (padded K I)) =
      ∑ S ∈ J.powerset, det (S.piecewise (-1 : Matrix e e R) (padded K I)) := by
  have h := (detRowAlternating.toMultilinearMap : MultilinearMap R (fun _ : e => e → R) R).map_piecewise_add
    (-1 : Matrix e e R) (padded K I) J
  calc
    _ = det (J.piecewise (-(1 : Matrix e e R) + padded K I) (padded K I)) := by
      congr 1
      ext i j
      simp [sub_eq_add_neg,add_comm]
    _ = _ := h

theorem signed_rows (K : Matrix e e R) (U S : Finset e) :
    det (S.piecewise (-1 : Matrix e e R) (padded K U)) =
      (-1 : R)^S.card * det (padded K (U \ S)) := by
  have he : S.piecewise (-1 : Matrix e e R) (padded K U) =
      Matrix.of (fun i j => (if i ∈ S then (-1 : R) else 1) * padded K (U \ S) i j) := by
    ext i j
    by_cases hs : i ∈ S <;> by_cases hu : i ∈ U <;>
      simp [padded,Finset.piecewise,hs,hu]
  rw [he,det_mul_column]
  congr 1
  simp

/-- Arbitrarily many inclusion/exclusion decisions, with no graph-size restriction. -/
theorem mixed_expansion (K : Matrix e e R) (I J : Finset e) :
    (-1 : R)^J.card * det (J.piecewise (padded K (I ∪ J) - (1 : Matrix e e R)) (padded K (I ∪ J))) =
      (-1 : R)^J.card * ∑ S ∈ J.powerset,
        (-1 : R)^S.card * det (padded K ((I ∪ J) \ S)) := by
  rw [row_expansion]
  simp_rw [signed_rows]

def mixed (K : Matrix e e R) (I J : Finset e) : R :=
  (-1 : R)^J.card * det (J.piecewise
    (padded K (I ∪ J) - (1 : Matrix e e R)) (padded K (I ∪ J)))

theorem diagonal_mixed (v : e → R) (I J : Finset e) (hIJ : Disjoint I J) :
    mixed (diagonal v) I J = (∏ i ∈ I, v i) * ∏ j ∈ J, (1-v j) := by
  have he : J.piecewise (padded (diagonal v) (I ∪ J) - (1 : Matrix e e R))
      (padded (diagonal v) (I ∪ J)) = diagonal (fun i =>
        (if i ∈ I then v i else 1) * (if i ∈ J then v i-1 else 1)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      by_cases hi : i ∈ I <;> by_cases hj : i ∈ J
      · exact False.elim ((Finset.disjoint_left.mp hIJ) hi hj)
      all_goals simp [padded,Finset.piecewise,hi,hj]
    · by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;>
        simp [padded,Finset.piecewise,hi,hj,diagonal_apply,hij]
  unfold mixed
  rw [he,det_diagonal,Finset.prod_mul_distrib]
  simp only [Fintype.prod_ite_mem]
  have hn : (∏ j ∈ J, (v j-1)) = (-1 : R)^J.card * ∏ j ∈ J, (1-v j) := by
    simp_rw [show ∀ j, v j-1= -(1-v j) from fun j => by ring]
    rw [Finset.prod_neg]
  rw [hn]
  have hs : (-1 : R)^J.card * (-1 : R)^J.card=1 := by
    rw [← mul_pow];simp
  calc _ = ((-1 : R)^J.card * (-1 : R)^J.card) *
      ((∏ i ∈ I,v i) * ∏ j ∈ J,(1-v j)) := by ring
       _ = _ := by rw [hs,one_mul]

/-- Any finite weighted law with determinant inclusion moments has the mixed determinant law. -/
theorem expectation_mixed {Ω : Type*} [Fintype Ω]
    (w : Ω → R) (v : Ω → e → R) (K : Matrix e e R)
    (hlaw : ∀ S, det (padded K S) = ∑ o, w o * det (padded (diagonal (v o)) S))
    (I J : Finset e) (hIJ : Disjoint I J) :
    mixed K I J = ∑ o, w o * ((∏ i ∈ I,v o i) * ∏ j ∈ J,(1-v o j)) := by
  unfold mixed
  rw [mixed_expansion]
  simp_rw [hlaw]
  calc
    _ = ∑ o, w o * ((-1 : R)^J.card * ∑ S ∈ J.powerset,
        (-1 : R)^S.card * det (padded (diagonal (v o)) ((I ∪ J) \ S))) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro o ho
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro o ho
      rw [← mixed_expansion]
      exact congrArg (w o * ·) (diagonal_mixed (v o) I J hIJ)

end PerfectPower.DeterminantalEvents
