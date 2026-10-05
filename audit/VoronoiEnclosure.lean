import PerfectPower.VoronoiEnclosure
open PerfectPower.VoronoiEnclosure
#print axioms chain_nonnegative
#print axioms chain_bound
#print axioms global_field_bound
#print axioms edge_gluing
#print axioms field_distance_lower
#print axioms boundary_coverage
#print axioms radius_transfer
#print axioms transferred_winner
#print axioms midpoint_affine
#print axioms quarter_area
#print axioms winner_unique
#print axioms midpoint_cover
#print axioms convex_radius
#print axioms tree_coverage

namespace PerfectPower.VoronoiEnclosure.Examples

theorem real_global (x y : ℝ) : |x-y| ≤ dist x y := by
  apply global_field_bound (fun a : ℝ => a)
  intro a b ε hε
  refine ⟨dist a b,?_,by linarith⟩
  have hlocal : |a-b| ≤ dist a b := by simp [Real.dist_eq]
  have hc := FieldChain.cons (f := fun a : ℝ => a) (dist_nonneg (x:=a) (y:=b))
    hlocal (FieldChain.nil b)
  simpa using hc

theorem midpoint_third : ∃ (i : Fin 4) (u v w : ℝ),
    0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u+v+w=1 ∧
      quarterMap i u v w=((1/3:ℝ),1/3,1/3) := by
  apply midpoint_cover <;> norm_num

theorem identity_transfer : dist (1/4:ℝ) 0 < dist (1/4:ℝ) 6 := by
  apply transferred_winner (φ := fun x : ℝ => x) 1 1 0 6 (1/2) (by norm_num) (by norm_num)
    (by intro x y; simp) (by intro x y; simp) (0:ℝ) (1/4) 0 6
  · norm_num [Real.dist_eq]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
    norm_num
  · norm_num [Real.dist_eq]
  · norm_num [Real.dist_eq]
  · norm_num

#print axioms real_global
#print axioms midpoint_third
#print axioms identity_transfer
end PerfectPower.VoronoiEnclosure.Examples
