import PerfectPower.GeometryAdmission
namespace PerfectPower.GeometryAdmission
instance (p a b : QPoint) : Decidable (OnSegment p a b) := by unfold OnSegment; infer_instance

def boundaryFormula (polygon : List QPoint) (a b : QPoint) : Formula :=
  any ((polygonEdges polygon).map (fun e => boundaryEdge e.1 e.2 a b))

theorem boundary_formula_spec (polygon : List QPoint) (a b : QPoint) (t : ℚ) :
    (boundaryFormula polygon a b).eval t = true ↔ polygonBoundary polygon (interpolate a b t) := by
  rw [boundaryFormula,any_eval]
  constructor
  · rintro ⟨f,hf,htrue⟩
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hf
    exact ⟨e,he,(boundary_edge_eval _ _ _ _ _).mp htrue⟩
  · rintro ⟨e,he,hedge⟩
    exact ⟨boundaryEdge e.1 e.2 a b,List.mem_map.mpr ⟨e,he,rfl⟩,
      (boundary_edge_eval _ _ _ _ _).mpr hedge⟩

theorem no_segment_contact (a b c d : QPoint) (cells : List (ℚ × ℚ))
    (h : accepted (boundaryEdge c d a b) cells) : ¬SegmentContact a b c d := by
  rintro ⟨p,hab,hcd⟩
  obtain ⟨t,hlo,hhi,hp⟩ := on_segment_parameter p a b hab
  have hf := accepted_sound _ _ h t hlo hhi
  have ht := (boundary_edge_eval c d a b t).mpr (by rw [← hp]; exact hcd)
  rw [ht] at hf
  contradiction

theorem no_boundary_contact (polygon : List QPoint) (a b : QPoint) (cells : List (ℚ × ℚ))
    (h : accepted (boundaryFormula polygon a b) cells) : ¬BoundaryContact polygon a b := by
  rintro ⟨e,he,p,hab,hcd⟩
  obtain ⟨t,hlo,hhi,hp⟩ := on_segment_parameter p a b hab
  have hf := accepted_sound _ _ h t hlo hhi
  have ht := (boundary_formula_spec polygon a b t).mpr ⟨e,he,by rw [← hp]; exact hcd⟩
  rw [ht] at hf
  contradiction

#print axioms no_segment_contact
#print axioms no_boundary_contact
end PerfectPower.GeometryAdmission
