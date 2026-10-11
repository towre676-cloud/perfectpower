import PerfectPower.GeometryAdmission
namespace PerfectPower.GeometryAdmission

def scalePoint (d : ℚ) (p : QPoint) : QPoint := (d*p.1,d*p.2)

theorem side_scale (d : ℚ) (a b p : QPoint) :
    qside (scalePoint d a) (scalePoint d b) (scalePoint d p) = (d*d)*qside a b p := by
  unfold qside scalePoint; ring

theorem interpolate_scale (d : ℚ) (a b : QPoint) (t : ℚ) :
    interpolate (scalePoint d a) (scalePoint d b) t = scalePoint d (interpolate a b t) := by
  ext <;> simp only [interpolate,scalePoint,Prod.fst,Prod.snd] <;> ring

theorem on_segment_scale (d : ℚ) (hd : 0 < d) (p a b : QPoint) :
    OnSegment (scalePoint d p) (scalePoint d a) (scalePoint d b) ↔ OnSegment p a b := by
  have hsq : 0 < d*d := mul_pos hd hd
  have hminx : min (d*a.1) (d*b.1) = d*min a.1 b.1 := (mul_min_of_nonneg _ _ (le_of_lt hd)).symm
  have hmaxx : max (d*a.1) (d*b.1) = d*max a.1 b.1 := (mul_max_of_nonneg _ _ (le_of_lt hd)).symm
  have hminy : min (d*a.2) (d*b.2) = d*min a.2 b.2 := (mul_min_of_nonneg _ _ (le_of_lt hd)).symm
  have hmaxy : max (d*a.2) (d*b.2) = d*max a.2 b.2 := (mul_max_of_nonneg _ _ (le_of_lt hd)).symm
  simp only [OnSegment]
  rw [side_scale]
  simp only [scalePoint,Prod.fst,Prod.snd,hminx,hmaxx,hminy,hmaxy,
    mul_eq_zero,ne_of_gt hsq,false_or,mul_le_mul_left hd]

theorem ray_count_scale (d : ℚ) (hd : 0 < d) (a b p : QPoint) :
    rayCount (scalePoint d a) (scalePoint d b) (scalePoint d p) = rayCount a b p := by
  have hsq : 0 < d*d := mul_pos hd hd
  have hn (x : ℚ) : (d*d)*x < 0 ↔ x < 0 := by
    simpa only [not_le] using not_congr (mul_nonneg_iff_of_pos_left hsq (b := x))
  simp only [rayCount,side_scale]
  simp only [scalePoint,Prod.fst,Prod.snd,mul_le_mul_left hd,mul_lt_mul_left hd,
    mul_pos_iff_of_pos_left hsq,hn]

theorem polygon_edges_scale (d : ℚ) (polygon : List QPoint) :
    polygonEdges (polygon.map (scalePoint d)) =
      (polygonEdges polygon).map (fun e => (scalePoint d e.1,scalePoint d e.2)) := by
  simp only [polygonEdges,← List.map_drop,← List.map_take,← List.map_append,List.zip_map,Prod.map]
  exact List.map_congr_left (fun e _ => by cases e; rfl)

theorem polygon_interior_scale (d : ℚ) (hd : 0 < d) (polygon : List QPoint) (p : QPoint) :
    polygonInterior (polygon.map (scalePoint d)) (scalePoint d p) ↔ polygonInterior polygon p := by
  have hb : polygonBoundary (polygon.map (scalePoint d)) (scalePoint d p) ↔ polygonBoundary polygon p := by
    simp only [polygonBoundary,polygon_edges_scale]
    constructor
    · rintro ⟨se,hse,hseg⟩
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hse
      exact ⟨e,he,(on_segment_scale d hd p e.1 e.2).mp hseg⟩
    · rintro ⟨e,he,hseg⟩
      exact ⟨(scalePoint d e.1,scalePoint d e.2),List.mem_map.mpr ⟨e,he,rfl⟩,
        (on_segment_scale d hd p e.1 e.2).mpr hseg⟩
  simp only [polygonInterior,hb,windingAt,polygon_edges_scale,List.map_map,Function.comp_def,
    ray_count_scale d hd]

theorem free_segment_scale (d : ℚ) (hd : 0 < d) (polygons : List (List QPoint)) (a b : QPoint) :
    FreeSegment (polygons.map (List.map (scalePoint d))) (scalePoint d a) (scalePoint d b) ↔
      FreeSegment polygons a b := by
  simp [free_segment_spec,interpolate_scale,polygon_interior_scale d hd]

def qweight (a b : QPoint) : ℚ := |b.1-a.1|+|b.2-a.2|

theorem qweight_scale (d : ℚ) (hd : 0 < d) (a b : QPoint) :
    qweight (scalePoint d a) (scalePoint d b) = d*qweight a b := by
  simp [qweight,scalePoint,← mul_sub,abs_mul,abs_of_pos hd,mul_add]

theorem weight_coercion (a b : PerfectPower.GeometryCertificates.Point) :
    (weight a b : ℚ) = qweight (qpoint a) (qpoint b) := by
  simp [weight,qweight,qpoint]

def rationalVertex (nodes : List QPoint) (u : Nat) : QPoint := nodes[u]?.getD (0,0)
inductive RationalGeometricWalk (polygons : List (List QPoint)) (nodes : List QPoint) : Nat → Nat → ℚ → Prop where
  | nil (u : Nat) : RationalGeometricWalk polygons nodes u u 0
  | cons {u v t : Nat} {c : ℚ} (hu : u < nodes.length) (hv : v < nodes.length)
      (hne : u ≠ v) (free : FreeSegment polygons (rationalVertex nodes u) (rationalVertex nodes v))
      (tail : RationalGeometricWalk polygons nodes v t c) :
      RationalGeometricWalk polygons nodes u t (qweight (rationalVertex nodes u) (rationalVertex nodes v)+c)

theorem rational_walk_scaled (d : ℚ) (hd : 0 < d) (polygons : List (List QPoint))
    (original : List QPoint) (nodes : List PerfectPower.GeometryCertificates.Point)
    (hlen : nodes.length = original.length)
    (binding : ∀ u, u < original.length → qpoint (vertex nodes u) = scalePoint d (rationalVertex original u))
    {s t : Nat} {cost : ℚ} (walk : RationalGeometricWalk polygons original s t cost) :
    ∃ scaled : Int,
      GeometricWalk (polygons.map (List.map (scalePoint d))) nodes s t scaled ∧ (scaled : ℚ) = d*cost := by
  induction walk with
  | nil u => exact ⟨0,GeometricWalk.nil u,by simp⟩
  | @cons u v t c hu hv hne free tail ih =>
    obtain ⟨scaled,hwalk,hcost⟩ := ih
    refine ⟨weight (vertex nodes u) (vertex nodes v)+scaled,?_,?_⟩
    · apply GeometricWalk.cons (by simpa [hlen] using hu) (by simpa [hlen] using hv) hne
      · rw [binding u hu,binding v hv]
        exact (free_segment_scale d hd polygons _ _).mpr free
      · exact hwalk
    · rw [Int.cast_add,weight_coercion,binding u hu,binding v hv,qweight_scale d hd,hcost]
      ring

theorem rational_optimal_walk (d : ℚ) (hd : 0 < d) (polygons : List (List QPoint))
    (original : List QPoint) (nodes : List PerfectPower.GeometryCertificates.Point)
    (hlen : nodes.length = original.length)
    (binding : ∀ u, u < original.length → qpoint (vertex nodes u) = scalePoint d (rationalVertex original u))
    {s t : Nat} {best : Int} {originalBest other : ℚ}
    (bestBinding : (best : ℚ) = d*originalBest)
    (bound : ∀ {c : Int}, GeometricWalk (polygons.map (List.map (scalePoint d))) nodes s t c → best ≤ c)
    (walk : RationalGeometricWalk polygons original s t other) : originalBest ≤ other := by
  obtain ⟨scaled,hwalk,hcost⟩ := rational_walk_scaled d hd polygons original nodes hlen binding walk
  have hb : (best : ℚ) ≤ (scaled : ℚ) := by exact_mod_cast bound hwalk
  rw [bestBinding,hcost] at hb
  exact (mul_le_mul_left hd).mp hb

#print axioms rational_optimal_walk

#print axioms free_segment_scale
end PerfectPower.GeometryAdmission
