import PerfectPower.PlanarGeometry
import PerfectPower.GeometrySourceTransport
namespace PerfectPower.RealVisibility
open PlanarCertificates PlanarGeometry

def mapPlanes (f : Formula) (h : Plane → Plane) : Formula := match f with
  | .lt a => .lt (h a)
  | .eq a => .eq (h a)
  | .truth b => .truth b
  | .winding rays => .winding (rays.map (fun r => (r.1,h r.2.1,h r.2.2.1,h r.2.2.2)))
  | .neg f => .neg (mapPlanes f h)
  | .conj f g => .conj (mapPlanes f h) (mapPlanes g h)

theorem eval_map (f : Formula) (h : Plane → Plane) (s : Plane → Int) :
    (mapPlanes f h).eval s = f.eval (fun a => s (h a)) := by
  induction f <;> simp [mapPlanes,Formula.eval,List.map_map,Function.comp_def, *]

def along (a b : QPoint) (f : Plane) : Plane :=
  (f.1*(b.1-a.1)+f.2.1*(b.2-a.2),0,f.1*a.1+f.2.1*a.2+f.2.2)
noncomputable def interpolate (a b : QPoint) (t : ℝ) : Point :=
  ((a.1 : ℝ)+t*((b.1 : ℝ)-(a.1 : ℝ)),(a.2 : ℝ)+t*((b.2 : ℝ)-(a.2 : ℝ)))

theorem along_value (a b : QPoint) (f : Plane) (p : Point) :
    value (along a b f) p = value f (interpolate a b p.1) := by
  simp [value,along,interpolate]; ring

theorem along_sign (a b : QPoint) (f : Plane) (p : Point) :
    sign (along a b f) p = sign f (interpolate a b p.1) := by
  unfold sign; rw [along_value]

def forbidden (polygons : List (List QPoint)) := any (polygons.map interiorFormula)
def segmentFormula (polygons : List (List QPoint)) (a b : QPoint) :=
  disj (.lt (1,0,0)) (disj (.lt (-1,0,1)) (.neg (mapPlanes (forbidden polygons) (along a b))))
noncomputable def FreeSegment (polygons : List (List QPoint)) (a b : QPoint) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ polygon ∈ polygons, ¬Interior polygon (interpolate a b t)

theorem segment_from_tree (polygons : List (List QPoint)) (a b : QPoint) (tree : Tree)
    (h : checked (segmentFormula polygons a b) [] tree) : FreeSegment polygons a b := by
  intro t htlo hthi polygon hpoly
  have hp := universal_identity _ tree h (t,0)
  simp only [segmentFormula,eval_disj,eval_lt,value] at hp
  have hneg : ¬t < 0 := by linarith
  have hpos : ¬-(t : ℝ)+1 < 0 := by linarith
  simp only [Rat.cast_one,Rat.cast_zero,Rat.cast_neg,one_mul,neg_one_mul,zero_mul,add_zero,zero_add,hneg,hpos,false_or] at hp
  rw [eval_neg,eval_map] at hp
  simp only [along_sign] at hp
  intro hi
  apply hp
  rw [forbidden,eval_any,exists_map]
  exact ⟨polygon,hpoly,(interior_spec polygon _).mpr hi⟩

noncomputable def blockedFormula (polygons : List (List QPoint)) (a b : QPoint) (t : ℚ) :=
  (forbidden polygons).eval (fun f =>
    let v := f.1*(a.1+t*(b.1-a.1))+f.2.1*(a.2+t*(b.2-a.2))+f.2.2
    if v < 0 then -1 else if v = 0 then 0 else 1)

theorem rational_sign (f : Plane) (p : QPoint) : sign f ((p.1 : ℝ),(p.2 : ℝ)) =
    (let v := f.1*p.1+f.2.1*p.2+f.2.2; if v < 0 then (-1 : Int) else if v = 0 then 0 else 1) := by
  have hv : value f ((p.1 : ℝ),(p.2 : ℝ)) = ((f.1*p.1+f.2.1*p.2+f.2.2 : ℚ) : ℝ) := by simp [value]
  unfold sign
  rw [hv]
  norm_cast

theorem blocked_segment (polygons : List (List QPoint)) (a b : QPoint) (t : ℚ)
    (hlo : 0 ≤ t) (hhi : t ≤ 1) (h : blockedFormula polygons a b t = true) : ¬FreeSegment polygons a b := by
  intro hf
  have hi : (forbidden polygons).eval (fun f => sign f (interpolate a b (t : ℝ))) = true := by
    have he : interpolate a b (t : ℝ) =
        (((a.1+t*(b.1-a.1) : ℚ) : ℝ),((a.2+t*(b.2-a.2) : ℚ) : ℝ)) := by simp [interpolate]
    rw [he]
    have hs : (fun f => sign f (((a.1+t*(b.1-a.1) : ℚ) : ℝ),((a.2+t*(b.2-a.2) : ℚ) : ℝ))) =
        (fun f : Plane => let v := f.1*(a.1+t*(b.1-a.1))+f.2.1*(a.2+t*(b.2-a.2))+f.2.2
          if v < 0 then (-1 : Int) else if v = 0 then 0 else 1) := by
      funext f; exact rational_sign f (a.1+t*(b.1-a.1),a.2+t*(b.2-a.2))
    rw [hs]
    exact h
  rw [forbidden,eval_any,exists_map] at hi
  obtain ⟨polygon,hpoly,hi⟩ := hi
  exact hf (t : ℝ) (by exact_mod_cast hlo) (by exact_mod_cast hhi) polygon hpoly ((interior_spec polygon _).mp hi)

open GeometryCertificates
inductive VisibilityWalk (polygons : List (List QPoint)) (nodes : List GeometryCertificates.Point) : Nat → Nat → Int → Prop where
  | nil (u : Nat) : VisibilityWalk polygons nodes u u 0
  | cons {u v t : Nat} {c : Int} (hu : u < nodes.length) (hv : v < nodes.length)
      (hne : u ≠ v) (free : FreeSegment polygons (GeometryAdmission.qpoint (GeometryAdmission.vertex nodes u))
        (GeometryAdmission.qpoint (GeometryAdmission.vertex nodes v)))
      (tail : VisibilityWalk polygons nodes v t c) : VisibilityWalk polygons nodes u t
        (GeometryAdmission.weight (GeometryAdmission.vertex nodes u) (GeometryAdmission.vertex nodes v)+c)

theorem real_walk_to_graph (polygons : List (List QPoint)) (nodes : List GeometryCertificates.Point)
    (admitted : List (Nat × Nat))
    (complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
      ((u,v) ∈ admitted ↔ FreeSegment polygons (GeometryAdmission.qpoint (GeometryAdmission.vertex nodes u))
        (GeometryAdmission.qpoint (GeometryAdmission.vertex nodes v))))
    {s t : Nat} {c : Int} (walk : VisibilityWalk polygons nodes s t c) :
    Walk (GeometryAdmission.graph nodes admitted) s t c := by
  induction walk with
  | nil u => exact Walk.nil u
  | cons hu hv hne free tail ih =>
    exact Walk.cons ((GeometryAdmission.mem_graph _ _ _ _ _).mpr
      ⟨hu,hv,hne,(complete _ _ hu hv hne).mpr free,rfl⟩) ih

theorem real_optimal_walk (polygons : List (List QPoint)) (nodes : List GeometryCertificates.Point)
    (admitted : List (Nat × Nat))
    (complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
      ((u,v) ∈ admitted ↔ FreeSegment polygons (GeometryAdmission.qpoint (GeometryAdmission.vertex nodes u))
        (GeometryAdmission.qpoint (GeometryAdmission.vertex nodes v))))
    (p : Nat → Int) (bounds : ∀ e ∈ GeometryAdmission.graph nodes admitted, p e.2.1 ≤ p e.1+e.2.2)
    {s t : Nat} {cost other : Int} (attained : cost = p t-p s)
    (walk : VisibilityWalk polygons nodes s t other) : cost ≤ other :=
  optimal_walk _ p bounds attained (real_walk_to_graph polygons nodes admitted complete walk)

/-- Finite walks with rational endpoint cost but real segment visibility.
Stationary steps and repeated vertices are included. -/
inductive SourceWalk (polygons : List (List QPoint)) (nodes : List QPoint) : Nat → Nat → ℚ → Prop where
  | nil (u : Nat) : SourceWalk polygons nodes u u 0
  | cons {u v t : Nat} {c : ℚ} (hu : u < nodes.length) (hv : v < nodes.length)
      (free : FreeSegment polygons (GeometryAdmission.rationalVertex nodes u) (GeometryAdmission.rationalVertex nodes v))
      (tail : SourceWalk polygons nodes v t c) : SourceWalk polygons nodes u t
        (GeometryAdmission.qweight (GeometryAdmission.rationalVertex nodes u) (GeometryAdmission.rationalVertex nodes v)+c)

theorem source_potential_bound (polygons : List (List QPoint)) (nodes : List QPoint) (p : Nat → ℚ)
    (bounds : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
      FreeSegment polygons (GeometryAdmission.rationalVertex nodes u) (GeometryAdmission.rationalVertex nodes v) →
      p v ≤ p u+GeometryAdmission.qweight (GeometryAdmission.rationalVertex nodes u) (GeometryAdmission.rationalVertex nodes v))
    {s t : Nat} {c : ℚ} (walk : SourceWalk polygons nodes s t c) : p t ≤ p s+c := by
  induction walk with
  | nil u => simp
  | @cons u v t c hu hv free tail ih =>
    by_cases he : u=v
    · subst v
      simpa [GeometryAdmission.qweight] using ih
    · have h := bounds u v hu hv he free
      linarith

theorem source_optimal_walk (polygons : List (List QPoint)) (nodes : List QPoint) (p : Nat → ℚ)
    (bounds : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
      FreeSegment polygons (GeometryAdmission.rationalVertex nodes u) (GeometryAdmission.rationalVertex nodes v) →
      p v ≤ p u+GeometryAdmission.qweight (GeometryAdmission.rationalVertex nodes u) (GeometryAdmission.rationalVertex nodes v))
    {s t : Nat} {best other : ℚ} (attained : best = p t-p s)
    (walk : SourceWalk polygons nodes s t other) : best ≤ other := by
  have h := source_potential_bound polygons nodes p bounds walk
  linarith

theorem source_closed_endpoint (polygons : List (List QPoint)) (nodes : List QPoint)
    (r : Nat → Prop)
    (closed : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
      FreeSegment polygons (GeometryAdmission.rationalVertex nodes u) (GeometryAdmission.rationalVertex nodes v) → r u → r v)
    {u v : Nat} {c : ℚ} (walk : SourceWalk polygons nodes u v c) (start : r u) : r v := by
  induction walk with
  | nil => exact start
  | @cons u v t c hu hv free tail ih =>
    by_cases he : u=v
    · subst v; exact ih start
    · exact ih (closed u v hu hv he free start)

theorem source_no_walk_outside (polygons : List (List QPoint)) (nodes : List QPoint)
    (r : Nat → Prop)
    (closed : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
      FreeSegment polygons (GeometryAdmission.rationalVertex nodes u) (GeometryAdmission.rationalVertex nodes v) → r u → r v)
    {s t : Nat} (hs : r s) (ht : ¬r t) : ∀ c, ¬SourceWalk polygons nodes s t c := by
  intro c walk
  exact ht (source_closed_endpoint polygons nodes r closed walk hs)

#print axioms source_no_walk_outside
#print axioms segment_from_tree
#print axioms blocked_segment
#print axioms real_optimal_walk
#print axioms source_optimal_walk
end PerfectPower.RealVisibility
