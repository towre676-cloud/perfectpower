import PerfectPower.PlanarCertificates
namespace PerfectPower.PlanarGeometry
open PlanarCertificates
abbrev QPoint := ℚ × ℚ

def sidePlane (a b : QPoint) : Plane :=
  (-(b.2-a.2),b.1-a.1,(b.2-a.2)*a.1-(b.1-a.1)*a.2)
def xPlane (x : ℚ) : Plane := (1,0,-x)
def yPlane (y : ℚ) : Plane := (0,1,-y)
def ge (a : Plane) : Formula := .neg (.lt a)
def disj (f g : Formula) : Formula := .neg (.conj (.neg f) (.neg g))
def all (fs : List Formula) : Formula := fs.foldr Formula.conj (.truth true)
def any (fs : List Formula) : Formula := fs.foldr disj (.truth false)
def same (f g : Formula) : Formula := .neg (disj (.conj f (.neg g)) (.conj (.neg f) g))
def edges (vertices : List QPoint) := vertices.zip (vertices.drop 1 ++ vertices.take 1)
def boundaryFormula (a b : QPoint) : Formula := all
  [.eq (sidePlane a b),ge (xPlane (min a.1 b.1)),ge (negate (xPlane (max a.1 b.1))),
    ge (yPlane (min a.2 b.2)),ge (negate (yPlane (max a.2 b.2)))]
def ray (a b : QPoint) : Int × Plane × Plane × Plane :=
  if a.2 < b.2 then (1,yPlane a.2,yPlane b.2,negate (sidePlane a b))
  else if b.2 < a.2 then (-1,yPlane b.2,yPlane a.2,sidePlane a b)
  else (0,(0,0,0),(0,0,0),(0,0,0))
def polygonBoundaryFormula (vs : List QPoint) := any ((edges vs).map (fun e => boundaryFormula e.1 e.2))
def windingFormula (vs : List QPoint) : Formula := .winding ((edges vs).map (fun e => ray e.1 e.2))
def filledFormula (vs : List QPoint) := disj (polygonBoundaryFormula vs) (windingFormula vs)
def interiorFormula (vs : List QPoint) : Formula := .conj (.neg (polygonBoundaryFormula vs)) (windingFormula vs)
def triangleFormula (t : QPoint × QPoint × QPoint) := all
  [ge (sidePlane t.1 t.2.1),ge (sidePlane t.2.1 t.2.2),ge (sidePlane t.2.2 t.1)]
def coverageFormula (vs : List QPoint) (mesh : List (QPoint × QPoint × QPoint)) :=
  same (filledFormula vs) (any (mesh.map triangleFormula))

noncomputable def side (a b : QPoint) (p : Point) : ℝ :=
  ((b.1 : ℝ)-(a.1 : ℝ))*(p.2-(a.2 : ℝ))-((b.2 : ℝ)-(a.2 : ℝ))*(p.1-(a.1 : ℝ))
noncomputable def OnSegment (a b : QPoint) (p : Point) : Prop :=
  side a b p = 0 ∧ ((min a.1 b.1 : ℚ) : ℝ) ≤ p.1 ∧ p.1 ≤ ((max a.1 b.1 : ℚ) : ℝ) ∧
    ((min a.2 b.2 : ℚ) : ℝ) ≤ p.2 ∧ p.2 ≤ ((max a.2 b.2 : ℚ) : ℝ)
noncomputable def Boundary (vs : List QPoint) (p : Point) := ∃ e ∈ edges vs, OnSegment e.1 e.2 p
noncomputable def rayCount (a b : QPoint) (p : Point) : Int :=
  if a.2 < b.2 then
    if (a.2 : ℝ) ≤ p.2 ∧ p.2 < (b.2 : ℝ) ∧ 0 < side a b p then 1 else 0
  else if b.2 < a.2 then
    if (b.2 : ℝ) ≤ p.2 ∧ p.2 < (a.2 : ℝ) ∧ side a b p < 0 then -1 else 0
  else 0
noncomputable def Winding (vs : List QPoint) (p : Point) := ((edges vs).map (fun e => rayCount e.1 e.2 p)).sum
noncomputable def Filled (vs : List QPoint) (p : Point) := Boundary vs p ∨ Winding vs p ≠ 0
noncomputable def Interior (vs : List QPoint) (p : Point) := ¬Boundary vs p ∧ Winding vs p ≠ 0
noncomputable def TriangleContains (t : QPoint × QPoint × QPoint) (p : Point) :=
  0 ≤ side t.1 t.2.1 p ∧ 0 ≤ side t.2.1 t.2.2 p ∧ 0 ≤ side t.2.2 t.1 p
noncomputable def MeshCovered (mesh : List (QPoint × QPoint × QPoint)) (p : Point) := ∃ t ∈ mesh, TriangleContains t p

theorem sign_lt (a : Plane) (p : Point) : sign a p = -1 ↔ value a p < 0 := by
  unfold sign
  split_ifs <;> simp_all
theorem sign_eq (a : Plane) (p : Point) : sign a p = 0 ↔ value a p = 0 := by
  unfold sign
  split_ifs <;> simp_all <;> linarith
theorem eval_lt (a : Plane) (p : Point) : (.lt a : Formula).eval (fun a => sign a p) = true ↔ value a p < 0 := by
  simp [Formula.eval,sign_lt]
theorem eval_eq (a : Plane) (p : Point) : (.eq a : Formula).eval (fun a => sign a p) = true ↔ value a p = 0 := by
  simp [Formula.eval,sign_eq]
theorem eval_neg (f : Formula) (s : Plane → Int) : (Formula.neg f).eval s = true ↔ ¬f.eval s = true := by
  cases h : f.eval s <;> simp [Formula.eval,h]
theorem eval_conj (f g : Formula) (s : Plane → Int) : (Formula.conj f g).eval s = true ↔ f.eval s = true ∧ g.eval s = true := by
  simp [Formula.eval]
theorem eval_disj (f g : Formula) (s : Plane → Int) : (disj f g).eval s = true ↔ f.eval s = true ∨ g.eval s = true := by
  cases hf : f.eval s <;> cases hg : g.eval s <;> simp [disj,Formula.eval,hf,hg]
theorem eval_all (fs : List Formula) (s : Plane → Int) : (all fs).eval s = true ↔ ∀ f ∈ fs, f.eval s = true := by
  induction fs with
  | nil => simp [all,Formula.eval]
  | cons f fs ih =>
    change (Formula.conj f (all fs)).eval s = true ↔ _
    rw [eval_conj,ih]; simp
theorem eval_any (fs : List Formula) (s : Plane → Int) : (any fs).eval s = true ↔ ∃ f ∈ fs, f.eval s = true := by
  induction fs with
  | nil => simp [any,Formula.eval]
  | cons f fs ih =>
    change (disj f (any fs)).eval s = true ↔ _
    rw [eval_disj,ih]; simp
theorem eval_same (f g : Formula) (s : Plane → Int) : (same f g).eval s = true ↔ (f.eval s = true ↔ g.eval s = true) := by
  cases hf : f.eval s <;> cases hg : g.eval s <;> simp [same,disj,Formula.eval,hf,hg]
theorem side_value (a b : QPoint) (p : Point) : value (sidePlane a b) p = side a b p := by
  simp [sidePlane,value,side]; ring
theorem x_value (x : ℚ) (p : Point) : value (xPlane x) p = p.1-(x : ℝ) := by simp [xPlane,value]; ring
theorem y_value (y : ℚ) (p : Point) : value (yPlane y) p = p.2-(y : ℝ) := by simp [yPlane,value]; ring
theorem eval_ge (a : Plane) (p : Point) : (ge a).eval (fun a => sign a p) = true ↔ 0 ≤ value a p := by
  simp [ge,eval_neg,eval_lt,not_lt]
theorem boundary_spec (a b : QPoint) (p : Point) : (boundaryFormula a b).eval (fun a => sign a p) = true ↔ OnSegment a b p := by
  simp only [boundaryFormula,eval_all,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,eval_eq,eval_ge,side_value,x_value,y_value,negate_value,OnSegment]
  constructor <;> rintro ⟨h1,h2,h3,h4,h5⟩ <;> exact ⟨h1,by linarith,by linarith,by linarith,by linarith⟩
theorem exists_map {α β : Type*} (xs : List α) (f : α → β) (P : β → Prop) :
    (∃ y ∈ xs.map f, P y) ↔ ∃ x ∈ xs, P (f x) := by
  constructor
  · rintro ⟨y,hy,hp⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact ⟨x,hx,hp⟩
  · rintro ⟨x,hx,hp⟩
    exact ⟨f x,List.mem_map.mpr ⟨x,hx,rfl⟩,hp⟩
theorem boundary_polygon_spec (vs : List QPoint) (p : Point) : (polygonBoundaryFormula vs).eval (fun a => sign a p) = true ↔ Boundary vs p := by
  simp only [polygonBoundaryFormula,eval_any,Boundary,exists_map,boundary_spec]
theorem ray_spec (a b : QPoint) (p : Point) :
    (if sign (ray a b).2.1 p ≠ -1 ∧ sign (ray a b).2.2.1 p = -1 ∧ sign (ray a b).2.2.2 p = -1
      then (ray a b).1 else 0) = rayCount a b p := by
  simp only [ray,rayCount]
  split_ifs <;> simp_all [sign_lt,y_value,side_value,negate_value]
theorem winding_spec (vs : List QPoint) (p : Point) : (windingFormula vs).eval (fun a => sign a p) = true ↔ Winding vs p ≠ 0 := by
  simp only [windingFormula,Formula.eval,List.map_map,Function.comp_def,ray_spec,Winding,decide_eq_true_eq]
theorem filled_spec (vs : List QPoint) (p : Point) : (filledFormula vs).eval (fun a => sign a p) = true ↔ Filled vs p := by
  simp only [filledFormula,eval_disj,boundary_polygon_spec,winding_spec,Filled]
theorem interior_spec (vs : List QPoint) (p : Point) : (interiorFormula vs).eval (fun a => sign a p) = true ↔ Interior vs p := by
  simp only [interiorFormula,eval_conj,eval_neg,boundary_polygon_spec,winding_spec,Interior]
theorem triangle_spec (t : QPoint × QPoint × QPoint) (p : Point) : (triangleFormula t).eval (fun a => sign a p) = true ↔ TriangleContains t p := by
  simp [triangleFormula,eval_all,eval_ge,side_value,TriangleContains]
theorem coverage_spec (vs : List QPoint) (mesh : List (QPoint × QPoint × QPoint)) (p : Point) :
    (coverageFormula vs mesh).eval (fun a => sign a p) = true ↔ (Filled vs p ↔ MeshCovered mesh p) := by
  simp only [coverageFormula,eval_same,filled_spec,eval_any,exists_map,triangle_spec,MeshCovered]
theorem coverage_from_tree (vs : List QPoint) (mesh : List (QPoint × QPoint × QPoint)) (tree : Tree)
    (h : checked (coverageFormula vs mesh) [] tree) : ∀ p : Point, Filled vs p ↔ MeshCovered mesh p := by
  intro p
  exact (coverage_spec vs mesh p).mp (universal_identity _ tree h p)
#print axioms coverage_from_tree
end PerfectPower.PlanarGeometry
