import PerfectPower.GeometryCertificates
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/- Exact rational geometry, with no producer-selected visibility edges trusted.
Interior means the standard nonzero winding ray rule, excluding polygon boundary.
Certificates partition the whole rational segment parameter interval. -/
namespace PerfectPower.GeometryAdmission
abbrev QPoint := ℚ × ℚ
abbrev Affine := ℚ × ℚ
def value (f : Affine) (t : ℚ) : ℚ := f.1 * t + f.2
structure RayCross where
  weight : Int
  lower : Affine
  upper : Affine
  turn : Affine
  deriving DecidableEq, Repr

def RayCross.eval (r : RayCross) (t : ℚ) : Int :=
  if 0 ≤ value r.lower t ∧ value r.upper t < 0 ∧ value r.turn t < 0 then r.weight else 0

def RayCross.leaves (r : RayCross) : List Affine := [r.lower,r.upper,r.turn]

inductive Formula where
  | lt (f : Affine)
  | eq (f : Affine)
  | truth (b : Bool)
  | winding (rays : List RayCross)
  | neg (f : Formula)
  | conj (f g : Formula)
  | xor (f g : Formula)
  deriving DecidableEq, Repr

def Formula.eval : Formula → ℚ → Bool
  | .lt f, t => decide (value f t < 0)
  | .eq f, t => decide (value f t = 0)
  | .truth b, _ => b
  | .winding rays, t => decide ((rays.map (fun r => r.eval t)).sum ≠ 0)
  | .neg f, t => !(f.eval t)
  | .conj f g, t => f.eval t && g.eval t
  | .xor f g, t => f.eval t != g.eval t

def Formula.leaves : Formula → List Affine
  | .lt f | .eq f => [f]
  | .truth _ => []
  | .winding rays => rays.flatMap RayCross.leaves
  | .neg f => f.leaves
  | .conj f g | .xor f g => f.leaves ++ g.leaves

def stable (f : Affine) (lo hi : ℚ) : Prop :=
  (value f lo = 0 ∧ value f hi = 0) ∨
  (0 ≤ value f lo ∧ 0 ≤ value f hi ∧ (0 < value f lo ∨ 0 < value f hi)) ∨
  (value f lo ≤ 0 ∧ value f hi ≤ 0 ∧ (value f lo < 0 ∨ value f hi < 0))
instance (f : Affine) (lo hi : ℚ) : Decidable (stable f lo hi) := by
  unfold stable; infer_instance

theorem affine_interpolation (f : Affine) (lo hi t : ℚ) :
    (hi-lo)*value f t = (hi-t)*value f lo + (t-lo)*value f hi := by
  unfold value; ring

theorem stable_sign (f : Affine) (lo hi t : ℚ) (h : stable f lo hi)
    (ht : lo < t ∧ t < hi) :
    (value f t < 0 ↔ value f ((lo+hi)/2) < 0) ∧
    (value f t = 0 ↔ value f ((lo+hi)/2) = 0) := by
  have hmid : lo < (lo+hi)/2 ∧ (lo+hi)/2 < hi := by constructor <;> linarith [ht.1, ht.2]
  have classify : ∀ x : ℚ, lo < x ∧ x < hi →
      (value f lo = 0 ∧ value f hi = 0 → value f x = 0) ∧
      (0 ≤ value f lo ∧ 0 ≤ value f hi ∧ (0 < value f lo ∨ 0 < value f hi) → 0 < value f x) ∧
      (value f lo ≤ 0 ∧ value f hi ≤ 0 ∧ (value f lo < 0 ∨ value f hi < 0) → value f x < 0) := by
    intro x hx
    have id := affine_interpolation f lo hi x
    have width : 0 < hi-lo := by linarith [hx.1,hx.2]
    constructor
    · rintro ⟨ha,hb⟩; rw [ha,hb] at id; nlinarith
    constructor
    · rintro ⟨ha,hb,hpos⟩
      have pa : 0 ≤ (hi-x)*value f lo := mul_nonneg (by linarith [hx.2]) ha
      have pb : 0 ≤ (x-lo)*value f hi := mul_nonneg (by linarith [hx.1]) hb
      rcases hpos with hpos | hpos
      · have strict := mul_pos (show 0 < hi-x by linarith [hx.2]) hpos; nlinarith
      · have strict := mul_pos (show 0 < x-lo by linarith [hx.1]) hpos; nlinarith
    · rintro ⟨ha,hb,hneg⟩
      have pa : (hi-x)*value f lo ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.2]) ha
      have pb : (x-lo)*value f hi ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.1]) hb
      rcases hneg with hneg | hneg
      · have strict := mul_neg_of_pos_of_neg (show 0 < hi-x by linarith [hx.2]) hneg; nlinarith
      · have strict := mul_neg_of_pos_of_neg (show 0 < x-lo by linarith [hx.1]) hneg; nlinarith
  rcases h with h | h | h
  · have a := (classify t ht).1 h
    have b := (classify _ hmid).1 h
    simp [a,b]
  · have a := (classify t ht).2.1 h
    have b := (classify _ hmid).2.1 h
    constructor
    · exact iff_of_false (by linarith) (by linarith)
    · exact iff_of_false (ne_of_gt a) (ne_of_gt b)
  · have a := (classify t ht).2.2 h
    have b := (classify _ hmid).2.2 h
    constructor
    · exact iff_of_true a b
    · exact iff_of_false (ne_of_lt a) (ne_of_lt b)

theorem formula_constant (f : Formula) (lo hi t : ℚ)
    (h : ∀ line ∈ f.leaves, stable line lo hi) (ht : lo < t ∧ t < hi) :
    f.eval t = f.eval ((lo+hi)/2) := by
  induction f with
  | lt line => simp only [Formula.eval]; exact decide_eq_decide.mpr (stable_sign line lo hi t (h line (by simp [Formula.leaves])) ht).1
  | eq line => simp only [Formula.eval]; exact decide_eq_decide.mpr (stable_sign line lo hi t (h line (by simp [Formula.leaves])) ht).2
  | truth b => rfl
  | winding rays =>
    have hr : ∀ r ∈ rays, r.eval t = r.eval ((lo+hi)/2) := by
      intro r hr
      have hl : ∀ l ∈ r.leaves, stable l lo hi := by
        intro l hl
        exact h l (by simp only [Formula.leaves, List.mem_flatMap]; exact ⟨r,hr,hl⟩)
      have low := (stable_sign r.lower lo hi t (hl _ (by simp [RayCross.leaves])) ht).1
      have up := (stable_sign r.upper lo hi t (hl _ (by simp [RayCross.leaves])) ht).1
      have turn := (stable_sign r.turn lo hi t (hl _ (by simp [RayCross.leaves])) ht).1
      have low' : (0 ≤ value r.lower t) ↔ (0 ≤ value r.lower ((lo+hi)/2)) := by
        simpa only [not_lt] using not_congr low
      simp only [RayCross.eval, low',up,turn]
    have hm : rays.map (fun r => r.eval t) = rays.map (fun r => r.eval ((lo+hi)/2) ) :=
      List.map_congr_left hr
    simp only [Formula.eval, hm]
  | neg f ih => exact congrArg Bool.not (ih h)
  | conj f g ihf ihg =>
    have hf := ihf (fun l hl => h l (by simp [Formula.leaves, hl]))
    have hg := ihg (fun l hl => h l (by simp [Formula.leaves, hl]))
    simp only [Formula.eval, hf,hg]
  | xor f g ihf ihg =>
    have hf := ihf (fun l hl => h l (by simp [Formula.leaves, hl]))
    have hg := ihg (fun l hl => h l (by simp [Formula.leaves, hl]))
    simp only [Formula.eval, hf,hg]

def cellSafe (f : Formula) (cell : ℚ × ℚ) : Prop :=
  f.eval cell.1 = false ∧ f.eval cell.2 = false ∧
  f.eval ((cell.1+cell.2)/2) = false ∧
  ∀ line ∈ f.leaves, stable line cell.1 cell.2
instance (f : Formula) (cell : ℚ × ℚ) : Decidable (cellSafe f cell) := by
  unfold cellSafe; infer_instance

theorem cell_safe (f : Formula) (cell : ℚ × ℚ) (h : cellSafe f cell)
    (t : ℚ) (ht : cell.1 ≤ t ∧ t ≤ cell.2) : f.eval t = false := by
  rcases eq_or_lt_of_le ht.1 with heq | hlt
  · simpa [← heq] using h.1
  rcases eq_or_lt_of_le ht.2 with heq | hlt'
  · simpa [heq] using h.2.1
  rw [formula_constant f cell.1 cell.2 t h.2.2.2 ⟨hlt,hlt'⟩]
  exact h.2.2.1

def partition (lo hi : ℚ) : List (ℚ × ℚ) → Prop
  | [] => lo = hi
  | cell :: rest => cell.1 = lo ∧ lo < cell.2 ∧ partition cell.2 hi rest
instance (lo hi : ℚ) (cells : List (ℚ × ℚ)) : Decidable (partition lo hi cells) := by
  induction cells generalizing lo with
  | nil => unfold partition; infer_instance
  | cons c cs ih => unfold partition; infer_instance

theorem partition_covers (cells : List (ℚ × ℚ)) (lo hi t : ℚ)
    (hp : partition lo hi cells) (hlt : lo < hi) (ht : lo ≤ t ∧ t ≤ hi) :
    ∃ cell ∈ cells, cell.1 ≤ t ∧ t ≤ cell.2 := by
  induction cells generalizing lo with
  | nil => simp only [partition] at hp; linarith
  | cons cell rest ih =>
    rcases hp with ⟨hfirst,hstep,htail⟩
    by_cases h : t ≤ cell.2
    · exact ⟨cell, List.mem_cons_self, by simpa [hfirst] using ht.1, h⟩
    · have hb : cell.2 < t := lt_of_not_ge h
      obtain ⟨c,hc,range⟩ := ih cell.2 htail (by linarith [ht.2]) ⟨le_of_lt hb,ht.2⟩
      exact ⟨c,List.mem_cons_of_mem _ hc,range⟩

def accepted (f : Formula) (cells : List (ℚ × ℚ)) : Prop :=
  partition 0 1 cells ∧ ∀ cell ∈ cells, cellSafe f cell
instance (f : Formula) (cells : List (ℚ × ℚ)) : Decidable (accepted f cells) := by
  unfold accepted; infer_instance

theorem accepted_sound (f : Formula) (cells : List (ℚ × ℚ)) (h : accepted f cells) :
    ∀ t : ℚ, 0 ≤ t → t ≤ 1 → f.eval t = false := by
  intro t hlo hhi
  obtain ⟨cell,hmem,ht⟩ := partition_covers cells 0 1 t h.1 (by norm_num) ⟨hlo,hhi⟩
  exact cell_safe f cell (h.2 cell hmem) t ht

-- Polygon predicates are expressions in exact affine signs, not sampled geometry.
def qside (a b p : QPoint) : ℚ := (b.1-a.1)*(p.2-a.2)-(b.2-a.2)*(p.1-a.1)
def interpolate (a b : QPoint) (t : ℚ) : QPoint :=
  (a.1+t*(b.1-a.1), a.2+t*(b.2-a.2))
def sideLine (a b start finish : QPoint) : Affine :=
  (qside a b finish-qside a b start, qside a b start)
theorem side_line_value (a b start finish : QPoint) (t : ℚ) :
    value (sideLine a b start finish) t = qside a b (interpolate start finish t) := by
  unfold value sideLine qside interpolate; ring

def negateLine (f : Affine) : Affine := (-f.1,-f.2)
def ge (f : Affine) : Formula := .neg (.lt f)
def gt (f : Affine) : Formula := .lt (negateLine f)
def disj (f g : Formula) : Formula := .neg (.conj (.neg f) (.neg g))
def all (fs : List Formula) : Formula := fs.foldr Formula.conj (.truth true)
def any (fs : List Formula) : Formula := fs.foldr disj (.truth false)
def coordLine (start finish : QPoint) (axis : Bool) (c : ℚ) : Affine :=
  if axis then (finish.1-start.1,start.1-c) else (finish.2-start.2,start.2-c)
def boundaryEdge (a b start finish : QPoint) : Formula := all
  [.eq (sideLine a b start finish),
   ge (coordLine start finish true (min a.1 b.1)),
   ge (negateLine (coordLine start finish true (max a.1 b.1))),
   ge (coordLine start finish false (min a.2 b.2)),
   ge (negateLine (coordLine start finish false (max a.2 b.2)))]
def crossingRay (a b start finish : QPoint) : RayCross :=
  if a.2 < b.2 then ⟨1, coordLine start finish false a.2,
    coordLine start finish false b.2, negateLine (sideLine a b start finish)⟩
  else if b.2 < a.2 then ⟨-1, coordLine start finish false b.2,
    coordLine start finish false a.2, sideLine a b start finish⟩
  else ⟨0,(0,0),(0,0),(0,0)⟩

def polygonEdges (polygon : List QPoint) : List (QPoint × QPoint) :=
  polygon.zip (polygon.drop 1 ++ polygon.take 1)
def polygonFormula (polygon : List QPoint) (start finish : QPoint) : Formula :=
  .conj (.neg (any ((polygonEdges polygon).map (fun e => boundaryEdge e.1 e.2 start finish))))
    (.winding ((polygonEdges polygon).map (fun e => crossingRay e.1 e.2 start finish)))
def obstaclesFormula (polygons : List (List QPoint)) (start finish : QPoint) : Formula :=
  any (polygons.map (fun p => polygonFormula p start finish))
def FreeSegment (polygons : List (List QPoint)) (a b : QPoint) : Prop :=
  ∀ t : ℚ, 0 ≤ t → t ≤ 1 → (obstaclesFormula polygons a b).eval t = false

theorem segment_admission (polygons : List (List QPoint)) (a b : QPoint)
    (cells : List (ℚ × ℚ)) (h : accepted (obstaclesFormula polygons a b) cells) :
    FreeSegment polygons a b := accepted_sound _ _ h

theorem blocked_segment (polygons : List (List QPoint)) (a b : QPoint) (t : ℚ)
    (hlo : 0 ≤ t) (hhi : t ≤ 1) (hit : (obstaclesFormula polygons a b).eval t = true) :
    ¬FreeSegment polygons a b := by
  intro free
  have h := free t hlo hhi
  rw [hit] at h
  contradiction

-- Closed-segment intersection and polygon-boundary contact are geometric Props.
def OnSegment (p a b : QPoint) : Prop :=
  qside a b p = 0 ∧ min a.1 b.1 ≤ p.1 ∧ p.1 ≤ max a.1 b.1 ∧
  min a.2 b.2 ≤ p.2 ∧ p.2 ≤ max a.2 b.2
def SegmentContact (a b c d : QPoint) : Prop := ∃ p, OnSegment p a b ∧ OnSegment p c d
def BoundaryContact (polygon : List QPoint) (a b : QPoint) : Prop :=
  ∃ edge ∈ polygonEdges polygon, SegmentContact a b edge.1 edge.2

theorem intersection_witness (a b c d p : QPoint)
    (hab : OnSegment p a b) (hcd : OnSegment p c d) : SegmentContact a b c d := ⟨p,hab,hcd⟩
theorem boundary_contact_witness (polygon : List QPoint) (a b c d p : QPoint)
    (edge : (c,d) ∈ polygonEdges polygon) (hab : OnSegment p a b) (hcd : OnSegment p c d) :
    BoundaryContact polygon a b := ⟨(c,d),edge,p,hab,hcd⟩

theorem value_negate (f : Affine) (t : ℚ) : value (negateLine f) t = -value f t := by
  unfold value negateLine; ring

theorem coord_line_x (a b : QPoint) (c t : ℚ) :
    value (coordLine a b true c) t = (interpolate a b t).1-c := by
  simp only [value,coordLine,interpolate,ite_true,Prod.fst]; ring

theorem coord_line_y (a b : QPoint) (c t : ℚ) :
    value (coordLine a b false c) t = (interpolate a b t).2-c := by
  simp only [value,coordLine,interpolate,Bool.false_eq_true,ite_false,Prod.snd]; ring

theorem all_eval (fs : List Formula) (t : ℚ) : (all fs).eval t = true ↔ ∀ f ∈ fs, f.eval t = true := by
  induction fs with
  | nil => simp [all,Formula.eval]
  | cons f fs ih => simp only [all,List.foldr_cons,Formula.eval,Bool.and_eq_true,List.forall_mem_cons]; exact and_congr Iff.rfl ih

theorem any_eval (fs : List Formula) (t : ℚ) : (any fs).eval t = true ↔ ∃ f ∈ fs, f.eval t = true := by
  induction fs with
  | nil => simp [any,Formula.eval]
  | cons f fs ih =>
    simp only [any,List.foldr_cons,disj,Formula.eval,Bool.not_eq_true',Bool.and_eq_false_iff,Bool.not_eq_false',List.mem_cons,exists_eq_or_imp]
    exact or_congr Iff.rfl ih

theorem boundary_edge_eval (a b start finish : QPoint) (t : ℚ) :
    (boundaryEdge a b start finish).eval t = true ↔ OnSegment (interpolate start finish t) a b := by
  simp [boundaryEdge, all_eval, Formula.eval, ge, value_negate, side_line_value,
    coord_line_x,coord_line_y,OnSegment]

def rayCount (a b p : QPoint) : Int :=
  if a.2 ≤ p.2 ∧ p.2 < b.2 ∧ 0 < qside a b p then 1
  else if b.2 ≤ p.2 ∧ p.2 < a.2 ∧ qside a b p < 0 then -1 else 0

theorem crossing_ray_eval (a b start finish : QPoint) (t : ℚ) :
    (crossingRay a b start finish).eval t = rayCount a b (interpolate start finish t) := by
  unfold crossingRay
  split_ifs with hup hdown
  · have hnot : ¬(b.2 ≤ (interpolate start finish t).2 ∧ (interpolate start finish t).2 < a.2 ∧ qside a b (interpolate start finish t) < 0) := by
      rintro ⟨h1,h2,_⟩; linarith
    simp [RayCross.eval, rayCount,coord_line_y,value_negate,side_line_value,hnot]
  · have hnot : ¬(a.2 ≤ (interpolate start finish t).2 ∧ (interpolate start finish t).2 < b.2 ∧ 0 < qside a b (interpolate start finish t)) := by
      rintro ⟨h1,h2,_⟩; linarith
    simp [RayCross.eval, rayCount,coord_line_y,value_negate,side_line_value,hnot]
  · have heq : a.2 = b.2 := by linarith
    have hu : ¬(a.2 ≤ (interpolate start finish t).2 ∧ (interpolate start finish t).2 < b.2 ∧ 0 < qside a b (interpolate start finish t)) := by
      rintro ⟨h1,h2,_⟩; linarith
    have hd : ¬(b.2 ≤ (interpolate start finish t).2 ∧ (interpolate start finish t).2 < a.2 ∧ qside a b (interpolate start finish t) < 0) := by
      rintro ⟨h1,h2,_⟩; linarith
    simp [RayCross.eval,rayCount,hu,hd,value]

def windingAt (polygon : List QPoint) (p : QPoint) : Int :=
  ((polygonEdges polygon).map (fun e => rayCount e.1 e.2 p)).sum
def polygonBoundary (polygon : List QPoint) (p : QPoint) : Prop :=
  ∃ e ∈ polygonEdges polygon, OnSegment p e.1 e.2
def polygonInterior (polygon : List QPoint) (p : QPoint) : Prop :=
  ¬polygonBoundary polygon p ∧ windingAt polygon p ≠ 0

theorem polygon_formula_spec (polygon : List QPoint) (a b : QPoint) (t : ℚ) :
    (polygonFormula polygon a b).eval t = true ↔ polygonInterior polygon (interpolate a b t) := by
  simp only [polygonFormula,Formula.eval,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
    List.map_map,Function.comp_def]
  rw [Bool.eq_false_iff]
  simp only [ne_eq,any_eval,crossing_ray_eval]
  have boundary : (∃ f ∈ (polygonEdges polygon).map (fun e => boundaryEdge e.1 e.2 a b), f.eval t = true) ↔
      polygonBoundary polygon (interpolate a b t) := by
    constructor
    · rintro ⟨f,hf,htrue⟩
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hf
      exact ⟨e,he,(boundary_edge_eval _ _ _ _ _).mp htrue⟩
    · rintro ⟨e,he,hedge⟩
      exact ⟨boundaryEdge e.1 e.2 a b,List.mem_map.mpr ⟨e,he,rfl⟩,
        (boundary_edge_eval _ _ _ _ _).mpr hedge⟩
  exact and_congr (not_congr boundary) Iff.rfl

theorem free_segment_spec (polygons : List (List QPoint)) (a b : QPoint) :
    FreeSegment polygons a b ↔ ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      ∀ polygon ∈ polygons, ¬polygonInterior polygon (interpolate a b t) := by
  simp [FreeSegment,obstaclesFormula,any_eval,polygon_formula_spec,Bool.eq_false_iff]

#print axioms free_segment_spec

theorem interpolate_on_segment (a b : QPoint) (t : ℚ) (hlo : 0 ≤ t) (hhi : t ≤ 1) :
    OnSegment (interpolate a b t) a b := by
  constructor
  · unfold qside interpolate; ring
  constructor
  · simp only [interpolate, Prod.fst, Prod.snd]
    rcases le_total a.1 b.1 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  constructor
  · simp only [interpolate, Prod.fst, Prod.snd]
    rcases le_total a.1 b.1 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  constructor
  · simp only [interpolate, Prod.fst, Prod.snd]
    rcases le_total a.2 b.2 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · simp only [interpolate, Prod.fst, Prod.snd]
    rcases le_total a.2 b.2 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

theorem on_segment_parameter (p a b : QPoint) (h : OnSegment p a b) :
    ∃ t : ℚ, 0 ≤ t ∧ t ≤ 1 ∧ p = interpolate a b t := by
  rcases h with ⟨hs,hxlo,hxhi,hylo,hyhi⟩
  unfold qside at hs
  by_cases hx : b.1-a.1 = 0
  · have heqx : a.1 = b.1 := by linarith
    have px : p.1 = a.1 := by simp only [← heqx, min_self, max_self] at hxlo hxhi; exact le_antisymm hxhi hxlo
    by_cases hy : b.2-a.2 = 0
    · have heqy : a.2 = b.2 := by linarith
      have py : p.2 = a.2 := by simp only [← heqy, min_self, max_self] at hylo hyhi; exact le_antisymm hyhi hylo
      exact ⟨0,by norm_num,by norm_num,by ext <;> simp [interpolate,px,py]⟩
    · let t := (p.2-a.2)/(b.2-a.2)
      have eq : t*(b.2-a.2) = p.2-a.2 := div_mul_cancel₀ _ hy
      have range : 0 ≤ t ∧ t ≤ 1 := by
        rcases lt_or_gt_of_ne hy with hd | hd
        · simp only [min_eq_right (show b.2 ≤ a.2 by linarith),max_eq_left (show b.2 ≤ a.2 by linarith)] at hylo hyhi
          constructor <;> nlinarith
        · simp only [min_eq_left (show a.2 ≤ b.2 by linarith),max_eq_right (show a.2 ≤ b.2 by linarith)] at hylo hyhi
          constructor <;> nlinarith
      exact ⟨t,range.1,range.2,by ext <;> simp only [interpolate] <;> nlinarith⟩
  · let t := (p.1-a.1)/(b.1-a.1)
    have eq : t*(b.1-a.1) = p.1-a.1 := div_mul_cancel₀ _ hx
    have range : 0 ≤ t ∧ t ≤ 1 := by
      rcases lt_or_gt_of_ne hx with hd | hd
      · simp only [min_eq_right (show b.1 ≤ a.1 by linarith),max_eq_left (show b.1 ≤ a.1 by linarith)] at hxlo hxhi
        constructor <;> nlinarith
      · simp only [min_eq_left (show a.1 ≤ b.1 by linarith),max_eq_right (show a.1 ≤ b.1 by linarith)] at hxlo hxhi
        constructor <;> nlinarith
    have py : p.2 = a.2+t*(b.2-a.2) := by
      have prod : (b.1-a.1)*(p.2-(a.2+t*(b.2-a.2))) = 0 := by
        calc
          _ = (b.1-a.1)*(p.2-a.2)-(b.2-a.2)*(t*(b.1-a.1)) := by ring
          _ = 0 := by rw [eq]; linarith [hs]
      exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left hx)
    exact ⟨t,range.1,range.2,by ext <;> simp only [interpolate] <;> linarith⟩

theorem segment_contact_parameters (a b c d : QPoint) : SegmentContact a b c d ↔
    ∃ t u : ℚ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ u ∧ u ≤ 1 ∧ interpolate a b t = interpolate c d u := by
  constructor
  · rintro ⟨p,hab,hcd⟩
    obtain ⟨t,htlo,hthi,ht⟩ := on_segment_parameter p a b hab
    obtain ⟨u,hulo,huhi,hu⟩ := on_segment_parameter p c d hcd
    exact ⟨t,u,htlo,hthi,hulo,huhi,ht.symm.trans hu⟩
  · rintro ⟨t,u,htlo,hthi,hulo,huhi,heq⟩
    exact ⟨interpolate a b t,interpolate_on_segment a b t htlo hthi,
      by rw [heq]; exact interpolate_on_segment c d u hulo huhi⟩

theorem boundary_contact_parameters (polygon : List QPoint) (a b : QPoint) :
    BoundaryContact polygon a b ↔ ∃ edge ∈ polygonEdges polygon,
      ∃ t u : ℚ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ u ∧ u ≤ 1 ∧ interpolate a b t = interpolate edge.1 edge.2 u := by
  simp only [BoundaryContact,segment_contact_parameters]

-- A geometric refinement preserves coverage pointwise, including boundaries.
def triangleClosed (a b c p : QPoint) : Prop :=
  0 ≤ qside a b p ∧ 0 ≤ qside b c p ∧ 0 ≤ qside c a p

theorem side_reverse (a b p : QPoint) : qside b a p = -qside a b p := by
  unfold qside; ring

theorem side_split_first (a b c p : QPoint) (t : ℚ) :
    qside a (interpolate b c t) p = (1-t)*qside a b p+t*qside a c p := by
  unfold qside interpolate; ring

theorem side_split_second (b c p : QPoint) (t : ℚ) :
    qside b (interpolate b c t) p = t*qside b c p := by
  unfold qside interpolate; ring

theorem side_split_third (b c p : QPoint) (t : ℚ) :
    qside (interpolate b c t) c p = (1-t)*qside b c p := by
  unfold qside interpolate; ring

theorem triangle_edge_split_coverage (a b c p : QPoint) (t : ℚ)
    (htlo : 0 < t) (hthi : t < 1) :
    triangleClosed a b c p ↔
      triangleClosed a b (interpolate b c t) p ∨ triangleClosed a (interpolate b c t) c p := by
  have rev : qside (interpolate b c t) a p = -((1-t)*qside a b p+t*qside a c p) := by
    rw [side_reverse, side_split_first]
  have revc : qside c a p = -qside a c p := side_reverse a c p
  simp only [triangleClosed, side_split_second, side_split_third, side_split_first,rev,revc]
  have hp : 0 < 1-t := by linarith
  constructor
  · rintro ⟨hab,hbc,hca⟩
    by_cases h : (1-t)*qside a b p+t*qside a c p ≤ 0
    · left
      exact ⟨hab,mul_nonneg (le_of_lt htlo) hbc,by linarith⟩
    · right
      exact ⟨le_of_lt (lt_of_not_ge h),mul_nonneg (le_of_lt hp) hbc,hca⟩
  · rintro (⟨hab,hbm,hma⟩ | ⟨ham,hmc,hca⟩)
    · have hbc : 0 ≤ qside b c p := by nlinarith
      have hca : qside a c p ≤ 0 := by nlinarith
      exact ⟨hab,hbc,by linarith⟩
    · have hbc : 0 ≤ qside b c p := by nlinarith
      have hab : 0 ≤ qside a b p := by nlinarith
      exact ⟨hab,hbc,hca⟩

abbrev Triangle := QPoint × QPoint × QPoint
def inTriangle (tri : Triangle) (p : QPoint) : Prop := triangleClosed tri.1 tri.2.1 tri.2.2 p
def meshCovers (mesh : List Triangle) (p : QPoint) : Prop := ∃ tri ∈ mesh, inTriangle tri p

theorem mesh_refinement_coverage (before suffix : List Triangle) (a b c : QPoint) (t : ℚ)
    (htlo : 0 < t) (hthi : t < 1) (p : QPoint) :
    meshCovers (before ++ (a,b,c) :: suffix) p ↔
    meshCovers (before ++ (a,b,interpolate b c t) :: (a,interpolate b c t,c) :: suffix) p := by
  simp only [meshCovers,List.mem_append,List.mem_cons,or_and_right,exists_or,exists_eq_left,inTriangle,Prod.fst,Prod.snd]
  rw [triangle_edge_split_coverage a b c p t htlo hthi]
  aesop

#print axioms segment_contact_parameters
#print axioms triangle_edge_split_coverage
#print axioms mesh_refinement_coverage

inductive Refines : List Triangle → List Triangle → Prop where
  | refl (mesh : List Triangle) : Refines mesh mesh
  | split (before after : List Triangle) (a b c : QPoint) (t : ℚ)
      (htlo : 0 < t) (hthi : t < 1) :
      Refines (before ++ (a,b,c) :: after)
        (before ++ (a,b,interpolate b c t) :: (a,interpolate b c t,c) :: after)
  | trans {a b c : List Triangle} : Refines a b → Refines b c → Refines a c

theorem refinement_coverage {a b : List Triangle} (h : Refines a b) (p : QPoint) :
    meshCovers a p ↔ meshCovers b p := by
  induction h with
  | refl => rfl
  | split before after a b c t htlo hthi =>
    exact mesh_refinement_coverage before after a b c t htlo hthi p
  | trans hab hbc ihab ihbc => exact ihab.trans ihbc

#print axioms refinement_coverage

-- Source-bound graph interpretation. All pairs, including rejected pairs, are
-- certified. This is stronger than proving optimality in an arbitrary edge list.
open PerfectPower.GeometryCertificates

def qpoint (p : Point) : QPoint := (p.1,p.2)
def weight (a b : Point) : Int := |b.1-a.1| + |b.2-a.2|
def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun u => ((List.range n).filter (fun v => u ≠ v)).map (fun v => (u,v)))
def vertex (nodes : List Point) (u : Nat) : Point := nodes[u]?.getD (0,0)
def graph (nodes : List Point) (admitted : List (Nat × Nat)) : List Edge :=
  (pairs nodes.length).filterMap (fun e => if e ∈ admitted then
    some (e.1,e.2,weight (vertex nodes e.1) (vertex nodes e.2)) else none)

theorem mem_pairs (n u v : Nat) : (u,v) ∈ pairs n ↔ u < n ∧ v < n ∧ u ≠ v := by
  simp [pairs, List.mem_flatMap, List.mem_map]

theorem mem_graph (nodes : List Point) (admitted : List (Nat × Nat)) (u v : Nat) (w : Int) :
    (u,v,w) ∈ graph nodes admitted ↔
    u < nodes.length ∧ v < nodes.length ∧ u ≠ v ∧ (u,v) ∈ admitted ∧
      w = weight (vertex nodes u) (vertex nodes v) := by
  simp only [graph, List.mem_filterMap]
  constructor
  · rintro ⟨⟨i,j⟩,hpair,heq⟩
    split_ifs at heq with h
    · have eq := Option.some.inj heq
      have eqi : i = u := congrArg Prod.fst eq
      have eqj : j = v := congrArg (fun e : Edge => e.2.1) eq
      have eqw : weight (vertex nodes i) (vertex nodes j) = w := congrArg (fun e : Edge => e.2.2) eq
      subst i; subst j
      exact ⟨(mem_pairs _ _ _).mp hpair |>.1, (mem_pairs _ _ _).mp hpair |>.2.1,
        (mem_pairs _ _ _).mp hpair |>.2.2,h,eqw.symm⟩
  · rintro ⟨hu,hv,hne,hadmit,rfl⟩
    exact ⟨(u,v),(mem_pairs _ _ _).mpr ⟨hu,hv,hne⟩,by simp [hadmit]⟩

inductive GeometricWalk (polygons : List (List QPoint)) (nodes : List Point) : Nat → Nat → Int → Prop where
  | nil (u : Nat) : GeometricWalk polygons nodes u u 0
  | cons {u v t : Nat} {c : Int} (hu : u < nodes.length) (hv : v < nodes.length)
      (hne : u ≠ v) (free : FreeSegment polygons (qpoint (vertex nodes u)) (qpoint (vertex nodes v)))
      (tail : GeometricWalk polygons nodes v t c) :
      GeometricWalk polygons nodes u t (weight (vertex nodes u) (vertex nodes v)+c)

theorem geometric_walk_to_graph (polygons : List (List QPoint)) (nodes : List Point)
    (admitted : List (Nat × Nat))
    (complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
      ((u,v) ∈ admitted ↔ FreeSegment polygons (qpoint (vertex nodes u)) (qpoint (vertex nodes v))))
    {s t : Nat} {c : Int} (walk : GeometricWalk polygons nodes s t c) :
    Walk (graph nodes admitted) s t c := by
  induction walk with
  | nil u => exact Walk.nil u
  | cons hu hv hne free tail ih =>
    exact Walk.cons ((mem_graph _ _ _ _ _).mpr ⟨hu,hv,hne,(complete _ _ hu hv hne).mpr free,rfl⟩) ih

theorem geometric_optimal_walk (polygons : List (List QPoint)) (nodes : List Point)
    (admitted : List (Nat × Nat))
    (complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
      ((u,v) ∈ admitted ↔ FreeSegment polygons (qpoint (vertex nodes u)) (qpoint (vertex nodes v))))
    (p : Nat → Int) (bounds : ∀ e ∈ graph nodes admitted, p e.2.1 ≤ p e.1 + e.2.2)
    {s t : Nat} {cost other : Int} (attained : cost = p t-p s)
    (walk : GeometricWalk polygons nodes s t other) : cost ≤ other :=
  optimal_walk _ p bounds attained (geometric_walk_to_graph polygons nodes admitted complete walk)

#print axioms accepted_sound
#print axioms segment_admission
#print axioms geometric_optimal_walk
end PerfectPower.GeometryAdmission
