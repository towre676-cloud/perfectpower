import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic

namespace PerfectPower.VoronoiEnclosure

/-- A chain of checked local field differences and nonnegative segment costs. -/
inductive FieldChain {X : Type*} (f : X → ℝ) : X → X → ℝ → Prop
  | nil (x) : FieldChain f x x 0
  | cons {x y z : X} {a b : ℝ} (ha : 0 ≤ a)
      (hlocal : |f x - f y| ≤ a) (tail : FieldChain f y z b) :
      FieldChain f x z (a+b)

theorem chain_nonnegative {X : Type*} {f : X → ℝ} {x y : X} {c : ℝ}
    (h : FieldChain f x y c) : 0 ≤ c := by
  induction h with
  | nil => rfl
  | cons ha _ _ ih => exact add_nonneg ha ih

theorem chain_bound {X : Type*} {f : X → ℝ} {x y : X} {c : ℝ}
    (h : FieldChain f x y c) : |f x-f y| ≤ c := by
  induction h with
  | nil => simp
  | @cons x y z a b ha hlocal tail ih =>
      have ht := abs_add (f x-f y) (f y-f z)
      have he : (f x-f y)+(f y-f z)=f x-f z := by ring
      rw [he] at ht
      linarith

/-- The missing geometric input is explicit: checked chains approximate distance.
This lemma does not construct the quotient surface or assert its identification. -/
theorem global_field_bound {X : Type*} [PseudoMetricSpace X] (f : X → ℝ)
    (hchains : ∀ x y ε, 0 < ε → ∃ c, FieldChain f x y c ∧ c ≤ dist x y+ε)
    (x y : X) : |f x-f y| ≤ dist x y := by
  by_contra h
  have hp : 0 < |f x-f y|-dist x y := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨c,hc,hbound⟩ := hchains x y ((|f x-f y|-dist x y)/2) (by linarith)
  have hb := chain_bound hc
  linarith

/-- Shared endpoint values give the same affine readout on a glued edge. -/
theorem edge_gluing (a b t : ℝ) :
    (1-t)*a+t*b = t*b+(1-t)*a := by ring

theorem field_distance_lower {X : Type*} [PseudoMetricSpace X] (f : X → ℝ)
    (hf : ∀ x y, |f x-f y| ≤ dist x y) (p s : X) :
    |f p-f s| ≤ dist p s := hf p s

/-- Finite patch coverage plus strict winner checks encloses every nearest-site tie. -/
theorem boundary_coverage {X I J : Type*} [PseudoMetricSpace X]
    (patch : J → Set X) (unresolved : Set J) (site : I → X)
    (cover : ∀ z, ∃ j, z ∈ patch j)
    (strict : ∀ j, j ∉ unresolved → ∃ i, ∀ z ∈ patch j,
      ∀ k, k ≠ i → dist z (site i) < dist z (site k))
    (z : X) (a b : I) (hab : a ≠ b)
    (hmin : ∀ i, dist z (site a) ≤ dist z (site i))
    (htie : dist z (site a)=dist z (site b)) :
    ∃ j ∈ unresolved, z ∈ patch j := by
  obtain ⟨j,hz⟩ := cover z
  refine ⟨j,?_,hz⟩
  by_contra hj
  obtain ⟨i,hi⟩ := strict j hj
  by_cases hia : a=i
  · have hbi : b ≠ i := by intro h; apply hab; exact hia.trans h.symm
    have hs := hi z hz b hbi
    rw [← hia] at hs
    linarith
  · have hs := hi z hz a hia
    have hm := hmin i
    linarith

/-- An enclosure radius survives an explicit global metric upper comparison. -/
theorem radius_transfer {X : Type*} (d e : X → X → ℝ) (u r : ℝ)
    (hu : 0 ≤ u) (hcompare : ∀ x y, e x y ≤ u*d x y)
    (p z : X) (hr : d p z ≤ r) : e p z ≤ u*r :=
  (hcompare p z).trans (mul_le_mul_of_nonneg_left hr hu)

/-- Transfer the strict patch rule to a second metric on a mapped surface.
Comparison hypotheses are required globally and are not numerical estimates. -/
theorem transferred_winner {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (φ : X → Y) (l u U L r : ℝ) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : ∀ x y, l*dist x y ≤ dist (φ x) (φ y))
    (hup : ∀ x y, dist (φ x) (φ y) ≤ u*dist x y)
    (p z s t : X) (hz : dist p z ≤ r) (hs : dist p s ≤ U)
    (ht : L ≤ dist p t) (hsep : u*U+2*(u*r)<l*L) :
    dist (φ z) (φ s) < dist (φ z) (φ t) := by
  have hz' := radius_transfer (fun x y => dist x y)
    (fun x y => dist (φ x) (φ y)) u r hu hup p z hz
  have hs' := (hup p s).trans (mul_le_mul_of_nonneg_left hs hu)
  have ht' := (mul_le_mul_of_nonneg_left ht hl).trans (hlo p t)
  have h1 := dist_triangle (φ z) (φ p) (φ s)
  have h2 := dist_triangle (φ p) (φ z) (φ t)
  rw [dist_comm (φ z) (φ p)] at h1
  linarith

/-- Midpoint refinement preserves affine edge interpolation. -/
theorem midpoint_affine (a b : ℝ) : (a+b)/2=(1-(1/2:ℝ))*a+(1/2:ℝ)*b := by ring

/-- Four equal-area children preserve a patch's total rational area. -/
theorem quarter_area (a : ℚ) : a/4+a/4+a/4+a/4=a := by ring

/-- A strict Voronoi winner is unique, including on pseudometric spaces. -/
theorem winner_unique {X I : Type*} [PseudoMetricSpace X] (site : I → X)
    (z : X) (i j : I)
    (hi : ∀ k, k ≠ i → dist z (site i)<dist z (site k))
    (hj : ∀ k, k ≠ j → dist z (site j)<dist z (site k)) : i=j := by
  by_contra h
  have h1 := hi j (Ne.symm h)
  have h2 := hj i h
  linarith

/-- Coordinates of the four midpoint children in a parent triangle. -/
noncomputable def quarterMap (i : Fin 4) (u v w : ℝ) : ℝ × ℝ × ℝ :=
  if i.val=0 then (u+(v+w)/2,v/2,w/2)
  else if i.val=1 then (u/2,u/2+v+w/2,w/2)
  else if i.val=2 then (u/2,v/2,(u+v)/2+w)
  else ((u+w)/2,(u+v)/2,(v+w)/2)

/-- Actual geometric coverage, rather than equality of area totals. -/
theorem midpoint_cover (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hs : x+y+z=1) :
    ∃ (i : Fin 4) (u v w : ℝ), 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧
      u+v+w=1 ∧ quarterMap i u v w=(x,y,z) := by
  by_cases ha : 1/2 ≤ x
  · refine ⟨(⟨0, by decide⟩ : Fin 4),2*x-1,2*y,2*z,by linarith,by linarith,by linarith,by linarith,?_⟩
    ext <;> (norm_num [quarterMap] <;> linarith)
  by_cases hb : 1/2 ≤ y
  · refine ⟨(⟨1, by decide⟩ : Fin 4),2*x,2*y-1,2*z,by linarith,by linarith,by linarith,by linarith,?_⟩
    ext <;> (norm_num [quarterMap] <;> linarith)
  by_cases hc : 1/2 ≤ z
  · refine ⟨(⟨2, by decide⟩ : Fin 4),2*x,2*y,2*z-1,by linarith,by linarith,by linarith,by linarith,?_⟩
    ext <;> (norm_num [quarterMap] <;> linarith)
  refine ⟨(⟨3, by decide⟩ : Fin 4),1-2*z,1-2*x,1-2*y,by linarith,by linarith,by linarith,by linarith,?_⟩
  ext <;> (norm_num [quarterMap]; linarith)

/-- Corner radius bounds cover every convex combination in the whole patch. -/
theorem convex_radius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c : E) (u v w r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hs : u+v+w=1) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (hc : ‖c‖ ≤ r) :
    ‖u • a + v • b + w • c‖ ≤ r := by
  have h1 := norm_add_le (u • a + v • b) (w • c)
  have h2 := norm_add_le (u • a) (v • b)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw] at h1
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hu, abs_of_nonneg hv] at h2
  have h3 := mul_le_mul_of_nonneg_left ha hu
  have h4 := mul_le_mul_of_nonneg_left hb hv
  have h5 := mul_le_mul_of_nonneg_left hc hw
  have he : u*r+v*r+w*r=r := by
    calc
      u*r+v*r+w*r = (u+v+w)*r := by ring
      _ = r := by rw [hs]; ring
  linarith

/-- A finite refinement tree keeps geometric coverage separate from area. -/
inductive PatchTree (X : Type*)
  | leaf (region : Set X)
  | split (region : Set X) (children : Fin 4 → PatchTree X)

def PatchTree.region {X : Type*} : PatchTree X → Set X
  | .leaf s => s
  | .split s _ => s

def PatchTree.covered {X : Type*} : PatchTree X → X → Prop
  | .leaf s, z => z ∈ s
  | .split _ children, z => ∃ i, (children i).covered z

def PatchTree.valid {X : Type*} : PatchTree X → Prop
  | .leaf _ => True
  | .split s children => (∀ z ∈ s, ∃ i, z ∈ (children i).region) ∧
      ∀ i, (children i).valid

/-- All levels of an adaptive tree cover the original patch. -/
theorem tree_coverage {X : Type*} (tree : PatchTree X) (hvalid : tree.valid)
    (z : X) (hz : z ∈ tree.region) : tree.covered z := by
  induction tree with
  | leaf s => exact hz
  | split s children ih =>
      obtain ⟨hc,hv⟩ := hvalid
      obtain ⟨i,hi⟩ := hc z hz
      exact ⟨i,ih i (hv i) hi⟩

end PerfectPower.VoronoiEnclosure
