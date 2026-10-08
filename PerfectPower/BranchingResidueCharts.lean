import PerfectPower.ResidueAtlas

namespace PerfectPower.BranchingResidueCharts
open PerfectPower.ResidueAtlas

/-- A nonzero content factor is removed only after an exact affine identity. -/
structure Chart (F : ℤ → ℤ → ℤ) where
  a : ℤ
  b : ℤ
  step : ℤ
  content : ℤ
  equation : ℤ → ℤ → ℤ
  positive : 0<step
  nonzero : content ≠ 0
  identity : ∀ u v, F (a+step*u) (b+step*v) = content*equation u v

theorem Chart.zero_iff {F} (chart : Chart F) (u v : ℤ) :
    F (chart.a+chart.step*u) (chart.b+chart.step*v)=0 ↔ chart.equation u v=0 := by
  rw [chart.identity,mul_eq_zero]
  simp only [chart.nonzero,false_or]

/-- Subcharts compose both source coordinates and removed content exactly. -/
def Chart.compose {F} (chart : Chart F) (child : Chart chart.equation) : Chart F where
  a := chart.a+chart.step*child.a
  b := chart.b+chart.step*child.b
  step := chart.step*child.step
  content := chart.content*child.content
  equation := child.equation
  positive := mul_pos chart.positive child.positive
  nonzero := mul_ne_zero chart.nonzero child.nonzero
  identity u v := by
    have hx : chart.a+chart.step*child.a+chart.step*child.step*u =
        chart.a+chart.step*(child.a+child.step*u) := by ring
    have hy : chart.b+chart.step*child.b+chart.step*child.step*v =
        chart.b+chart.step*(child.b+child.step*v) := by ring
    rw [hx,hy,chart.identity,child.identity]
    ring

/-- Splitting by every modular root covers every exact zero in signed coordinates. -/
theorem split_zero_cover {F m} (atlas : AtlasPacket F m) (x y : ℤ) :
    F x y=0 ↔ ∃ z ∈ atlas.roots, ∃ u v : ℤ,
      x=z.1+m*u ∧ y=z.2+m*v ∧ F (z.1+m*u) (z.2+m*v)=0 := by
  constructor
  · intro h
    refine ⟨(x%m,y%m),atlas.source_survives x y h,x/m,y/m,?_,?_,?_⟩
    · exact (Int.emod_add_ediv x m).symm
    · exact (Int.emod_add_ediv y m).symm
    · simpa only [Int.emod_add_ediv] using h
  · rintro ⟨z,_,u,v,rfl,rfl,h⟩
    exact h

/-- Removing common prime content never discards an exact zero. -/
theorem content_zero_iff (c value : ℤ) (hc : c ≠ 0) : c*value=0 ↔ value=0 := by
  rw [mul_eq_zero]
  simp [hc]

/-- Exact complete census in a declared box, independent of any traversal. -/
def boxZeros (F : ℤ → ℤ → ℤ) (bounds : Bounds) : Finset (ℤ×ℤ) :=
  ((Finset.Icc bounds.1.1 bounds.1.2).product
    (Finset.Icc bounds.2.1 bounds.2.2)).filter fun z => F z.1 z.2=0

theorem boxZeros_complete (F : ℤ → ℤ → ℤ) (bounds : Bounds) (x y : ℤ) :
    (x,y) ∈ boxZeros F bounds ↔
      bounds.1.1≤x ∧ x≤bounds.1.2 ∧ bounds.2.1≤y ∧ y≤bounds.2.2 ∧ F x y=0 := by
  simp [boxZeros,Finset.product_eq_sprod,and_assoc]

end PerfectPower.BranchingResidueCharts
