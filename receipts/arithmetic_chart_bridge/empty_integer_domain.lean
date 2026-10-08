import PerfectPower.RationalPowerAtlas
namespace PowerCharts_299c1bac93b04e05
open PerfectPower.RationalPowerAtlas
open PerfectPower.ResidueAtlas (Bounds)
def F (x y : ℤ) : ℤ := (1) * (x)^0 * (y)^0 + (-2) * (x)^0 * (y)^2
def bounds : Bounds := ((-3,3),(-3,3))
theorem source_periodic (x y : ℤ) : F x y % 2=F (x%2) (y%2) % 2 := by
  change Int.ModEq 2 (F x y) (F (x%2) (y%2))
  have hx : Int.ModEq 2 x (x%2) := (Int.mod_modEq x 2).symm
  have hy : Int.ModEq 2 y (y%2) := (Int.mod_modEq y 2).symm
  unfold F
  exact ((((Int.ModEq.refl (1)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 0 hy)).add (((Int.ModEq.refl (-2)).mul (Int.ModEq.pow 0 hx)).mul (Int.ModEq.pow 2 hy)))
def emptyCover : PerfectPower.ResidueAtlas.AtlasPacket F 2 := ⟨by norm_num,∅,by decide +kernel,source_periodic⟩
theorem no_integer_solution (x y : ℤ) : F x y≠0 := emptyCover.empty_obstruction rfl x y
#print axioms source_periodic
#print axioms no_integer_solution
def accepts (x y : ℤ) : Prop := F x y=0 ∧ (True)
instance : DecidablePred (fun z : ℤ×ℤ => accepts z.1 z.2) := fun z => by unfold accepts; infer_instance
def sourcePoints : Finset (ℤ×ℤ) := ((Finset.Icc (-3) (3)).product (Finset.Icc (-3) (3))).filter fun z => accepts z.1 z.2
def points : Finset (ℤ×ℤ) := ∅
theorem points_checked : sourcePoints=points := by decide +kernel
theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ -3≤x ∧ x≤3 ∧ -3≤y ∧ y≤3 ∧ accepts x y := by
  rw [← points_checked]; simp only [sourcePoints,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]; tauto
#print axioms points_checked
#print axioms points_complete
end PowerCharts_299c1bac93b04e05
