import PerfectPower.GeometryAdmission
namespace PerfectPower.CheckedMesh.Rd34908484848badb2aaad3a7bcc5283a956567ef5ce5aa36b1d56ee74c6ea82d
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
def mesh_0 : List Triangle := [((((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((6 : ℚ)/(1 : ℚ))))]
theorem source_positive : (0 : ℚ) < qside (((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (((6 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (((0 : ℚ)/(1 : ℚ)),((6 : ℚ)/(1 : ℚ))) := by decide +kernel
theorem refinement_0 : Refines mesh_0 mesh_0 := Refines.refl _
def mesh_1 : List Triangle := [((((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ)))), ((((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((6 : ℚ)/(1 : ℚ))))]
theorem step_1 : Refines mesh_0 mesh_1 := by
  have h := Refines.split [] [] (((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (((6 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (((0 : ℚ)/(1 : ℚ)),((6 : ℚ)/(1 : ℚ))) ((1 : ℚ)/(2 : ℚ)) (by norm_num) (by norm_num)
  have left : mesh_0 = [] ++ ((((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((6 : ℚ)/(1 : ℚ)))) :: [] := by decide +kernel
  have right : mesh_1 = [] ++ ((((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ)))) :: ((((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((6 : ℚ)/(1 : ℚ)))) :: [] := by decide +kernel
  rw [left,right]
  convert h using 1; norm_num [interpolate]
theorem refinement_1 : Refines mesh_0 mesh_1 := Refines.trans refinement_0 step_1
theorem final_triangles_positive : ∀ tri ∈ mesh_1, (0 : ℚ) < qside tri.1 tri.2.1 tri.2.2 := by decide +kernel
theorem source_coverage (p : QPoint) : meshCovers mesh_0 p ↔ meshCovers mesh_1 p :=
  refinement_coverage refinement_1 p
#print axioms source_coverage
end PerfectPower.CheckedMesh.Rd34908484848badb2aaad3a7bcc5283a956567ef5ce5aa36b1d56ee74c6ea82d
