import PerfectPower.GeometryFoundations
namespace PerfectPower.CheckedGeometry.Area74a58f468b1cf56d9e8c554fc3eab4967e520cb9e330af48078ffa0e674951b5
theorem triangle_0_determinant : ((4 : Int)-(4))*((2)-(0))-((4)-(0))*((2)-(4))=(8) := by decide
theorem triangle_0_positive : (0 : Int)<(((4 : Int)-(4))*((2)-(0))-((4)-(0))*((2)-(4))) := by decide
theorem triangle_1_determinant : ((4 : Int)-(0))*((2)-(0))-((0)-(0))*((2)-(0))=(8) := by decide
theorem triangle_1_positive : (0 : Int)<(((4 : Int)-(0))*((2)-(0))-((0)-(0))*((2)-(0))) := by decide
theorem triangle_2_determinant : ((2 : Int)-(0))*((4)-(0))-((2)-(0))*((0)-(0))=(8) := by decide
theorem triangle_2_positive : (0 : Int)<(((2 : Int)-(0))*((4)-(0))-((2)-(0))*((0)-(0))) := by decide
theorem source_polygon_area : Int.natAbs (((0 : Int)*(0)-(0)*(4))+((4 : Int)*(4)-(0)*(4))+((4 : Int)*(2)-(4)*(2))+((2 : Int)*(4)-(2)*(0))+((0 : Int)*(0)-(4)*(0)))=(24) := by decide
theorem area_conservation : (8 : Int)+(8 : Int)+(8 : Int)=(24) := by decide
#print axioms area_conservation
end PerfectPower.CheckedGeometry.Area74a58f468b1cf56d9e8c554fc3eab4967e520cb9e330af48078ffa0e674951b5
