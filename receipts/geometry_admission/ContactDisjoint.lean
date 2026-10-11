import PerfectPower.GeometryContact
namespace PerfectPower.CheckedContact.C98c7b5c421cd7cf516b808d48581d61f5c243e37ec1d7d5676c148a59657ad12
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
def polygon : List QPoint := [(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((6 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ))), (((4 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ))), (((4 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((5 : ℚ)/(1 : ℚ)))]
def start : QPoint := (((3 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ)))
def finish : QPoint := (((3 : ℚ)/(1 : ℚ)),((4 : ℚ)/(1 : ℚ)))
def cells : List (ℚ × ℚ) := [(((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))]
theorem admission : accepted (boundaryFormula polygon start finish) cells := by decide +kernel
theorem disjoint : ¬BoundaryContact polygon start finish := no_boundary_contact _ _ _ _ admission
#print axioms disjoint
end PerfectPower.CheckedContact.C98c7b5c421cd7cf516b808d48581d61f5c243e37ec1d7d5676c148a59657ad12
