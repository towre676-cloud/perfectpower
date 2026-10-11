import PerfectPower.GeometryContact
namespace PerfectPower.CheckedContact.C06f45a589526ff477c5cb16d7293767547320ccc10b2349f72af6e1cd5412f0c
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
def polygon : List QPoint := [(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((4 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((4 : ℚ)/(1 : ℚ)),((4 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((4 : ℚ)/(1 : ℚ)))]
def start : QPoint := (((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)))
def finish : QPoint := (((3 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)))
theorem contact : BoundaryContact polygon start finish :=
  boundary_contact_witness polygon start finish (((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (((4 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (((1 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
#print axioms contact
end PerfectPower.CheckedContact.C06f45a589526ff477c5cb16d7293767547320ccc10b2349f72af6e1cd5412f0c
