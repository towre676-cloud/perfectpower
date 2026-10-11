import PerfectPower.GeometryContact
namespace PerfectPower.CheckedContact.Ca5f0e536a28c520a07e80e7c44ead96c76db4273b152484404861232f81d8a58
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
def polygon : List QPoint := [(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)))]
def start : QPoint := (((-1 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))
def finish : QPoint := (((3 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))
theorem contact : BoundaryContact polygon start finish :=
  boundary_contact_witness polygon start finish (((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))) (((2 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
#print axioms contact
end PerfectPower.CheckedContact.Ca5f0e536a28c520a07e80e7c44ead96c76db4273b152484404861232f81d8a58
