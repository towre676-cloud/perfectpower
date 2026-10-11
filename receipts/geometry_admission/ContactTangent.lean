import PerfectPower.GeometryContact
namespace PerfectPower.CheckedContact.C6a120ed4eb079a015463135bf32d2005bab0541ecad13fcb488c1f8f68c5d1c9
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
def polygon : List QPoint := [(((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))), (((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))), (((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)))]
def start : QPoint := (((-1 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))
def finish : QPoint := (((1 : ℚ)/(1 : ℚ)),((-1 : ℚ)/(1 : ℚ)))
theorem contact : BoundaryContact polygon start finish :=
  boundary_contact_witness polygon start finish (((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ))) (by decide +kernel) (by decide +kernel) (by decide +kernel)
#print axioms contact
end PerfectPower.CheckedContact.C6a120ed4eb079a015463135bf32d2005bab0541ecad13fcb488c1f8f68c5d1c9
