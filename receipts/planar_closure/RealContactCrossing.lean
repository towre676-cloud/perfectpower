import PerfectPower.RealContact
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open PerfectPower.PlanarCertificates
namespace RealContactCrossing
def a : ℚ × ℚ := (((0 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)))
def b : ℚ × ℚ := (((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)))
def c : ℚ × ℚ := (((0 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)))
def d : ℚ × ℚ := (((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)))
def witness : ℚ × ℚ := (((1 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)))
theorem source_hit : (PerfectPower.RealContact.contactFormula a b c d).eval (fun f => PerfectPower.RealContact.rationalSign f witness) = true := by decide +kernel
theorem source_contact : PerfectPower.RealContact.Contact a b c d :=
  PerfectPower.RealContact.contact_from_hit a b c d witness source_hit
#print axioms source_contact
end RealContactCrossing
