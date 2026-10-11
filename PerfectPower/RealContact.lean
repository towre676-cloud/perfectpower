import PerfectPower.RealVisibility
namespace PerfectPower.RealContact
open PlanarCertificates PlanarGeometry
noncomputable section

def contactFormula (a b c d : QPoint) : Formula :=
  .conj (boundaryFormula a b) (boundaryFormula c d)
def disjointFormula (a b c d : QPoint) : Formula := .neg (contactFormula a b c d)
def Contact (a b c d : QPoint) : Prop := ∃ p : Point, OnSegment a b p ∧ OnSegment c d p

theorem contact_spec (a b c d : QPoint) (p : Point) :
    (contactFormula a b c d).eval (fun f => sign f p) = true ↔ OnSegment a b p ∧ OnSegment c d p := by
  simp only [contactFormula,eval_conj,boundary_spec]

theorem disjoint_from_tree (a b c d : QPoint) (tree : Tree)
    (h : checked (disjointFormula a b c d) [] tree) : ¬Contact a b c d := by
  rintro ⟨p,hab,hcd⟩
  have hp := universal_identity _ tree h p
  rw [disjointFormula,eval_neg] at hp
  exact hp ((contact_spec a b c d p).mpr ⟨hab,hcd⟩)

def rationalSign (f : Plane) (p : QPoint) : Int :=
  let v := f.1*p.1+f.2.1*p.2+f.2.2
  if v < 0 then -1 else if v = 0 then 0 else 1

theorem rational_point_eval (f : Formula) (p : QPoint) :
    f.eval (fun a => sign a ((p.1 : ℝ),(p.2 : ℝ))) = f.eval (fun a => rationalSign a p) := by
  have hs : (fun a => sign a ((p.1 : ℝ),(p.2 : ℝ))) = (fun a => rationalSign a p) := by
    funext a; exact RealVisibility.rational_sign a p
  rw [hs]

theorem contact_from_hit (a b c d p : QPoint)
    (h : (contactFormula a b c d).eval (fun f => rationalSign f p) = true) : Contact a b c d := by
  refine ⟨((p.1 : ℝ),(p.2 : ℝ)),?_⟩
  apply (contact_spec a b c d _).mp
  rw [rational_point_eval]
  exact h

#print axioms disjoint_from_tree
#print axioms contact_from_hit
end
end PerfectPower.RealContact
