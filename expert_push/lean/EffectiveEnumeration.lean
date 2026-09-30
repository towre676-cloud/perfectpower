import Mathlib
/- Uncompiled draft: integrate with the repository's pinned toolchain. -/
namespace ExpertPush

def boundedSolutions (k L U V : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc L U).product (Finset.Icc (-V) V)).filter
    (fun p => p.2 ^ 2 = p.1 ^ 3 + k)

theorem mem_boundedSolutions (k L U V x y : ℤ) :
    (x,y) ∈ boundedSolutions k L U V ↔
    (L ≤ x ∧ x ≤ U) ∧ (-V ≤ y ∧ y ≤ V) ∧ y^2 = x^3+k := by
  simp [boundedSolutions, and_assoc]

theorem enumeration_complete (k L U V : ℤ)
    (bound : ∀ x y : ℤ, y^2=x^3+k →
      (L ≤ x ∧ x ≤ U) ∧ (-V ≤ y ∧ y ≤ V)) (x y : ℤ) :
    y^2=x^3+k ↔ (x,y) ∈ boundedSolutions k L U V := by
  rw [mem_boundedSolutions]
  constructor
  · intro h
    exact ⟨(bound x y h).1, (bound x y h).2, h⟩
  · intro h
    exact h.2.2

theorem even_quartic_forward (a b c u v : ℤ)
    (h : v^2 = a*u^4+b*u^2+c) :
    (a*u*v)^2=(a*u^2)^3+b*(a*u^2)^2+a*c*(a*u^2) := by
  calc
    (a*u*v)^2 = (a*u)^2 * v^2 := by ring
    _ = (a*u)^2 * (a*u^4+b*u^2+c) := by rw [h]
    _ = (a*u^2)^3+b*(a*u^2)^2+a*c*(a*u^2) := by ring
end ExpertPush
