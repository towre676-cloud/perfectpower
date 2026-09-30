import Mathlib
/- Draft only: producing environment has no Lean executable.
Port to the repository's pinned toolchain; do not count as audited declarations. -/
namespace GaloisMerge

def cubic (c0 c1 c2 c3 x y : ℤ) : ℤ :=
  c0*x^3+c1*x^2*y+c2*x*y^2+c3*y^3

theorem determinant_one_inverse (a b c d x y : ℤ)
    (h : a*d-b*c=1) :
    d*(a*x+b*y)-b*(c*x+d*y)=x ∧
    -c*(a*x+b*y)+a*(c*x+d*y)=y := by
  constructor
  · linear_combination x*h
  · linear_combination y*h

/-- Transport a complete list through a bijection; restrictions belong in P. -/
theorem complete_transport {α β : Type*} (P : α → Prop) (Q : β → Prop)
    (f : β → α) (g : α → β)
    (left : ∀ x, f (g x)=x)
    (compat : ∀ y, Q y ↔ P (f y))
    (L : Set β) (complete : ∀ y, Q y ↔ y ∈ L) :
    ∀ x, P x ↔ x ∈ f '' L := by
  intro x
  constructor
  · intro hx
    refine ⟨g x, ?_, left x⟩
    apply (complete (g x)).mp
    apply (compat (g x)).mpr
    simpa only [left x] using hx
  · rintro ⟨y, hy, rfl⟩
    exact (compat y).mp ((complete y).mpr hy)
end GaloisMerge
