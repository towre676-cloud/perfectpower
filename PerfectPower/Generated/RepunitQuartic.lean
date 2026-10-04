import PerfectPower.Tactic.SquareLeadingQuartic
namespace PerfectPower.RepunitQuartic
native_square_leading_quartic points for 1, 1, 1, 1, 1

theorem inputs (x : ℤ) :
    (∃ y : ℤ, y^2=SquareLeadingQuartic.value 1 1 1 1 1 x) ↔
    x = -1 ∨ x = 0 ∨ x = 3 := by
  have hp : points = {(-1,-1),(-1,1),(0,-1),(0,1),(3,-11),(3,11)} := by decide +kernel
  simp_rw [points_complete,hp]
  simp [exists_or]

theorem positive (x : ℤ) (hx : 0 < x) :
    (∃ y : ℤ, y^2=SquareLeadingQuartic.value 1 1 1 1 1 x) ↔ x=3 := by
  rw [inputs]
  omega
end PerfectPower.RepunitQuartic
