import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Finite residue certificates exclude primitive integral quartic points.
Solubility in a finite quotient alone makes no assertion about a p-adic point. -/
namespace PerfectPower.LocalQuarticObstruction

def obstructed (p : ℕ) [NeZero p] (d A c : ℤ) : Prop :=
  ∀ x e z : ZMod p, x ≠ 0 ∨ e ≠ 0 →
    z^2 ≠ (d : ZMod p)*x^4 + (A : ZMod p)*x^2*e^2 + (c : ZMod p)*e^4

instance (p : ℕ) [NeZero p] (d A c : ℤ) : Decidable (obstructed p d A c) :=
  inferInstanceAs (Decidable (∀ x e z : ZMod p, x ≠ 0 ∨ e ≠ 0 →
    z^2 ≠ (d : ZMod p)*x^4 + (A : ZMod p)*x^2*e^2 + (c : ZMod p)*e^4))

theorem no_primitive_point (p : ℕ) [NeZero p] (d A c : ℤ)
    (cert : obstructed p d A c) (x e z : ℤ)
    (primitive : (x : ZMod p) ≠ 0 ∨ (e : ZMod p) ≠ 0) :
    z^2 ≠ d*x^4 + A*x^2*e^2 + c*e^4 := by
  intro h
  apply cert (x : ZMod p) (e : ZMod p) (z : ZMod p) primitive
  have hc := congr_arg (fun n : ℤ => (n : ZMod p)) h
  simpa only [Int.cast_pow, Int.cast_add, Int.cast_mul] using hc

theorem no_point_of_not_dvd (p : ℕ) [NeZero p] (d A c : ℤ)
    (cert : obstructed p d A c) (x e z : ℤ)
    (primitive : ¬ (p : ℤ) ∣ x ∨ ¬ (p : ℤ) ∣ e) :
    z^2 ≠ d*x^4 + A*x^2*e^2 + c*e^4 := by
  apply no_primitive_point p d A c cert x e z
  rcases primitive with hx | he
  · exact Or.inl (fun h => hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h))
  · exact Or.inr (fun h => he ((ZMod.intCast_zmod_eq_zero_iff_dvd e p).mp h))

end PerfectPower.LocalQuarticObstruction
