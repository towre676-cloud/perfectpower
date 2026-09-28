import PerfectPower.Estimates

open Polynomial Filter Topology
open scoped Classical

namespace PerfectPower

/-- Rigid dichotomy: exact polynomial root identity, or only finitely many hits. -/
theorem rigid_dichotomy {d : ℕ} (hd : 2 ≤ d) {F : ℤ[X]} (hF : IsRigid d F) (hF0 : F ≠ 0) :
    (∃ G : ℤ[X], F = G ^ d) ∨ (hitSet (fun n => F.eval (n : ℤ)) d 0).Finite := by
  obtain ⟨Q, hQd, hQdeg⟩ := exists_truncated_root hd hF hF0
  by_cases hEq : F.map (Int.castRingHom ℚ) = Q ^ d
  · left
    obtain ⟨G, hG⟩ := integral_closure_step hd F Q hEq.symm
    refine ⟨G, ?_⟩
    apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [Polynomial.map_pow, hG, hEq]
  · right
    have hev := eventually_no_hit hd hQdeg hEq
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine (Set.finite_Iio N).subset ?_
    intro n hn
    by_contra hlt
    have hle : N ≤ n := not_lt.mp (by simpa using hlt)
    exact hN n hle (by simpa using hn.2)

end PerfectPower
