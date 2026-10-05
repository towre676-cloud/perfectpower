import PerfectPower.SemilinearCapacity
import PerfectPower.NativePowerRoots

namespace PerfectPower.SemilinearPowerSearch

/-- Complete finite search driven by the sign domain, rather than a height guess. -/
def solutions (F : ℤ → ℤ) (d : ℕ) (X : Finset ℤ) : Finset (ℤ × ℤ) :=
  X.biUnion (fun x => (PerfectPower.NativePowerRoots.roots d (F x)).image (fun y => (x,y)))

/-- Any certified finite nonnegative domain closes every positive even exponent. -/
theorem complete (F : ℤ → ℤ) (d : ℕ) (hd : d ≠ 0) (heven : Even d)
    (X : Finset ℤ) (sign_domain : ∀ x, 0 ≤ F x ↔ x ∈ X) (x y : ℤ) :
    y ^ d = F x ↔ (x,y) ∈ solutions F d X := by
  simp only [solutions, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · intro h
    have hn : 0 ≤ F x := by rw [← h]; exact heven.pow_nonneg y
    exact ⟨x,(sign_domain x).mp hn,y,
      (PerfectPower.NativePowerRoots.roots_complete d (F x) y hd).mp h,rfl⟩
  · rintro ⟨u,_,v,hv,he⟩
    have hx : u = x := congrArg Prod.fst he
    have hy : v = y := congrArg Prod.snd he
    subst u; subst v
    exact (PerfectPower.NativePowerRoots.roots_complete d (F x) y hd).mpr hv

/-- The negative-leading quartic has exactly three possible input coordinates. -/
theorem negative_quartic_domain (x : ℤ) :
    0 ≤ 3 - 2 * x ^ 4 ↔ x ∈ ({-1,0,1} : Finset ℤ) := by
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    by_contra hc
    have hg : x ≤ -2 ∨ 2 ≤ x := by omega
    have hs : 4 ≤ x ^ 2 := by rcases hg with h | h <;> nlinarith
    nlinarith [sq_nonneg (x ^ 2 - 4)]
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- A complete literal output, with every original signed root retained. -/
theorem negative_quartic_packet :
    solutions (fun x => 3 - 2 * x ^ 4) 2 {-1,0,1} =
      {(-1,-1),(-1,1),(1,-1),(1,1)} := by decide +kernel

theorem negative_quartic_complete (x y : ℤ) :
    y ^ 2 = 3 - 2 * x ^ 4 ↔
      (x,y) ∈ ({(-1,-1),(-1,1),(1,-1),(1,1)} : Finset (ℤ × ℤ)) := by
  rw [← negative_quartic_packet]
  exact complete _ 2 (by norm_num) (by decide) _ negative_quartic_domain x y

end PerfectPower.SemilinearPowerSearch
