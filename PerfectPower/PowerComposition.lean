import PerfectPower.NativePowerRoots

namespace PerfectPower.PowerComposition
/-- Lift a finite outer point set through an exact integer power coordinate. -/
def lift (outer : Finset (ℤ × ℤ)) (q : ℕ) : Finset (ℤ × ℤ) :=
  outer.biUnion fun p => (NativePowerRoots.roots q p.1).image fun x => (x,p.2)

theorem complete (F H : ℤ → ℤ) (outer : Finset (ℤ × ℤ)) (q d : ℕ) (hq : q ≠ 0)
    (hidentity : ∀ x, F x=H (x^q))
    (houter : ∀ u y, y^d=H u ↔ (u,y) ∈ outer) (x y : ℤ) :
    y^d=F x ↔ (x,y) ∈ lift outer q := by
  constructor
  · intro h
    apply Finset.mem_biUnion.mpr
    refine ⟨(x^q,y),(houter _ _).mp (by rw [← hidentity];exact h),?_⟩
    exact Finset.mem_image.mpr ⟨x,(NativePowerRoots.roots_complete q _ x hq).mp rfl,rfl⟩
  · intro h
    obtain ⟨⟨u,v⟩,hu,hv⟩ := Finset.mem_biUnion.mp h
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hv
    obtain ⟨hx,hy⟩ := Prod.mk.inj he
    change v=y at hy
    subst z;subst v
    have hp := (NativePowerRoots.roots_complete q u x hq).mpr hz
    rw [hidentity,hp]
    exact (houter u y).mpr hu

/-- Algebraic deweighting includes scale zero; the inverse chart does not. -/
theorem deweighting_zero (Q R : ℚ → ℚ → ℚ → ℚ)
    (h : ∀ w l z, Q (l^2*w) l z=l^12*R w l z) (w z : ℚ) : Q 0 0 z=0 := by
  simpa using h w 0 z

theorem deweighting_nonzero (Q R : ℚ → ℚ → ℚ → ℚ)
    (h : ∀ w l z, Q (l^2*w) l z=l^12*R w l z) (w l z : ℚ) (hl : l ≠ 0) :
    Q (l^2*w) l z=0 ↔ R w l z=0 := by rw [h,mul_eq_zero];simp [hl]

end PerfectPower.PowerComposition
