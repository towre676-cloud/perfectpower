import PerfectPower.NativePowerRoots
namespace PerfectPower.ExceptionalPowerSearch
/-- Exceptional residual roots are included even when outside the search interval. -/
def points (F : ℤ → ℤ) (d : ℕ) (box exceptions : Finset ℤ) : Finset (ℤ × ℤ) :=
  (box ∪ exceptions).biUnion fun x => (NativePowerRoots.roots d (F x)).image fun y => (x,y)

theorem complete (F R : ℤ → ℤ) (d : ℕ) (hd : d ≠ 0) (box exceptions : Finset ℤ)
    (hex : ∀ x,R x=0 ↔ x ∈ exceptions)
    (htail : ∀ x y,y^d=F x → x ∉ box → R x=0) (x y : ℤ) :
    y^d=F x ↔ (x,y) ∈ points F d box exceptions := by
  constructor
  · intro h
    have hx : x ∈ box ∪ exceptions := by
      by_cases hb : x ∈ box
      · exact Finset.mem_union_left _ hb
      · exact Finset.mem_union_right _ ((hex x).mp (htail x y h hb))
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr
      ⟨y,(NativePowerRoots.roots_complete d _ y hd).mp h,rfl⟩⟩
  · intro h
    obtain ⟨u,_,hu⟩ := Finset.mem_biUnion.mp h
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hu
    obtain ⟨hx,hy⟩ := Prod.mk.inj he
    subst u;subst v
    exact (NativePowerRoots.roots_complete d _ y hd).mpr hv

/-- The final integer gap step for a rational completion. -/
theorem integer_gap (D z p : ℤ) (h : |D*z-p| < 1) : D*z=p := by
  have hh := abs_lt.mp h
  omega

/-- Exact isolated integer roots for the widely separated polynomial. -/
theorem separated_roots (A x : ℤ) : (x-1)*(x-A)=0 ↔ x=1 ∨ x=A := by
  rw [mul_eq_zero,sub_eq_zero,sub_eq_zero]

/-- The square-plus-one route retains both distant fibres and both witnesses. -/
theorem square_plus_one (p y : ℤ) : y^2=p^2+1 ↔ p=0 ∧ (y=1 ∨ y= -1) := by
  constructor
  · intro h
    have hp : 0 ≤ |p| := abs_nonneg p
    have hy : 0 ≤ |y| := abs_nonneg y
    have hs : |y|^2=|p|^2+1 := by simpa only [sq_abs] using h
    have he : |y|=|p|+1 ∨ |y| ≤ |p| ∨ |p|+2 ≤ |y| := by omega
    rcases he with he | he | he
    · have hp0 : |p|=0 := by nlinarith
      have py : p=0 := abs_eq_zero.mp hp0
      refine ⟨py,?_⟩
      rw [py] at h
      have hz : (y-1)*(y+1)=0 := by nlinarith
      rcases mul_eq_zero.mp hz with hz | hz
      · left;omega
      · right;omega
    · nlinarith
    · nlinarith
  · rintro ⟨rfl,(rfl|rfl)⟩ <;> norm_num

theorem distant_complete (A x y : ℤ) :
    y^2=((x-1)*(x-A))^2+1 ↔ (x=1 ∨ x=A) ∧ (y=1 ∨ y= -1) := by
  rw [square_plus_one,separated_roots]
end PerfectPower.ExceptionalPowerSearch
