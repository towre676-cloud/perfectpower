import PerfectPower.PowerComposition
namespace PerfectPower.AffinePowerComposition

/-- Keep both integral image restrictions when lifting a scaled affine power coordinate. -/
def lift (outer : Finset (ℤ × ℤ)) (q : ℕ) (a b s : ℤ) : Finset (ℤ × ℤ) :=
  outer.biUnion fun p => ((NativePowerRoots.roots q p.1).filter
    (fun t => a ∣ t-b ∧ s ∣ p.2)).image fun t => ((t-b)/a,p.2/s)

theorem complete (F H : ℤ → ℤ) (outer : Finset (ℤ × ℤ))
    (q d : ℕ) (a b s : ℤ) (hq : q ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0)
    (hidentity : ∀ x, s^d*F x=H ((a*x+b)^q))
    (houter : ∀ u v,v^d=H u ↔ (u,v) ∈ outer) (x y : ℤ) :
    y^d=F x ↔ (x,y) ∈ lift outer q a b s := by
  constructor
  · intro h
    have hp : (s*y)^d=H ((a*x+b)^q) := by rw [mul_pow,h,hidentity]
    apply Finset.mem_biUnion.mpr
    refine ⟨((a*x+b)^q,s*y),(houter _ _).mp hp,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨a*x+b,Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
    · exact (NativePowerRoots.roots_complete q _ _ hq).mp rfl
    · constructor
      · exact ⟨x,by ring⟩
      · exact ⟨y,rfl⟩
    · simp only [add_sub_cancel_right,Int.mul_ediv_cancel_left _ ha,Int.mul_ediv_cancel_left _ hs]
  · intro h
    obtain ⟨⟨u,v⟩,hp,ht⟩ := Finset.mem_biUnion.mp h
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp ht
    obtain ⟨hr,had,hsv⟩ := Finset.mem_filter.mp ht
    have htq : t^q=u := (NativePowerRoots.roots_complete q _ _ hq).mpr hr
    have hxy : ((t-b)/a,v/s)=(x,y) := he
    have hx := congrArg Prod.fst hxy
    have hy := congrArg Prod.snd hxy
    have hat : a*x+b=t := by
      change (t-b)/a=x at hx
      rw [← hx,Int.mul_ediv_cancel' had]
      ring
    have hsv' : s*y=v := by
      change v/s=y at hy
      rw [← hy,Int.mul_ediv_cancel' hsv]
    have hv := (houter u v).mpr hp
    rw [← htq,← hat,← hsv',mul_pow,← hidentity] at hv
    exact mul_left_cancel₀ (pow_ne_zero d hs) hv

end PerfectPower.AffinePowerComposition
