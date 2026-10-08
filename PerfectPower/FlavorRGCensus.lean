import PerfectPower.FlavorRG

/-! Complete real classification of the literal four-operator scalar beta map.
The elimination is checked with rational polynomial identities and positivity,
without importing a computer-algebra transcript as a premise. -/
set_option maxHeartbeats 2000000

namespace PerfectPower.FlavorRG

private theorem secondary_branch_impossible (a c d h : ℝ) (hr : ScalarRay a c d h)
    (hb : 480*a+480*c+10*d-192*h-15=0) : False := by
  obtain ⟨ha,hc,_,hh⟩ := hr
  have hd : d=3/2-48*(a+c)+(96/5)*h := by linarith
  rw [hd] at ha hc hh
  have hs :
      (326656/175:ℝ)*((653312*a+616512*c-264976*h-19191)/653312)^2 +
      (216455/2233:ℝ)*((13853120*c-6094448*h-390353)/13853120)^2 +
      (314631857/30303700:ℝ)*((1258527428*h+26414795)/1258527428)^2 +
      (15920948593/2819101438720:ℝ)=0 := by
    linear_combination ha + (2/7:ℝ)*hc + (9/50:ℝ)*hh
  have hp : 0 <
      (326656/175:ℝ)*((653312*a+616512*c-264976*h-19191)/653312)^2 +
      (216455/2233:ℝ)*((13853120*c-6094448*h-390353)/13853120)^2 +
      (314631857/30303700:ℝ)*((1258527428*h+26414795)/1258527428)^2 +
      (15920948593/2819101438720:ℝ) := by positivity
  linarith

/-- Every real scalar ray cancels the independent alignment-force coefficient. -/
theorem scalar_ray_alignment (a c d h : ℝ) (hr : ScalarRay a c d h) : d=(6/5)*h := by
  have hcopy := hr
  obtain ⟨_,_,hd,hh⟩ := hcopy
  have hp : (5*d-6*h)*(480*a+480*c+10*d-192*h-15)=0 := by
    linear_combination 75*hd-90*hh
  rcases mul_eq_zero.mp hp with he | he
  · linarith
  · exact False.elim (secondary_branch_impossible a c d h hr he)

/-- All real solutions: the zero solution and exactly the five declared rays. -/
theorem scalar_ray_classification (a c d h : ℝ) (hr : ScalarRay a c d h) :
    (a=0 ∧ c=0 ∧ d=0 ∧ h=0) ∨
    (a=1/128 ∧ c=0 ∧ d=0 ∧ h=0) ∨
    (a=1/144 ∧ c= -1/144 ∧ d=0 ∧ h=0) ∨
    (a=1/192 ∧ c=1/96 ∧ d=0 ∧ h=0) ∨
    (a=1/256 ∧ c=5/512 ∧ d=3/160 ∧ h=1/64) ∨
    (a=1/576 ∧ c=7/1152 ∧ d=1/40 ∧ h=1/48) := by
  have hd := scalar_ray_alignment a c d h hr
  obtain ⟨ha,hc,_,hh⟩ := hr
  rw [hd] at ha hc hh
  by_cases hz : h=0
  · rw [hz] at ha hc
    have dz : d=0 := by rw [hz] at hd; linarith
    have cp : c*(160*a+16*c-1)=0 := by linear_combination hc
    rcases mul_eq_zero.mp cp with cz | ce
    · rw [cz] at ha
      have ap : a*(128*a-1)=0 := by linear_combination ha
      rcases mul_eq_zero.mp ap with az | ae
      · exact Or.inl ⟨az,cz,dz,hz⟩
      · exact Or.inr (Or.inl ⟨by linarith,cz,dz,hz⟩)
    · have cv : c=1/16-10*a := by linarith
      rw [cv] at ha
      have ap : (144*a-1)*(192*a-1)=0 := by linear_combination 16*ha
      rcases mul_eq_zero.mp ap with ae | ae
      · have av : a=1/144 := by linarith
        exact Or.inr (Or.inr (Or.inl ⟨av,by rw [av] at cv; linarith,dz,hz⟩))
      · have av : a=1/192 := by linarith
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨av,by rw [av] at cv; linarith,dz,hz⟩)))
  · have hp : h*(32*a+32*c+36*h-1)=0 := by linear_combination hh
    have he := (mul_eq_zero.mp hp).resolve_left hz
    have hv : h=(1-32*(a+c))/36 := by linarith
    rw [hv] at ha hc
    have hl : 96*(a+c)*a + ((32*(a+c)-1)*(1088*(a+c)-7))/864=0 := by
      linear_combination ha+hc
    have ep : (128*(a+c)-1)*(512*(a+c)-7)*
        (40960*(a+c)^2-640*(a+c)+7)=0 := by
      linear_combination (5184*(96*(a+c))^2)*ha -
        (5184*(144*(96*(a+c)*a-((32*(a+c)-1)*(1088*(a+c)-7))/864)+
          (-32*(a+c)-1)*96*(a+c)))*hl
    have qp : 0 < 40960*(a+c)^2-640*(a+c)+7 := by
      nlinarith [sq_nonneg (a+c-1/128)]
    have ep' := (mul_eq_zero.mp ep).resolve_right (ne_of_gt qp)
    rcases mul_eq_zero.mp ep' with es | es
    · have sv : a+c=1/128 := by linarith
      rw [sv] at hl hv
      have av : a=1/576 := by norm_num at hl; linarith
      have cv : c=7/1152 := by linarith
      have hh' : h=1/48 := by norm_num at hv; exact hv
      have dd : d=1/40 := by rw [hh'] at hd; norm_num at hd; exact hd
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨av,cv,dd,hh'⟩))))
    · have sv : a+c=7/512 := by linarith
      rw [sv] at hl hv
      have av : a=1/256 := by norm_num at hl; linarith
      have cv : c=5/512 := by linarith
      have hh' : h=1/64 := by norm_num at hv; exact hv
      have dd : d=3/160 := by rw [hh'] at hd; norm_num at hd; exact hd
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨av,cv,dd,hh'⟩))))

/-- The classification is an equivalence, including the zero solution. -/
theorem scalar_ray_iff (a c d h : ℝ) : ScalarRay a c d h ↔
    (a=0 ∧ c=0 ∧ d=0 ∧ h=0) ∨
    (a=1/128 ∧ c=0 ∧ d=0 ∧ h=0) ∨
    (a=1/144 ∧ c= -1/144 ∧ d=0 ∧ h=0) ∨
    (a=1/192 ∧ c=1/96 ∧ d=0 ∧ h=0) ∨
    (a=1/256 ∧ c=5/512 ∧ d=3/160 ∧ h=1/64) ∨
    (a=1/576 ∧ c=7/1152 ∧ d=1/40 ∧ h=1/48) := by
  constructor
  · exact scalar_ray_classification a c d h
  · intro hr
    rcases hr with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ |
      ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
    all_goals norm_num [ScalarRay]

/-- Exactly five nonzero real rays; no positivity assumption is required. -/
theorem scalar_ray_nonzero_iff (a c d h : ℝ) :
    (ScalarRay a c d h ∧ (a≠0 ∨ c≠0 ∨ d≠0 ∨ h≠0)) ↔
    (a=1/128 ∧ c=0 ∧ d=0 ∧ h=0) ∨
    (a=1/144 ∧ c= -1/144 ∧ d=0 ∧ h=0) ∨
    (a=1/192 ∧ c=1/96 ∧ d=0 ∧ h=0) ∨
    (a=1/256 ∧ c=5/512 ∧ d=3/160 ∧ h=1/64) ∨
    (a=1/576 ∧ c=7/1152 ∧ d=1/40 ∧ h=1/48) := by
  constructor
  · rintro ⟨hr,hn⟩
    rcases scalar_ray_classification a c d h hr with hz | hr
    · obtain ⟨rfl,rfl,rfl,rfl⟩ := hz
      simp at hn
    · exact hr
  · intro hr
    rcases hr with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ |
      ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
    all_goals norm_num [ScalarRay]

end PerfectPower.FlavorRG
