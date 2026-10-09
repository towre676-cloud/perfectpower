import PerfectPower.PellOrbitPopulation
import PerfectPower.IntegerPolynomialFibres

namespace PerfectPower.AutomaticReduction

/-- Invert an affine coordinate and swap axes while retaining its divisibility condition. -/
def affinePullback (S : Finset (ℤ × ℤ)) (a b : ℤ) : Finset (ℤ × ℤ) :=
  (S.filter fun q => a ∣ q.2-b).image fun q => ((q.2-b)/a,q.1)

theorem affinePullback_complete (S : Finset (ℤ × ℤ)) (a b : ℤ) (ha : a ≠ 0)
    (p : ℤ × ℤ) : p ∈ affinePullback S a b ↔ (p.2,a*p.1+b) ∈ S := by
  simp only [affinePullback,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨q,⟨hq,hd⟩,he⟩
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only [Prod.fst,Prod.snd] at h1 h2
    have hm := Int.mul_ediv_cancel' hd
    have hqeq : q=(p.2,a*p.1+b) := by
      ext
      · exact h2
      · rw [h1] at hm
        change q.2=a*p.1+b
        linarith
    simpa only [hqeq] using hq
  · intro h
    refine ⟨(p.2,a*p.1+b),⟨h,by exact ⟨p.1,by ring⟩⟩,?_⟩
    ext
    · simp only [Prod.fst,Prod.snd,add_sub_cancel_right]
      rw [Int.mul_ediv_cancel_left _ ha]
    · rfl

theorem quadratic_norm (a b c x y : ℤ) (ha : a ≠ 0) :
    y^2=a*x^2+b*x+c ↔ (2*a*x+b)^2-4*a*y^2=b^2-4*a*c := by
  constructor
  · intro h; linear_combination -(4*a)*h
  · intro h
    have he : (4*a)*(y^2-(a*x^2+b*x+c))=0 := by linear_combination -h
    have hc : (4*a) ≠ 0 := mul_ne_zero (by norm_num) ha
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hc)

def outputPullback (S : Finset (ℤ × ℤ)) (a : ℤ) : Finset (ℤ × ℤ) :=
  (S.filter fun q => a ∣ q.2).image fun q => (q.1,q.2/a)

theorem outputPullback_complete (S : Finset (ℤ × ℤ)) (a : ℤ) (ha : a ≠ 0)
    (p : ℤ × ℤ) : p ∈ outputPullback S a ↔ (p.1,a*p.2) ∈ S := by
  simp only [outputPullback,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨q,⟨hq,hd⟩,he⟩
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only [Prod.fst,Prod.snd] at h1 h2
    have hm := Int.mul_ediv_cancel' hd
    have hqeq : q=(p.1,a*p.2) := by
      ext
      · exact h1
      · rw [h2] at hm
        exact hm.symm
    simpa only [hqeq] using hq
  · intro h
    refine ⟨(p.1,a*p.2),⟨h,⟨p.2,rfl⟩⟩,?_⟩
    ext
    · rfl
    · simp only [Prod.fst,Prod.snd]
      rw [Int.mul_ediv_cancel_left _ ha]

/-- The root cutoff is derived from the original input cutoff, including both signs. -/
theorem quadratic_root_bound (a b c T cap x y : ℤ) (ha : 0<a) (hT : 0≤T)
    (hcap : 0≤cap) (hgap : a*T^2+|b| *T+|c| < (cap+1)^2)
    (hx : |x|≤T) (hy : y^2=a*x^2+b*x+c) : |y|≤cap := by
  have hx0 := abs_nonneg x
  have hx2 : x^2≤T^2 := by nlinarith [sq_abs x]
  have hm := mul_le_mul_of_nonneg_left hx2 ha.le
  have hb := abs_mul b x
  have hb2 := mul_le_mul_of_nonneg_left hx (abs_nonneg b)
  have hv : b*x≤|b| *T := (le_abs_self (b*x)).trans (by simpa only [hb] using hb2)
  by_contra hn
  have hh : cap+1≤|y| := by omega
  nlinarith [sq_abs y,le_abs_self c]

end PerfectPower.AutomaticReduction
