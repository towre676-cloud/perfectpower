import Mathlib
namespace PerfectPower.BoundedReconstruction

/-- Equal modular fractions within the strict reconstruction bound are equal.
No existence or correctness of an external reconstruction algorithm is assumed. -/
theorem unique (M A B r a b c d : ℤ) (hM : 2*A*B < M)
    (hA : 0 ≤ A)
    (ha : |a| ≤ A) (hc : |c| ≤ A) (hb : 0 < b) (hd : 0 < d)
    (hbB : b ≤ B) (hdB : d ≤ B)
    (hab : M ∣ a-r*b) (hcd : M ∣ c-r*d) :
    (a : ℚ)/b = (c : ℚ)/d := by
  have hv : M ∣ a*d-c*b := by
    obtain ⟨u,hu⟩ := hab
    obtain ⟨v,hv⟩ := hcd
    refine ⟨u*d-v*b, ?_⟩
    nlinarith [hu,hv]
  have hbound : |a*d-c*b| ≤ 2*A*B := by
    calc
      |a*d-c*b| ≤ |a*d|+|c*b| := abs_sub _ _
      _ = |a| * d + |c| * b := by rw [abs_mul,abs_mul,abs_of_pos hd,abs_of_pos hb]
      _ ≤ A*B+A*B := by gcongr
      _ = 2*A*B := by ring
  have hz : a*d-c*b=0 := by
    by_contra hn
    have hle := Int.le_of_dvd (abs_pos.mpr hn) (show M ∣ |a*d-c*b| from (dvd_abs M _).mpr hv)
    omega
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  field_simp
  exact_mod_cast (sub_eq_zero.mp hz)
end PerfectPower.BoundedReconstruction
