import PerfectPower.MordellDescentCore

namespace PerfectPower.MordellDescentMask

def squareCheck (M : ℕ) (mask : List ℤ) : Bool :=
  (List.range M).all fun y => decide (((y:ℤ)^2 % M) ∈ mask)

def congrCheck (D c b : ℤ) (M : ℕ) (mask : List ℤ) : Bool :=
  (List.range M).all fun x => decide
    (((x:ℤ)^3+c^3-D*b^2)%M ∈ mask →
      ((x:ℤ)^2-c*x+c^2)%2=1 ∧
      ¬ PerfectPower.MordellDescent.good D ((((x:ℤ)^2-c*x+c^2)%8).toNat))

theorem congr_ok (D c b : ℤ) (M : ℕ) (mask : List ℤ)
    (hs : squareCheck M mask = true) (hc : congrCheck D c b M mask = true) :
    PerfectPower.MordellDescent.CongOK D c b M := by
  intro X hX Y hY he
  have hy := of_decide_eq_true (List.all_eq_true.mp hs Y (List.mem_range.mpr hY))
  have hx := of_decide_eq_true (List.all_eq_true.mp hc X (List.mem_range.mpr hX))
  apply hx
  have hv : ((Y:ℤ)^2 % M) = (((X:ℤ)^3+c^3-D*b^2)%M) := by
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    convert he using 1
    ring
  rw [← hv]
  exact hy

def mask8 : List ℤ := [0,1,4]
def mask32 : List ℤ := [0,1,4,9,16,17,25]
def mask64 : List ℤ := [0,1,4,9,16,17,25,33,36,41,49,57]
theorem square8 : squareCheck 8 mask8 = true := by decide +kernel
theorem square32 : squareCheck 32 mask32 = true := by decide +kernel
theorem square64 : squareCheck 64 mask64 = true := by decide +kernel

end PerfectPower.MordellDescentMask
