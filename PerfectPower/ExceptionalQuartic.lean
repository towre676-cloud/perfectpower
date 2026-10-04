import PerfectPower.ExceptionalPowerSearch
import PerfectPower.RungePower
namespace PerfectPower.ExceptionalQuartic
def value (x : ℤ) := x^4+x-100
def box : Finset ℤ := Finset.Icc (-10) 10

theorem outside_is_exceptional (x y : ℤ) (h : y^2=value x) (hx : x ∉ box) : x=100 := by
  by_contra he
  have hr : x-100 ≠ 0 := by omega
  have hi : y^2=(x^2)^2+(x-100) := by unfold value at h;nlinarith [h]
  have hg := RungePower.power_gap (x^2) y (x-100) 2 (by omega) hr hi
  have hb : |x-100| ≤ |x|+100 := by simpa using abs_sub_le x 0 100
  have ha : 11 ≤ |x| := by
    have hx' : ¬ (-10 ≤ x ∧ x ≤ 10) := by simpa only [box,Finset.mem_Icc] using hx
    have hm := neg_abs_le x
    have hp := le_abs_self x
    omega
  have hn := mul_nonneg (show 0 ≤ |x|-11 by omega) (show 0 ≤ |x|+10 by omega)
  simp only [Nat.reduceSub,pow_one,abs_of_nonneg (sq_nonneg x)] at hg
  have hs := sq_abs x
  nlinarith

def packet := ExceptionalPowerSearch.points value 2 box {100}
theorem complete (x y : ℤ) : y^2=value x ↔ (x,y) ∈ packet := by
  apply ExceptionalPowerSearch.complete value (fun x => x-100) 2 (by omega) box {100}
  · intro x;simp only [Finset.mem_singleton];omega
  · intro x y h hx
    have he := outside_is_exceptional x y h hx
    omega

theorem packet_checked : packet={(100,-10000),(100,10000)} := by decide +kernel

theorem solutions (x y : ℤ) : y^2=x^4+x-100 ↔
    (x=100 ∧ y= -10000) ∨ (x=100 ∧ y=10000) := by
  change y^2=value x ↔ _
  rw [complete,packet_checked]
  simp [Prod.mk.injEq]
end PerfectPower.ExceptionalQuartic
