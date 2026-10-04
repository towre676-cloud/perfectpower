import PerfectPower.NativePowerRoots
import PerfectPower.RungePolynomial

/-! Effective Runge bounds for all integer exponents d ≥ 2, with checked
polynomial completions and binary root fibres on the original equation. -/
namespace PerfectPower.RungePower
/-- A gap between nonnegative integer powers controls the larger base. -/
lemma nonneg_gap (u v : ℤ) (hu : 0 ≤ u) (hv : u+1 ≤ v) (d : ℕ) (hd : 1 ≤ d) :
    v^(d-1) ≤ v^d-u^d := by
  induction d, hd using Nat.le_induction with
  | base => simp; omega
  | succ d hd ih =>
    have hp := pow_nonneg hu d
    have hm := mul_le_mul_of_nonneg_left ih (show 0 ≤ v by omega)
    have hn : 0 ≤ (v-u)*u^d := mul_nonneg (by omega) hp
    have hid : d-1+1=d := by omega
    rw [← pow_succ', hid] at hm
    simp only [Nat.add_sub_cancel, pow_succ]
    nlinarith
/-- Distinct integer d-th powers have a gap at least the (d-1)-st power
of either base, including opposite signs and even exponents. -/
theorem power_gap (p y k : ℤ) (d : ℕ) (hd : 2 ≤ d) (hk : k ≠ 0)
    (h : y^d=p^d+k) : |p|^(d-1) ≤ |k| := by
  by_cases hp : p=0
  · simp [hp, zero_pow (show d-1 ≠ 0 by omega)]
  have hp1 : 1 ≤ |p| := by have := abs_pos.mpr hp; omega
  by_cases he : |y|=|p|
  · rcases abs_eq_abs.mp he with hy | hy
    · rw [hy] at h; omega
    · rcases Nat.even_or_odd d with hv | hv
      · rw [hy,hv.neg_pow] at h; omega
      · rw [hy,hv.neg_pow] at h
        have hk2 : k= -2*p^d := by omega
        rw [hk2,abs_mul,abs_pow]
        have hm := pow_le_pow_right₀ hp1 (show d-1 ≤ d by omega)
        have hp0 := pow_nonneg (abs_nonneg p) d
        norm_num
        omega
  · have ht := abs_abs_sub_abs_le_abs_sub (y^d) (p^d)
    rw [abs_pow,abs_pow,show y^d-p^d=k by omega] at ht
    rcases lt_or_gt_of_ne he with hl | hl
    · have hg := nonneg_gap |y| |p| (abs_nonneg y) (by omega) d (by omega)
      have hb := le_abs_self (|p|^d-|y|^d)
      rw [abs_sub_comm] at hb
      omega
    · have hg := nonneg_gap |p| |y| (abs_nonneg p) (by omega) d (by omega)
      have hm := pow_le_pow_left₀ (abs_nonneg p) hl.le (d-1)
      have hb := le_abs_self (|y|^d-|p|^d)
      omega
open NativePolynomialSquare

/-- Unconditional coordinate bound from a checked d-th-power completion.
The polynomial P represents Q^(d-1), so it dominates the residual. -/
theorem coordinate_bound (F q P r : List ℤ) (a : ℤ) (d : ℕ) (hd : 2 ≤ d)
    (hP : valid P) (hr : valid r) (hdegree : r.length < P.length)
    (hpower : ∀ x : ℤ, eval P x=(eval q x)^(d-1))
    (hidentity : ∀ x : ℤ, a^d*eval F x=(eval q x)^d+eval r x)
    (x y : ℤ) (h : y^d=eval F x) : |x| ≤ RungePolynomial.bound P r := by
  have hs : (a*y)^d=(eval q x)^d+eval r x := by
    rw [← hidentity,← h,mul_pow]
  by_contra hn
  have hlarge : height P+height r+1 ≤ |x| := by unfold RungePolynomial.bound at hn; omega
  by_cases hz : eval r x=0
  · have hl : ([] : List ℤ).length < r.length := by
      cases r with
      | nil => exact False.elim hr
      | cons b bs => simp
    have hh := height_nonneg P
    have ht := RungePolynomial.degree_domination r [] x hr hl (by simp [height]; omega)
    simp [eval,hz] at ht
  · have hg := power_gap (eval q x) (a*y) (eval r x) d hd hz hs
    have ht := RungePolynomial.degree_domination P r x hP hdegree hlarge
    rw [hpower,abs_pow] at ht
    omega

/-- Finite fibres use the proved binary root algorithm and the original equation. -/
def points (F P r : List ℤ) (d : ℕ) : Finset (ℤ × ℤ) :=
  (RungePolynomial.coordinates P r).biUnion fun x =>
    (NativePowerRoots.roots d (eval F x)).image fun y => (x,y)

theorem complete (F q P r : List ℤ) (a : ℤ) (d : ℕ) (hd : 2 ≤ d)
    (hP : valid P) (hr : valid r) (hdegree : r.length < P.length)
    (hpower : ∀ x : ℤ, eval P x=(eval q x)^(d-1))
    (hidentity : ∀ x : ℤ, a^d*eval F x=(eval q x)^d+eval r x) (x y : ℤ) :
    y^d=eval F x ↔ (x,y) ∈ points F P r d := by
  constructor
  · intro h
    have hb := coordinate_bound F q P r a d hd hP hr hdegree hpower hidentity x y h
    apply Finset.mem_biUnion.mpr
    refine ⟨x,Finset.mem_union_left _ (Finset.mem_Icc.mpr (abs_le.mp hb)),?_⟩
    exact Finset.mem_image.mpr ⟨y,(NativePowerRoots.roots_complete d _ y (by omega)).mp h,rfl⟩
  · intro h
    obtain ⟨u,_,hu⟩ := Finset.mem_biUnion.mp h
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hu
    obtain ⟨hx,hy⟩ := Prod.mk.inj he
    subst u; subst v
    exact (NativePowerRoots.roots_complete d _ y (by omega)).mpr hv

/-- Exact powers retain the negative branch precisely for even exponents. -/
theorem power_family (F q : List ℤ) (a : ℤ) (d : ℕ) (hd : 2 ≤ d) (ha : a ≠ 0)
    (hidentity : ∀ x : ℤ, a^d*eval F x=(eval q x)^d) (x y : ℤ) :
    y^d=eval F x ↔ a*y=eval q x ∨ a*y= -eval q x ∧ Even d := by
  rw [← pow_eq_pow_iff_of_ne_zero (show d ≠ 0 by omega)]
  constructor
  · intro h; rw [mul_pow,h,hidentity]
  · intro h
    apply mul_left_cancel₀ (pow_ne_zero d ha)
    rw [← mul_pow,h,hidentity]

end PerfectPower.RungePower
