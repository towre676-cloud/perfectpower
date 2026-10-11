import PerfectPower.EuclidMethods

/-! Std-only complete finite charts for nonzero difference-of-squares constants.
The executable chart deliberately uses a simple bounded divisor enumeration;
Python can submit its faster list for equality checking by the kernel. -/
namespace PerfectPower.LinearProductChart

def divisors (k : Int) : List Int :=
  ((List.range (2*k.natAbs+1)).map fun (i : Nat) => (i : Int)-(k.natAbs : Int)).filter
    fun u => u != 0 && k % u == 0

theorem divisor_mem (k u : Int) (hk : k ≠ 0) :
    u ∈ divisors k ↔ u ∣ k := by
  constructor
  · intro h
    obtain ⟨_, h⟩ := List.mem_filter.mp h
    have hm : k % u = 0 := by simpa using (Bool.and_eq_true_iff.mp h).2
    exact Int.dvd_of_emod_eq_zero hm
  · intro h
    have hn : u ≠ 0 := by intro hz; subst u; simp at h; exact hk h
    have hb : u.natAbs ≤ k.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hk) (Int.natAbs_dvd_natAbs.mpr h)
    have hp := Int.le_natAbs (a := u)
    have hm := Int.le_natAbs (a := -u)
    simp only [Int.natAbs_neg] at hm
    apply List.mem_filter.mpr
    refine ⟨?_, by simp [hn, Int.emod_eq_zero_of_dvd h]⟩
    apply List.mem_map.mpr
    refine ⟨(u+(k.natAbs : Int)).toNat, List.mem_range.mpr ?_, ?_⟩
    · omega
    · omega

def pairs (k : Int) : List (Int × Int) := (divisors k).map fun u => (u,k/u)

theorem pair_mem (k u v : Int) (hk : k ≠ 0) :
    (u,v) ∈ pairs k ↔ u*v=k := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := List.mem_map.mp h
    have hu : w=u := congrArg Prod.fst he
    have hv : k/w=v := congrArg Prod.snd he
    subst w
    rw [← hv]
    exact Int.mul_ediv_cancel' ((divisor_mem k u hk).mp hw)
  · intro h
    have hn : u ≠ 0 := by intro hz; rw [hz, Int.zero_mul] at h; exact hk h.symm
    apply List.mem_map.mpr
    refine ⟨u, (divisor_mem k u hk).mpr ⟨v,h.symm⟩, ?_⟩
    apply Prod.ext
    · rfl
    · simp only [Prod.snd]
      rw [← h]
      exact Int.mul_ediv_cancel_left v hn

theorem difference_squares (x z : Int) : (x-z)*(x+z)=x*x-z*z := by
  simp only [Int.sub_mul, Int.mul_add]
  rw [Int.mul_comm z x]
  omega

def recover (q t s : Int) (uv : Int × Int) : Int × Int :=
  ((uv.1+uv.2-2*t)/(4*q),(uv.2-uv.1)/(4*s))

def integralPair (q t s : Int) (uv : Int × Int) : Bool :=
  (uv.1+uv.2-2*t) % (4*q) == 0 && (uv.2-uv.1) % (4*s) == 0

theorem integral_image (q t s n y : Int) :
    integralPair q t s (2*q*n+t-2*s*y,2*q*n+t+2*s*y) = true := by
  have hn : (2*q*n+t-2*s*y)+(2*q*n+t+2*s*y)-2*t=(4*q)*n := by
    simp only [Int.mul_assoc, ← Int.add_mul]; omega
  have hy : (2*q*n+t+2*s*y)-(2*q*n+t-2*s*y)=(4*s)*y := by
    simp only [Int.mul_assoc, ← Int.add_mul]; omega
  simp only [integralPair, Prod.fst, Prod.snd, hn, hy]
  simp

theorem recover_image (q t s n y : Int) (hq : q ≠ 0) (hs : s ≠ 0) :
    recover q t s (2*q*n+t-2*s*y,2*q*n+t+2*s*y)=(n,y) := by
  unfold recover
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd]
  · have he : (2*q*n+t-2*s*y)+(2*q*n+t+2*s*y)-2*t=(4*q)*n := by
      simp only [Int.mul_assoc, ← Int.add_mul]; omega
    rw [he]
    exact Int.mul_ediv_cancel_left n (Int.mul_ne_zero (by decide) hq)
  · have he : (2*q*n+t+2*s*y)-(2*q*n+t-2*s*y)=(4*s)*y := by
      simp only [Int.mul_assoc, ← Int.add_mul]; omega
    rw [he]
    exact Int.mul_ediv_cancel_left y (Int.mul_ne_zero (by decide) hs)

/-- Source-specific polynomial identity supplies only this explicit premise. -/
def points (F : Int → Int) (q t s k : Int) : List (Int × Int) :=
  (((pairs k).filter (integralPair q t s)).map (recover q t s)).filter fun p => p.2*p.2 == F p.1

theorem complete (F : Int → Int) (q t s k : Int)
    (hq : q ≠ 0) (hs : s ≠ 0) (hk : k ≠ 0)
    (identity : ∀ n, (2*q*n+t)*(2*q*n+t)-(2*s)*(2*s)*F n=k)
    (n y : Int) : y*y=F n ↔ (n,y) ∈ points F q t s k := by
  constructor
  · intro h
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa using h⟩
    apply List.mem_map.mpr
    refine ⟨(2*q*n+t-2*s*y,2*q*n+t+2*s*y), ?_, recover_image q t s n y hq hs⟩
    apply List.mem_filter.mpr
    refine ⟨?_, integral_image q t s n y⟩
    apply (pair_mem k _ _ hk).mpr
    rw [difference_squares]
    have hy : (2*s*y)*(2*s*y)=(2*s)*(2*s)*(y*y) := by
      simp only [Int.mul_assoc, Int.mul_left_comm]
    rw [hy, h]
    exact identity n
  · intro h
    simpa using (List.mem_filter.mp h).2

#print axioms divisor_mem
#print axioms pair_mem
#print axioms recover_image
#print axioms complete
end PerfectPower.LinearProductChart
