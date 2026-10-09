import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Floor

/-! The sufficient direction of Landau's criterion, from an exact rational
floor-step certificate to divisibility of original factorial products. -/
namespace PerfectPower.LandauIntegral
open scoped BigOperators

/-- Product of the original factorials indexed by a finite slope list. -/
def factorialProduct (cs : List ℕ) (n : ℕ) : ℕ :=
  (cs.map fun c => (c*n).factorial).prod
/-- Sum of the natural quotients used in one Legendre layer. -/
def floorAt (cs : List ℕ) (n q : ℕ) : ℕ :=
  (cs.map fun c => c*n/q).sum
/-- Sum of prime valuations of the individual factorials. -/
def exponent (cs : List ℕ) (n p : ℕ) : ℕ :=
  (cs.map fun c => padicValNat p (c*n).factorial).sum
/-- Exact integer floor sum evaluated at a rational argument. -/
def floorSum (cs : List ℕ) (x : ℚ) : ℤ :=
  (cs.map fun (c : ℕ) => ⌊(c : ℚ)*x⌋).sum
/-- Signed floor step of a factorial ratio. -/
def delta (a b : List ℕ) (x : ℚ) : ℤ := floorSum a x - floorSum b x

theorem product_ne_zero (cs : List ℕ) (n : ℕ) : factorialProduct cs n ≠ 0 := by
  induction cs with
  | nil => simp [factorialProduct]
  | cons c cs ih => simpa [factorialProduct] using mul_ne_zero (Nat.factorial_ne_zero (c*n)) ih

theorem product_factorization (cs : List ℕ) (n p : ℕ) (hp : p.Prime) :
    (factorialProduct cs n).factorization p = exponent cs n p := by
  induction cs with
  | nil => simp [factorialProduct, exponent]
  | cons c cs ih =>
    have he : factorialProduct (c::cs) n = (c*n).factorial * factorialProduct cs n := by
      simp [factorialProduct]
    rw [he, Nat.factorization_mul (Nat.factorial_ne_zero _) (product_ne_zero cs n)]
    simp only [Finsupp.add_apply, Nat.factorization_def (c*n).factorial hp]
    simpa only [exponent, List.map_cons, List.sum_cons] using
      congrArg (Nat.add (padicValNat p (c*n).factorial)) ih

theorem exponent_sum (cs : List ℕ) (n p B : ℕ) (hp : p.Prime)
    (hb : ∀ c ∈ cs, Nat.log p (c*n) < B) :
    exponent cs n p = ∑ i ∈ Finset.Ico 1 B, floorAt cs n (p^i) := by
  letI : Fact p.Prime := ⟨hp⟩
  induction cs with
  | nil => simp [exponent, floorAt]
  | cons c cs ih =>
    change padicValNat p (c*n).factorial + exponent cs n p = _
    rw [padicValNat_factorial (hb c (by simp)), ih (by
      intro d hd
      exact hb d (by simp [hd]))]
    simp only [floorAt, List.map_cons, List.sum_cons, Finset.sum_add_distrib]

theorem member_le_sum (cs : List ℕ) (c : ℕ) (hc : c ∈ cs) : c ≤ cs.sum := by
  induction cs with
  | nil => simp at hc
  | cons d cs ih =>
    simp only [List.mem_cons] at hc
    simp only [List.sum_cons]
    rcases hc with rfl | hc
    · omega
    · have := ih hc
      omega

theorem integral_of_division_steps (a b : List ℕ)
    (steps : ∀ n q, floorAt b n q ≤ floorAt a n q) (n : ℕ) :
    factorialProduct b n ∣ factorialProduct a n := by
  apply (Nat.factorization_le_iff_dvd (product_ne_zero b n) (product_ne_zero a n)).mp
  intro p
  by_cases hp : p.Prime
  · let B := ((a++b).map fun c => c*n).sum + 1
    have hbound : ∀ c ∈ a++b, Nat.log p (c*n) < B := by
      intro c hc
      have hmem : c*n ∈ (a++b).map (fun c => c*n) := List.mem_map.mpr ⟨c,hc,rfl⟩
      have hle := member_le_sum _ _ hmem
      have hlog := Nat.log_le_self p (c*n)
      omega
    rw [product_factorization b n p hp, product_factorization a n p hp,
      exponent_sum b n p B hp (by intro c hc; exact hbound c (by simp [hc])),
      exponent_sum a n p B hp (by intro c hc; exact hbound c (by simp [hc]))]
    exact Finset.sum_le_sum fun i _ => steps n (p^i)
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

theorem floorSum_division (cs : List ℕ) (n q : ℕ) :
    floorSum cs ((n : ℚ)/q) = (floorAt cs n q : ℤ) := by
  induction cs with
  | nil => simp [floorSum, floorAt]
  | cons c cs ih =>
    simp only [floorSum, floorAt, List.map_cons, List.sum_cons, Nat.cast_add]
    rw [← mul_div_assoc, ← Nat.cast_mul, Rat.floor_natCast_div_natCast,
      ← Int.natCast_ediv]
    exact congrArg₂ (·+·) rfl ih

theorem integral_of_nonnegative (a b : List ℕ)
    (nonnegative : ∀ x : ℚ, 0 ≤ delta a b x) (n : ℕ) :
    factorialProduct b n ∣ factorialProduct a n := by
  apply integral_of_division_steps a b ?_ n
  intro m q
  have h := nonnegative ((m : ℚ)/q)
  rw [delta, floorSum_division, floorSum_division] at h
  omega

theorem floorSum_shift (cs : List ℕ) (x : ℚ) (k : ℤ) :
    floorSum cs (x+k) = floorSum cs x + (cs.sum : ℤ)*k := by
  induction cs with
  | nil => simp [floorSum]
  | cons c cs ih =>
    have he : (c : ℚ)*(x+k) = (c : ℚ)*x + (((c : ℤ)*k : ℤ) : ℚ) := by
      simp [mul_add]
    simp only [floorSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [he, Int.floor_add_intCast, ih]
    simp [Nat.cast_add, add_mul, add_assoc, add_left_comm, add_comm]

theorem balanced_shift (a b : List ℕ) (balanced : a.sum=b.sum) (x : ℚ) (k : ℤ) :
    delta a b (x+k) = delta a b x := by
  simp only [delta, floorSum_shift, balanced]
  omega

theorem nonnegative_of_cells (a b : List ℕ) (balanced : a.sum=b.sum)
    (cells : ∀ x : ℚ, 0 ≤ x → x < 1 → 0 ≤ delta a b x) (x : ℚ) :
    0 ≤ delta a b x := by
  have h := cells (Int.fract x) (Int.fract_nonneg x) (Int.fract_lt_one x)
  have he := balanced_shift a b balanced (Int.fract x) ⌊x⌋
  rw [Int.fract_add_floor] at he
  rwa [he]

end PerfectPower.LandauIntegral
