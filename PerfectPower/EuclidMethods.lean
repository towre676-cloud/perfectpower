import Std

/-! Algebraic foundations for Euclidean certificates. Python execution is separate. -/
namespace PerfectPower.EuclidMethods

def horner : List Int → Int → Int
  | [], _ => 0
  | a::as, n => a+n*horner as n

def addPoly : List Int → List Int → List Int
  | [], bs => bs
  | as, [] => as
  | a::as, b::bs => (a+b)::addPoly as bs

def scalePoly (k : Int) (as : List Int) : List Int := as.map (k*·)

def mulPoly : List Int → List Int → List Int
  | [], _ => []
  | a::as, bs => addPoly (scalePoly a bs) (0::mulPoly as bs)

theorem horner_add (as bs : List Int) (n : Int) :
    horner (addPoly as bs) n=horner as n+horner bs n := by
  induction as generalizing bs with
  | nil => simp [addPoly, horner]
  | cons a as ih =>
    cases bs with
    | nil => simp [addPoly, horner]
    | cons b bs =>
      simp only [addPoly, horner]
      rw [ih, Int.mul_add]
      omega

theorem horner_scale (as : List Int) (k n : Int) :
    horner (scalePoly k as) n=k*horner as n := by
  induction as with
  | nil => simp [scalePoly, horner]
  | cons a as ih =>
    simp only [scalePoly, List.map_cons, horner] at *
    rw [ih]
    simp [Int.mul_add, Int.mul_assoc, Int.mul_left_comm]

theorem horner_mul (as bs : List Int) (n : Int) :
    horner (mulPoly as bs) n=horner as n*horner bs n := by
  induction as with
  | nil => simp [mulPoly, horner]
  | cons a as ih =>
    rw [mulPoly, horner_add, horner_scale]
    simp only [horner, Int.zero_add]
    rw [ih]
    simp [Int.add_mul, Int.mul_assoc]

/-- A common divisor divides every integral linear combination. -/
theorem common_divisor_bezout (a b u v c d : Int)
    (ha : d ∣ a) (hb : d ∣ b) (hidentity : u*a+v*b=c) : d ∣ c := by
  rcases ha with ⟨x, hx⟩
  rcases hb with ⟨y, hy⟩
  refine ⟨u*x+v*y, ?_⟩
  rw [← hidentity, hx, hy]
  simp only [Int.mul_add, Int.mul_assoc, Int.mul_left_comm]

/-- Evaluation of a polynomial Bezout identity supplies the arithmetic premise above. -/
theorem evaluated_obstruction (A B U V : Int → Int) (c : Int)
    (identity : ∀ n, U n*A n+V n*B n=c) (n d : Int)
    (hA : d ∣ A n) (hB : d ∣ B n) : d ∣ c :=
  common_divisor_bezout (A n) (B n) (U n) (V n) c d hA hB (identity n)

/-- Valuation residues in a product power are complementary modulo its degree.
The valuation-additivity premise is supplied by the number-theoretic caller. -/
theorem complementary_exponents (e f d k : Nat) (h : e+f=d*k) :
    (e+f)%d=0 := by rw [h]; simp

/-- Squared-distance difference with no radical evaluation. -/
theorem squared_difference (x a b : Int) :
    (x-a)*(x-a)-(x-b)*(x-b) =
    (x*b+x*b)-(x*a+x*a)+a*a-b*b := by
  simp only [Int.sub_mul, Int.mul_sub]
  rw [Int.mul_comm a x, Int.mul_comm b x]
  omega

/-- Similarity scaling preserves squared differences exactly. -/
theorem squared_scale (x y k : Int) :
    (k*x-k*y)*(k*x-k*y)=k*k*((x-y)*(x-y)) := by
  simp only [← Int.mul_sub, Int.mul_assoc, Int.mul_left_comm]

/-- Exact dyadic denominator growth for interval-width bounds. -/
def dyadicWidth (initial : Nat) : Nat → Nat
  | 0 => initial
  | k+1 => 2*dyadicWidth initial k

theorem dyadic_growth (initial k : Nat) : dyadicWidth initial k=2^k*initial := by
  induction k with
  | zero => simp [dyadicWidth]
  | succ k ih =>
    simp [dyadicWidth, ih, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

-- Concrete exceptional-prime descent: x(x+2), resultant 2.
theorem adjacent_two_bezout (n : Int) : -(n)+(n+2)=2 := by omega
theorem adjacent_two_common_divisor (n d : Int) (ha : d ∣ n) (hb : d ∣ n+2) : d ∣ 2 := by
  exact common_divisor_bezout n (n+2) (-1) 1 2 d ha hb (by omega)

-- Source-independent finite norm and interval checks.
theorem pell_61_norm : (1766319049 : Int)^2-61*226153980^2=1 := by decide
theorem sqrt_two_bounds :
    (1414213 : Int)^2 < 2*1000000^2 ∧ 2*1000000^2 < (1414214 : Int)^2 := by decide

#print axioms horner_mul
#print axioms evaluated_obstruction
#print axioms squared_difference
#print axioms complementary_exponents
#print axioms adjacent_two_common_divisor
#print axioms pell_61_norm
#print axioms sqrt_two_bounds
end PerfectPower.EuclidMethods
