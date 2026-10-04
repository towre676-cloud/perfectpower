import PerfectPower.NativePolynomialRoots

/-! A complete mixed-variable Runge example from Beukers–Tengely (2005), §5.
The proof uses quadratic projection in x and an explicit square squeeze in y,
rather than reproducing their branch/resultant proof. All bounds are proved here. -/
namespace PerfectPower.MixedRunge
set_option maxRecDepth 100000

def equation (x y : ℤ) : Prop :=
  y^4 + 2*y^3 - 9*x^2*y^2 + 2*x*y - 15*x - 7 = 0

def discriminant (y : ℤ) : ℤ := 36*y^6+72*y^5-248*y^2-60*y+225
def approximation (y : ℤ) : ℤ := 6*y^3+6*y^2-3*y+3

theorem projection (x y : ℤ) (h : equation x y) :
    (18*y^2*x-2*y+15)^2 = discriminant y := by
  unfold equation at h
  unfold discriminant
  linear_combination (-36*y^2)*h

theorem no_square_gap (w q d : ℤ) (hq : 0 ≤ q)
    (hlo : q^2 < d) (hhi : d < (q+1)^2) : w^2 ≠ d := by
  intro h
  have ha : |w|^2 = w^2 := sq_abs w
  have hw := abs_nonneg w
  have hcases : |w| ≤ q ∨ q+1 ≤ |w| := by omega
  rcases hcases with hl | hh
  · nlinarith
  · nlinarith

theorem positive_tail (y : ℤ) (hy : 24 ≤ y) :
    0 ≤ approximation y-1 ∧
      (approximation y-1)^2 < discriminant y ∧
      discriminant y < (approximation y)^2 := by
  let t := y-24
  have ht : 0 ≤ t := by dsimp [t]; omega
  have hq : approximation y-1 = 6*t^3+438*t^2+10653*t+86330 := by
    dsimp [approximation,t]; ring
  have h1 : discriminant y-(approximation y-1)^2 =
      12*t^3+583*t^2+7200*t+3101 := by dsimp [discriminant,approximation,t]; ring
  have h2 : (approximation y)^2-discriminant y =
      293*t^2+14106*t+169560 := by dsimp [discriminant,approximation,t]; ring
  have hq0 : 0 ≤ approximation y-1 := by rw [hq]; positivity
  have h10 : 0 < discriminant y-(approximation y-1)^2 := by rw [h1]; positivity
  have h20 : 0 < (approximation y)^2-discriminant y := by rw [h2]; positivity
  exact ⟨hq0, by omega, by omega⟩

theorem negative_tail (y : ℤ) (hy : y ≤ -26) :
    0 ≤ -approximation y-1 ∧
      (-approximation y-1)^2 < discriminant y ∧
      discriminant y < (-approximation y)^2 := by
  let t := -y-26
  have ht : 0 ≤ t := by dsimp [t]; omega
  have hq : -approximation y-1 = 6*t^3+462*t^2+11853*t+101318 := by
    dsimp [approximation,t]; ring
  have h1 : discriminant y-(-approximation y-1)^2 =
      12*t^3+631*t^2+8512*t+5877 := by dsimp [discriminant,approximation,t]; ring
  have h2 : (-approximation y)^2-discriminant y =
      293*t^2+15194*t+196760 := by dsimp [discriminant,approximation,t]; ring
  have hq0 : 0 ≤ -approximation y-1 := by rw [hq]; positivity
  have h10 : 0 < discriminant y-(-approximation y-1)^2 := by rw [h1]; positivity
  have h20 : 0 < (-approximation y)^2-discriminant y := by rw [h2]; positivity
  exact ⟨hq0, by omega, by omega⟩

theorem coordinate_bound (x y : ℤ) (h : equation x y) : -25 ≤ y ∧ y ≤ 23 := by
  have hp := projection x y h
  constructor
  · by_contra hn
    have hy : y ≤ -26 := by omega
    obtain ⟨hq,hl,hh⟩ := negative_tail y hy
    apply no_square_gap (18*y^2*x-2*y+15) (-approximation y-1) (discriminant y) hq hl
      (by convert hh using 1; ring) hp
  · by_contra hn
    have hy : 24 ≤ y := by omega
    obtain ⟨hq,hl,hh⟩ := positive_tail y hy
    apply no_square_gap (18*y^2*x-2*y+15) (approximation y-1) (discriminant y) hq hl
      (by convert hh using 1; ring) hp

def coefficients (y : ℤ) : List ℤ :=
  if y = 0 then [-7,-15] else [y^4+2*y^3-7,2*y-15,-9*y^2]

theorem valid_coefficients (y : ℤ) : NativePolynomialSquare.valid (coefficients y) := by
  by_cases h : y=0
  · simp [coefficients,h,NativePolynomialSquare.valid]
  · simp [coefficients,h,NativePolynomialSquare.valid,pow_ne_zero 2 h]

theorem fibre_exact (x y : ℤ) : equation x y ↔
    x ∈ NativePolynomialRoots.roots (coefficients y) := by
  rw [← NativePolynomialRoots.complete _ (valid_coefficients y)]
  by_cases h : y=0
  · subst y; simp [equation,coefficients,NativePolynomialSquare.eval]; omega
  · simp only [coefficients,h,if_false,NativePolynomialSquare.eval]
    unfold equation
    constructor <;> intro hh <;> nlinarith [hh]

def points : Finset (ℤ × ℤ) :=
  (Finset.Icc (-25 : ℤ) 23).biUnion fun y =>
    (NativePolynomialRoots.roots (coefficients y)).image fun x => (x,y)

theorem complete (x y : ℤ) : equation x y ↔ (x,y) ∈ points := by
  constructor
  · intro h
    exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_Icc.mpr (coordinate_bound x y h),
      Finset.mem_image.mpr ⟨x,(fibre_exact x y).mp h,rfl⟩⟩
  · intro h
    obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp h
    obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hv
    obtain ⟨hx,hy⟩ := Prod.mk.inj he
    subst u
    subst v
    exact (fibre_exact x y).mpr hu

end PerfectPower.MixedRunge
