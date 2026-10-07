import PerfectPower.GeneralCRT
import PerfectPower.ResiduePopulation
import PerfectPower.FiniteDomainCertificate
import PerfectPower.PolynomialSourceSemantics

/-! Exact Dresden model mathematics. This file proves chart and predicate
transport, finite populations and rank transport. It does not verify JSON
parsing, Python execution, a Sturm producer, or historical source readings. -/
namespace PerfectPower.DresdenCalendar
open PerfectPower

inductive Relation where
  | eq | ne | lt | le | gt | ge

def relationHolds : Relation → ℚ → Prop
  | .eq, x => x = 0
  | .ne, x => x ≠ 0
  | .lt, x => x < 0
  | .le, x => x ≤ 0
  | .gt, x => 0 < x
  | .ge, x => 0 ≤ x

inductive Condition where
  | atom : Relation → Polynomial ℚ → Condition
  | truth : Prop → Condition
  | conj : Condition → Condition → Condition
  | disj : Condition → Condition → Condition
  | neg : Condition → Condition

def holds (x : ℚ) : Condition → Prop
  | .atom r p => relationHolds r (p.eval x)
  | .truth p => p
  | .conj p q => holds x p ∧ holds x q
  | .disj p q => holds x p ∨ holds x q
  | .neg p => ¬ holds x p

noncomputable def affinePolynomial (a m : ℚ) : Polynomial ℚ :=
  Polynomial.C a + Polynomial.C m * Polynomial.X

noncomputable def pullback (a m : ℚ) : Condition → Condition
  | .atom r p => .atom r (p.comp (affinePolynomial a m))
  | .truth p => .truth p
  | .conj p q => .conj (pullback a m p) (pullback a m q)
  | .disj p q => .disj (pullback a m p) (pullback a m q)
  | .neg p => .neg (pullback a m p)

theorem polynomial_pullback (p : Polynomial ℚ) (a m k : ℚ) :
    (p.comp (affinePolynomial a m)).eval k = p.eval (a + m*k) := by
  simp [Polynomial.eval_comp, affinePolynomial]

theorem condition_pullback (c : Condition) (a m k : ℚ) :
    holds k (pullback a m c) ↔ holds (a+m*k) c := by
  induction c <;> simp_all [pullback, holds, polynomial_pullback, affinePolynomial]

def chart (a m k : ℤ) : ℤ := a+m*k

theorem chart_injective (a m : ℤ) (hm : m ≠ 0) :
    Function.Injective (chart a m) := by
  intro x y h
  exact mul_left_cancel₀ hm (add_left_cancel h)

theorem integer_pullback (c : Condition) (a m k : ℤ) :
    holds (k:ℚ) (pullback a m c) ↔ holds (chart a m k : ℚ) c := by
  simpa [chart, Int.cast_add, Int.cast_mul] using condition_pullback c a m k

noncomputable def accepted (cell : ResiduePopulation.Cell) (c : Condition) : Finset ℤ := by
  classical
  exact (ResiduePopulation.values cell).filter (fun x => holds (x:ℚ) c)

noncomputable def parameters (cell : ResiduePopulation.Cell) (c : Condition) : Finset ℤ := by
  classical
  exact (Finset.Icc ((cell.lower-1-cell.residue)/cell.modulus+1)
    ((cell.upper-cell.residue)/cell.modulus)).filter
      (fun k => holds (k:ℚ) (pullback cell.residue cell.modulus c))

theorem accepted_membership (cell : ResiduePopulation.Cell) (c : Condition) (x : ℤ) :
    x ∈ accepted cell c ↔ ResiduePopulation.accepts cell x ∧ holds (x:ℚ) c := by
  classical
  simp [accepted]

theorem accepted_image (cell : ResiduePopulation.Cell) (c : Condition)
    (hm : 0 < cell.modulus) (hr : 0 ≤ cell.residue) (hrm : cell.residue < cell.modulus) :
    accepted cell c = (parameters cell c).image (chart cell.residue cell.modulus) := by
  classical
  unfold accepted parameters
  rw [ResiduePopulation.interval_image cell hm hr hrm]
  ext x
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨k,hk,rfl⟩,hc⟩
    exact ⟨k,⟨hk,(integer_pullback c _ _ _).mpr hc⟩,rfl⟩
  · rintro ⟨k,⟨hk,hc⟩,rfl⟩
    exact ⟨⟨k,hk,rfl⟩,(integer_pullback c _ _ _).mp hc⟩

theorem accepted_count (cell : ResiduePopulation.Cell) (c : Condition)
    (hm : 0 < cell.modulus) (hr : 0 ≤ cell.residue) (hrm : cell.residue < cell.modulus) :
    (accepted cell c).card = (parameters cell c).card := by
  rw [accepted_image cell c hm hr hrm,
    Finset.card_image_of_injective _ (chart_injective _ _ (ne_of_gt hm))]

theorem affine_rank (S : Finset ℤ) (a m k : ℤ) (hm : 0 < m) :
    FiniteDomainCertificate.rank (S.image (chart a m)) (chart a m k) =
      FiniteDomainCertificate.rank S k := by
  classical
  have hf : (S.image (chart a m)).filter (fun x => x < chart a m k) =
      (S.filter (fun x => x < k)).image (chart a m) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨j,hj,rfl⟩,hlt⟩
      refine ⟨j,⟨hj,?_⟩,rfl⟩
      dsimp [chart] at hlt
      nlinarith
    · rintro ⟨j,⟨hj,hlt⟩,rfl⟩
      refine ⟨⟨j,hj,rfl⟩,?_⟩
      dsimp [chart]
      nlinarith
  unfold FiniteDomainCertificate.rank
  rw [hf, Finset.card_image_of_injective _ (chart_injective _ _ (ne_of_gt hm))]

theorem accepted_rank (cell : ResiduePopulation.Cell) (c : Condition) (k : ℤ)
    (hm : 0 < cell.modulus) (hr : 0 ≤ cell.residue) (hrm : cell.residue < cell.modulus) :
    FiniteDomainCertificate.rank (accepted cell c) (chart cell.residue cell.modulus k) =
      FiniteDomainCertificate.rank (parameters cell c) k := by
  rw [accepted_image cell c hm hr hrm]
  exact affine_rank _ _ _ _ hm

theorem selected_day (cell : ResiduePopulation.Cell) (c : Condition) (k : ℤ) (i : ℕ)
    (hm : 0 < cell.modulus) (hr : 0 ≤ cell.residue) (hrm : cell.residue < cell.modulus)
    (hk : k ∈ parameters cell c) (hi : FiniteDomainCertificate.rank (parameters cell c) k = i) :
    ResiduePopulation.accepts cell (chart cell.residue cell.modulus k) ∧
    holds (chart cell.residue cell.modulus k : ℚ) c ∧
    ∀ x ∈ accepted cell c, FiniteDomainCertificate.rank (accepted cell c) x = i →
      x = chart cell.residue cell.modulus k := by
  have hx : chart cell.residue cell.modulus k ∈ accepted cell c := by
    rw [accepted_image cell c hm hr hrm]
    exact Finset.mem_image.mpr ⟨k,hk,rfl⟩
  have hi' : FiniteDomainCertificate.rank (accepted cell c)
      (chart cell.residue cell.modulus k) = i := (accepted_rank cell c k hm hr hrm).trans hi
  exact ⟨((accepted_membership cell c _).mp hx).1,
    ((accepted_membership cell c _).mp hx).2,
    fun x hx' hix => FiniteDomainCertificate.select_unique _ i x _ hx' hx hix hi'⟩

theorem calendar_compatibility (a b : ℕ) :
    (∃ x, Nat.ModEq 260 x a ∧ Nat.ModEq 365 x b) ↔ Nat.ModEq 5 a b := by
  have hg : Nat.gcd 260 365 = 5 := by decide
  simpa [hg] using GeneralCRT.compatible_iff 260 365 a b

theorem calendar_period : Nat.lcm 260 365 = 18980 := by decide
theorem joint_venus_period : Nat.lcm 18980 584 = 37960 := by decide

def longCountDays (b k t u d : ℕ) : ℕ := 144000*b+7200*k+360*t+20*u+d

/-- The nondecimal 18-uinal carry is part of the declared numeral model. -/
theorem long_count_uinal_carry (b k t d : ℕ) :
    longCountDays b k t 18 d = longCountDays b k (t+1) 0 d := by
  unfold longCountDays
  ring

/-- Canonical five-place readings cannot encode two different digit tuples. -/
theorem long_count_unique (b k t u d b' k' t' u' d' : ℕ)
    (hk : k < 20) (ht : t < 20) (hu : u < 18) (hd : d < 20)
    (hk' : k' < 20) (ht' : t' < 20) (hu' : u' < 18) (hd' : d' < 20)
    (he : longCountDays b k t u d = longCountDays b' k' t' u' d') :
    b=b' ∧ k=k' ∧ t=t' ∧ u=u' ∧ d=d' := by
  unfold longCountDays at he
  omega

/-- Overlapping equal-residue tails activate at the earlier boundary. -/
theorem restart_activation (a b x m : ℤ) (hab : Int.ModEq m a b) :
    ((a ≤ x ∧ Int.ModEq m x a) ∨ (b ≤ x ∧ Int.ModEq m x b)) ↔
      min a b ≤ x ∧ Int.ModEq m x a := by
  constructor
  · rintro (⟨ha,hx⟩ | ⟨hb,hx⟩)
    · exact ⟨(min_le_left a b).trans ha,hx⟩
    · exact ⟨(min_le_right a b).trans hb,hx.trans hab.symm⟩
  · rintro ⟨hmin,hx⟩
    by_cases h : a ≤ b
    · left; exact ⟨by simpa [min_eq_left h] using hmin,hx⟩
    · right; exact ⟨by simpa [min_eq_right (le_of_not_ge h)] using hmin,hx.trans hab⟩

/-- An affine drift inside a block is bounded by that block's endpoints. -/
theorem affine_envelope (a b lo hi x : ℚ) (hl : lo ≤ x) (hh : x ≤ hi) :
    min (a+b*lo) (a+b*hi) ≤ a+b*x ∧ a+b*x ≤ max (a+b*lo) (a+b*hi) := by
  rcases le_total 0 b with hb | hb
  · have he : a+b*lo ≤ a+b*hi := by nlinarith
    rw [min_eq_left he, max_eq_right he]
    constructor <;> nlinarith
  · have he : a+b*hi ≤ a+b*lo := by nlinarith
    rw [min_eq_right he, max_eq_left he]
    constructor <;> nlinarith

/-- Number of indexed span intervals in a contiguous appearance window. -/
theorem lunar_window_count (n span : ℕ) : (Finset.range (n-span)).card = n-span := by
  simp

/-- Two sufficiently long halves omit exactly `span` crossing intervals. -/
theorem lunar_split_count (n boundary span : ℕ)
    (hleft : span ≤ boundary) (hright : boundary+span ≤ n) :
    n-span = (boundary-span) + (n-boundary-span) + span := by omega

end PerfectPower.DresdenCalendar
