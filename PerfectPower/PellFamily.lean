import PerfectPower.QueryNative
import Mathlib.NumberTheory.Pell
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PerfectPower.PellFamily

/-- Adjacent-square certificates exclude every integer square, including negative roots. -/
theorem square_gap (v : ℤ) (q : ℕ) (hl : (q:ℤ)^2 < v)
    (hu : v < ((q:ℤ)+1)^2) (m : ℤ) : m^2 ≠ v := by
  intro he
  have ha := abs_nonneg m
  have hs : |m|^2 = m^2 := sq_abs m
  by_cases h : |m| ≤ (q:ℤ)
  · nlinarith
  · have h' : (q:ℤ)+1 ≤ |m| := by omega
    nlinarith

def gapCheck (D B : ℤ) (roots : List ℕ) : Bool :=
  (List.range B.toNat).all fun n => decide (n=0 ∨
    let q : ℤ := roots[n]?.getD 0
    q^2 < D*(n:ℤ)^2+1 ∧ D*(n:ℤ)^2+1 < (q+1)^2)

/-- A finite adjacent-square certificate establishes minimality of the proposed seed. -/
theorem fundamental (D A B : ℤ) (hD : 0 < D) (hA : 1 < A) (hB : 0 < B)
    (hnorm : A^2-D*B^2=1) (roots : List ℕ) (hgap : gapCheck D B roots = true) :
    Pell.IsFundamental (Pell.Solution₁.mk A B hnorm) := by
  refine ⟨hA,hB,?_⟩
  intro b hb
  change A ≤ b.x
  by_contra hh
  have hx : b.x < A := by omega
  have hn := b.prop
  have ha := abs_nonneg b.y
  have hs : |b.y|^2 = b.y^2 := sq_abs b.y
  have hy : |b.y| < B := by
    by_contra h
    have he : B ≤ |b.y| := by omega
    have hmul : 0 ≤ D*(|b.y|^2-B^2) := mul_nonneg hD.le (by nlinarith)
    nlinarith
  have hypos : 0 < |b.y| := by
    by_contra h
    have he : b.y = 0 := abs_eq_zero.mp (by omega)
    rw [he] at hn
    nlinarith
  let n := |b.y|.toNat
  have hncast : (n:ℤ) = |b.y| := Int.toNat_of_nonneg ha
  have hnb : n < B.toNat := by omega
  have hg := of_decide_eq_true (List.all_eq_true.mp hgap n (List.mem_range.mpr hnb))
  rcases hg with hzero | ⟨hl,hu⟩
  · have : n ≠ 0 := by omega
    exact this hzero
  · apply square_gap (D*(n:ℤ)^2+1) (roots[n]?.getD 0) hl hu b.x
    rw [hncast, hs]
    linarith

abbrev seed (D A B : ℤ) (h : A^2-D*B^2=1) := Pell.Solution₁.mk A B h

def point {D : ℤ} (a : Pell.Solution₁ D) (k : ℕ) : ℤ × ℤ := ((a^k).y,(a^k).x)

def fastPower {D : ℤ} (a : Pell.Solution₁ D) : ℕ → ℕ → Pell.Solution₁ D
  | 0, _ => 1
  | fuel+1, k =>
    let h := fastPower a fuel (k/2)
    if k%2=0 then h*h else h*h*a

theorem fastPower_eq {D : ℤ} (a : Pell.Solution₁ D) (fuel k : ℕ) (hk : k < 2^fuel) :
    fastPower a fuel k = a^k := by
  induction fuel generalizing k with
  | zero =>
    have : k=0 := by simpa using hk
    subst k
    simp [fastPower]
  | succ fuel ih =>
    have hhalf : k/2 < 2^fuel := by
      rw [pow_succ] at hk
      omega
    simp only [fastPower, ih _ hhalf]
    split_ifs with he
    · rw [← pow_add]
      congr 1
      omega
    · rw [← pow_add, ← pow_succ]
      congr 1
      omega

def fastPoint {D : ℤ} (a : Pell.Solution₁ D) (fuel k : ℕ) : ℤ × ℤ :=
  ((fastPower a fuel k).y,(fastPower a fuel k).x)

theorem fastPoint_eq {D : ℤ} (a : Pell.Solution₁ D) (fuel k : ℕ) (hk : k < 2^fuel) :
    fastPoint a fuel k = point a k := by rw [fastPoint, fastPower_eq a fuel k hk]; rfl

theorem point_spec {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a) (k : ℕ) :
    0 ≤ (point a k).1 ∧ 1 ≤ (point a k).2 ∧ (point a k).2^2 = D*(point a k).1^2+1 := by
  have hx := Pell.Solution₁.x_pow_pos ha.x_pos k
  have hy : 0 ≤ (a^k).y := by
    cases k with
    | zero => simp
    | succ k => exact (Pell.Solution₁.y_pow_succ_pos ha.x_pos ha.2.1 k).le
  have hp := (a^k).prop
  change 0 ≤ (a^k).y ∧ 1 ≤ (a^k).x ∧ (a^k).x^2 = D*(a^k).y^2+1
  exact ⟨hy,by omega,by linarith⟩

theorem complete {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a) (p : ℤ × ℤ) :
    (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2^2 = D*p.1^2+1) ↔ ∃ k, point a k = p := by
  constructor
  · rintro ⟨hx,hy,he⟩
    let b := Pell.Solution₁.mk p.2 p.1 (by linarith)
    have hpos : 0 < b.x := by change 0 < p.2; nlinarith [ha.d_pos, sq_nonneg p.1]
    obtain ⟨k,hk⟩ := ha.eq_pow_of_nonneg hpos hx
    refine ⟨k,?_⟩
    rw [point, ← hk]
    exact Prod.eta p
  · rintro ⟨k,rfl⟩
    obtain ⟨hx,hy,he⟩ := point_spec a ha k
    exact ⟨hx,by omega,he⟩

theorem input_strictMono {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a) :
    StrictMono (fun k => (point a k).1) := by
  intro k l h
  have he := ha.y_strictMono (show (k:ℤ)<(l:ℤ) by exact_mod_cast h)
  simpa [point, zpow_natCast] using he

theorem point_injective {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a) :
    Function.Injective (point a) := by
  intro k l h
  exact (input_strictMono a ha).injective (congrArg Prod.fst h)

def populationPrefix {D : ℤ} (a : Pell.Solution₁ D) (length : ℕ) := (List.range length).map (point a)

theorem cutoff_rank {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a)
    (length : ℕ) (N : ℤ) (hpos : 0 < length)
    (hlast : (point a (length-1)).1 ≤ N) (hnext : N < (point a length).1) (k : ℕ) :
    (point a k).1 ≤ N ↔ k < length := by
  constructor
  · intro h
    by_contra hh
    have hm := (input_strictMono a ha).monotone (show length ≤ k by omega)
    omega
  · intro h
    have hm := (input_strictMono a ha).monotone (show k ≤ length-1 by omega)
    omega

theorem prefix_complete {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a)
    (length : ℕ) (N : ℤ) (hpos : 0 < length)
    (hlast : (point a (length-1)).1 ≤ N) (hnext : N < (point a length).1) (p : ℤ × ℤ) :
    p ∈ populationPrefix a length ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ N ∧ p.2^2 = D*p.1^2+1 := by
  simp only [populationPrefix, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k,hk,rfl⟩
    obtain ⟨hx,hy,he⟩ := point_spec a ha k
    exact ⟨hx,by omega,(cutoff_rank a ha length N hpos hlast hnext k).mpr hk,he⟩
  · rintro ⟨hx,hy,hcut,he⟩
    obtain ⟨k,hk⟩ := (complete a ha p).mp ⟨hx,hy,he⟩
    refine ⟨k,?_,hk⟩
    apply (cutoff_rank a ha length N hpos hlast hnext k).mp
    simpa [hk] using hcut

def signVariants (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  if p.1=0 then [(0,p.2),(0,-p.2)]
  else [(p.1,p.2),(-p.1,p.2),(p.1,-p.2),(-p.1,-p.2)]

theorem mem_signVariants (p q : ℤ × ℤ) :
    q ∈ signVariants p ↔ (q.1=p.1 ∨ q.1= -p.1) ∧ (q.2=p.2 ∨ q.2= -p.2) := by
  by_cases h : p.1=0
  · simp [signVariants, h, Prod.ext_iff]
    tauto
  · simp [signVariants, h, Prod.ext_iff]
    tauto

def signedPrefix {D : ℤ} (a : Pell.Solution₁ D) (length : ℕ) :=
  (populationPrefix a length).flatMap signVariants

theorem signed_prefix_complete {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a)
    (length : ℕ) (N : ℤ) (hpos : 0 < length)
    (hlast : (point a (length-1)).1 ≤ N) (hnext : N < (point a length).1) (p : ℤ × ℤ) :
    p ∈ signedPrefix a length ↔ |p.1| ≤ N ∧ p.2^2 = D*p.1^2+1 := by
  simp only [signedPrefix, List.mem_flatMap, mem_signVariants]
  constructor
  · rintro ⟨q,hq,hsx,hsy⟩
    obtain ⟨hx,hy,hcut,he⟩ := (prefix_complete a ha length N hpos hlast hnext q).mp hq
    rcases hsx with hsx | hsx <;> rcases hsy with hsy | hsy <;>
      rw [hsx,hsy] <;> simpa [abs_of_nonneg hx] using And.intro hcut he
  · rintro ⟨hcut,he⟩
    refine ⟨(|p.1|,|p.2|),?_,?_,?_⟩
    · apply (prefix_complete a ha length N hpos hlast hnext _).mpr
      exact ⟨abs_nonneg _,abs_nonneg _,hcut,by simpa only [sq_abs] using he⟩
    · by_cases hx : 0 ≤ p.1
      · exact Or.inl (abs_of_nonneg hx).symm
      · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge hx)]; omega)
    · by_cases hy : 0 ≤ p.2
      · exact Or.inl (abs_of_nonneg hy).symm
      · exact Or.inr (by rw [abs_of_neg (lt_of_not_ge hy)]; omega)

/-- Nonnegative polynomial expressions are monotone on the nonnegative quadrant. -/
def positiveExpr : PerfectPower.QueryNative.Expr → Prop
  | .constant n => 0 ≤ n
  | .x | .y => True
  | .add a b | .mul a b => positiveExpr a ∧ positiveExpr b
  | .power a _ => positiveExpr a

instance positiveExprDecidable : (e : PerfectPower.QueryNative.Expr) → Decidable (positiveExpr e)
  | .constant n => inferInstanceAs (Decidable (0 ≤ n))
  | .x | .y => isTrue trivial
  | .add a b | .mul a b => @instDecidableAnd _ _ (positiveExprDecidable a) (positiveExprDecidable b)
  | .power a _ => positiveExprDecidable a

theorem expr_nonneg (e : PerfectPower.QueryNative.Expr) (he : positiveExpr e)
    (p : ℤ × ℤ) (hx : 0 ≤ p.1) (hy : 0 ≤ p.2) : 0 ≤ e.eval p := by
  induction e with
  | constant n => exact he
  | x => exact hx
  | y => exact hy
  | add a b ia ib => exact add_nonneg (ia he.1) (ib he.2)
  | mul a b ia ib => exact mul_nonneg (ia he.1) (ib he.2)
  | power a n ia => exact pow_nonneg (ia he) n

theorem expr_monotone (e : PerfectPower.QueryNative.Expr) (he : positiveExpr e)
    (p q : ℤ × ℤ) (hx : 0 ≤ p.1) (hy : 0 ≤ p.2)
    (hpx : p.1 ≤ q.1) (hpy : p.2 ≤ q.2) : e.eval p ≤ e.eval q := by
  induction e with
  | constant n => exact le_refl _
  | x => exact hpx
  | y => exact hpy
  | add a b ia ib => exact add_le_add (ia he.1) (ib he.2)
  | mul a b ia ib =>
    exact mul_le_mul (ia he.1) (ib he.2) (expr_nonneg b he.2 p hx hy)
      (expr_nonneg a he.1 q (le_trans hx hpx) (le_trans hy hpy))
  | power a n ia => exact pow_le_pow_left₀ (expr_nonneg a he p hx hy) (ia he) n

theorem global_minimum {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a)
    (e : PerfectPower.QueryNative.Expr) (he : positiveExpr e) (p : ℤ × ℤ)
    (hp : 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2^2 = D*p.1^2+1) :
    e.eval (0,1) ≤ e.eval p := by
  obtain ⟨hx,hy,h⟩ := hp
  have hy1 : 1 ≤ p.2 := by nlinarith [ha.d_pos, sq_nonneg p.1]
  exact expr_monotone e he (0,1) p (by decide) (by decide) hx hy1

theorem input_ge_rank {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a) (k : ℕ) :
    (k:ℤ) ≤ (point a k).1 := by
  induction k with
  | zero => simp [point]
  | succ k ih =>
    have h := input_strictMono a ha (show k<k+1 by omega)
    change (point a k).1 < (point a (k+1)).1 at h
    push_cast
    omega

theorem negative_input_unbounded {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a)
    (bound : ℤ) : ∃ p : ℤ × ℤ, (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2^2 = D*p.1^2+1) ∧ -p.1 < bound := by
  let k := (-bound).toNat+1
  obtain ⟨hx,hy,he⟩ := point_spec a ha k
  have hr := input_ge_rank a ha k
  have hk : -bound < (k:ℤ) := by dsimp [k]; omega
  have hb := lt_of_lt_of_le hk hr
  exact ⟨point a k,⟨hx,by omega,he⟩,by omega⟩

def cutoffFinset {D : ℤ} (a : Pell.Solution₁ D) (length : ℕ) :=
  (Finset.range length).image (point a)

theorem cutoffFinset_complete {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a)
    (length : ℕ) (N : ℤ) (hpos : 0 < length)
    (hlast : (point a (length-1)).1 ≤ N) (hnext : N < (point a length).1) (p : ℤ × ℤ) :
    p ∈ cutoffFinset a length ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ N ∧ p.2^2 = D*p.1^2+1 := by
  simpa [cutoffFinset,populationPrefix] using prefix_complete a ha length N hpos hlast hnext p

theorem cutoffFinset_card {D : ℤ} (a : Pell.Solution₁ D) (ha : Pell.IsFundamental a) (length : ℕ) :
    (cutoffFinset a length).card = length := by
  rw [cutoffFinset,Finset.card_image_of_injective _ (point_injective a ha),Finset.card_range]

end PerfectPower.PellFamily
