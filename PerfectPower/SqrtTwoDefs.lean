import PerfectPower.SqrtTwoBridges

/-!
# Four more `√2` entries, from their own definitions

Each entry is defined from the text of its OEIS record and proved equal to a coordinate of
`(1 + √2)^k = A_k + B_k √2` (`SqrtTwoOrbit.A`, `SqrtTwoOrbit.B`).

* **A024537**: `a(n) = ⌊a(n-1)/(√2 − 1)⌋`, `a(0) = 1`.  `2 a(n) = A_{n+1} + 1`
  (`A024537_eq`).  The step is `⌊(1 + √2) a⌋ = a'`: with `2a = A + 1` and `2a' = A + 2B + 1`,
  `(1 + √2) a − a' = (√2 (A + 1) − 2B)/2`, which lies in `[0, 1)` because
  `2B² ≤ (A + 1)²` and `(A + 1)² < 2(B + 1)²` (from `A² − 2B² = ±1` and `A < 2B`).
* **A018905** ("Duplicate of A024537", offset 0): its terms are those of A024537 **shifted by
  one**, so the duplicate label cannot be read at the same index.  We record the reading
  `a(n) = A024537(n + 1)` fixed by the terms (`A018905_eq`).
* **A171842**: binomial transform of `1, 0, 1, 0, 2, 0, 4, 0, 8, …`.  The finite sum is evaluated by
  the binomial theorem: `4 c_j = 2[j = 0] + √2^j + (−√2)^j`, so
  `4 a(n) = 2 + (1 + √2)^n + (1 − √2)^n = 2 + 2A_n` (`A171842_eq`).
* **A163271**: numerators of `r(1) = 0`, `r(n) = (r(n-1) + 2)/(r(n-1) + 1)`.  The vector
  `(N, D)` moves by `[[1, 2], [1, 1]]`, so `r(n) = 2B_{n-1}/A_{n-1}`, and
  `A·A − 2B·B = ±1` makes the fraction reduced: the **reduced** numerator is `2B_{n-1}`
  (`A163271_eq`).
-/

namespace PerfectPower.SqrtTwoDefs

open PerfectPower SqrtTwoOrbit Finset

/-! ### Basic facts on the orbit -/

lemma A_pos' (k : ℕ) : 0 < SqrtTwoOrbit.A k := A_pos k

lemma B_ge_one (k : ℕ) : 1 ≤ B (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [B_succ] at ih ⊢; rw [B_succ]; nlinarith [A_pos k, B_nonneg k, A_pos (k + 1), B_nonneg (k + 1)]

lemma norm_pm (k : ℕ) : SqrtTwoOrbit.A k ^ 2 - 2 * B k ^ 2 = 1 ∨ SqrtTwoOrbit.A k ^ 2 - 2 * B k ^ 2 = -1 := by
  rw [norm_AB]; rcases neg_one_pow_eq_or ℤ k with h | h <;> simp [h]

/-- `A < 2B` from `k ≥ 1`. -/
lemma A_lt_two_B (k : ℕ) : SqrtTwoOrbit.A (k + 1) < 2 * B (k + 1) := by
  have h1 := B_ge_one k
  have h2 := A_pos (k + 1)
  rcases norm_pm (k + 1) with h | h <;> nlinarith

/-- `(1 + √2)^n = A_n + B_n √2` and `(1 − √2)^n = A_n − B_n √2`. -/
lemma pow_eq (n : ℕ) : (1 + Real.sqrt 2) ^ n = SqrtTwoOrbit.A n + B n * Real.sqrt 2 ∧
    (1 - Real.sqrt 2) ^ n = SqrtTwoOrbit.A n - B n * Real.sqrt 2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  induction n with
  | zero => simp [SqrtTwoOrbit.A, B, AB]
  | succ n ih =>
    rw [pow_succ, pow_succ, ih.1, ih.2, A_succ, B_succ]
    push_cast
    constructor <;> linear_combination (B n : ℝ) * hs

/-! ### A024537: the floor recursion -/

/-- **A024537** (offset 0): `a(n) = floor( a(n-1)/(sqrt(2) - 1) )`, with `a(0) = 1`. -/
noncomputable def A024537 : ℕ → ℤ
  | 0 => 1
  | n + 1 => ⌊(A024537 n : ℝ) / (Real.sqrt 2 - 1)⌋

lemma inv_sqrt2_sub_one : 1 / (Real.sqrt 2 - 1) = 1 + Real.sqrt 2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  field_simp [show Real.sqrt 2 - 1 ≠ 0 by linarith]
  linarith

/-- The floor step: if `2a = A_k + 1` (`k ≥ 1`) then `⌊(1 + √2) a⌋ = (A_{k+1} + 1)/2`. -/
lemma floor_step (k : ℕ) (a a' : ℤ) (ha : 2 * a = SqrtTwoOrbit.A (k + 1) + 1) (ha' : 2 * a' = SqrtTwoOrbit.A (k + 2) + 1) :
    ⌊(a : ℝ) * (1 + Real.sqrt 2)⌋ = a' := by
  set s := Real.sqrt 2
  have hs : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hA := A_pos (k + 1)
  have hB := B_ge_one k
  have hAB := A_lt_two_B k
  have e : SqrtTwoOrbit.A (k + 2) = SqrtTwoOrbit.A (k + 1) + 2 * B (k + 1) := A_succ (k + 1)
  -- integer inequalities
  have i1 : 2 * B (k + 1) ^ 2 ≤ (SqrtTwoOrbit.A (k + 1) + 1) ^ 2 := by rcases norm_pm (k + 1) with h | h <;> nlinarith
  have i2 : (SqrtTwoOrbit.A (k + 1) + 1) ^ 2 < 2 * (B (k + 1) + 1) ^ 2 := by
    rcases norm_pm (k + 1) with h | h <;> nlinarith
  have r1 : 2 * (B (k + 1) : ℝ) ^ 2 ≤ ((SqrtTwoOrbit.A (k + 1) : ℝ) + 1) ^ 2 := by exact_mod_cast i1
  have r2 : ((SqrtTwoOrbit.A (k + 1) : ℝ) + 1) ^ 2 < 2 * ((B (k + 1) : ℝ) + 1) ^ 2 := by exact_mod_cast i2
  -- s (A + 1) ≥ 2B and s (A + 1) < 2B + 2
  have l1 : 2 * (B (k + 1) : ℝ) ≤ s * ((SqrtTwoOrbit.A (k + 1) : ℝ) + 1) := by
    by_contra h; push_neg at h
    have := mul_self_lt_mul_self (by positivity) h
    nlinarith
  have l2 : s * ((SqrtTwoOrbit.A (k + 1) : ℝ) + 1) < 2 * (B (k + 1) : ℝ) + 2 := by
    by_contra h; push_neg at h
    have := mul_self_le_mul_self (by positivity) h
    nlinarith
  have ha2 : (2 : ℝ) * a = SqrtTwoOrbit.A (k + 1) + 1 := by exact_mod_cast ha
  have ha2' : (2 : ℝ) * a' = SqrtTwoOrbit.A (k + 2) + 1 := by exact_mod_cast ha'
  have e' : (SqrtTwoOrbit.A (k + 2) : ℝ) = SqrtTwoOrbit.A (k + 1) + 2 * B (k + 1) := by exact_mod_cast e
  rw [Int.floor_eq_iff]
  constructor <;> nlinarith

lemma A_odd (k : ℕ) : ∃ a : ℤ, 2 * a = SqrtTwoOrbit.A k + 1 := by
  have := (parity k).1
  exact ⟨(SqrtTwoOrbit.A k + 1) / 2, by omega⟩

/-- **A024537 is a coordinate**: `2 a(n) = A_{n+1} + 1`. -/
theorem A024537_eq (n : ℕ) : 2 * A024537 n = SqrtTwoOrbit.A (n + 1) + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨a', ha'⟩ := A_odd (n + 2)
    have : A024537 (n + 1) = a' := by
      rw [A024537, div_eq_mul_one_div, inv_sqrt2_sub_one]
      exact floor_step n _ a' ih ha'
    rw [this, ha']

/-! ### A018905: the duplicate, read with its shift -/

/-- **A018905** (offset 0), "Duplicate of A024537": its terms `2, 4, 9, …` are A024537 from index 1,
so the entry is read as `a(n) = A024537(n + 1)`.  The shift is fixed by the terms; at the same
index the two records disagree. -/
noncomputable def A018905 (n : ℕ) : ℤ := A024537 (n + 1)

theorem A018905_eq (n : ℕ) : 2 * A018905 n = SqrtTwoOrbit.A (n + 2) + 1 := A024537_eq (n + 1)

/-! ### A171842: the binomial transform -/

/-- The sequence `1, 0, 1, 0, 2, 0, 4, 0, 8, …` (offset 0): `c₀ = 1`, `c_{2j} = 2^{j-1}`
(`j ≥ 1`), `c_{2j+1} = 0`. -/
def c171842 (j : ℕ) : ℤ := if j = 0 then 1 else if j % 2 = 1 then 0 else 2 ^ (j / 2 - 1)

/-- **A171842** (offset 0): the binomial transform `a(n) = Σ_{j ≤ n} C(n, j) c_j`. -/
def A171842 (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), (n.choose j : ℤ) * c171842 j

lemma four_c (j : ℕ) :
    4 * (c171842 j : ℝ) = 2 * (if j = 0 then 1 else 0) + Real.sqrt 2 ^ j + (-Real.sqrt 2) ^ j := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · have e1 : Real.sqrt 2 ^ (2 * i) = 2 ^ i := by rw [pow_mul, hs]
    have e2 : (-Real.sqrt 2) ^ (2 * i) = 2 ^ i := by rw [Even.neg_pow (even_two_mul i), e1]
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp [c171842]; norm_num
    · have h1 : 2 * i ≠ 0 := by omega
      have h2 : ¬ (2 * i) % 2 = 1 := by omega
      simp only [c171842, h1, h2, if_false, show 2 * i / 2 = i by omega]
      push_cast
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [show m + 1 - 1 = m by omega, pow_succ]; ring
  · have h1 : 2 * i + 1 ≠ 0 := by omega
    have h2 : (2 * i + 1) % 2 = 1 := by omega
    simp only [c171842, h1, h2, if_true, if_false, Int.cast_zero, mul_zero]
    rw [Odd.neg_pow ⟨i, rfl⟩]; ring

/-- **A171842 is a coordinate**: `2 a(n) = A_n + 1`. -/
theorem A171842_eq (n : ℕ) : 2 * A171842 n = SqrtTwoOrbit.A n + 1 := by
  have key : 4 * (A171842 n : ℝ) = 2 + (1 + Real.sqrt 2) ^ n + (1 - Real.sqrt 2) ^ n := by
    have h1 := add_pow (Real.sqrt 2) 1 n
    have h2 := add_pow (-Real.sqrt 2) 1 n
    rw [add_comm (Real.sqrt 2) 1] at h1
    rw [show -Real.sqrt 2 + 1 = 1 - Real.sqrt 2 by ring] at h2
    rw [h1, h2]
    simp only [one_pow, mul_one, A171842]
    push_cast
    rw [mul_sum]
    have hz : ∑ j ∈ range (n + 1), (n.choose j : ℝ) * (2 * (if j = 0 then 1 else 0)) = 2 := by
      rw [sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp)]; simp
    have hsplit : ∑ j ∈ range (n + 1), ((n.choose j : ℝ) * (2 * (if j = 0 then 1 else 0)) +
        Real.sqrt 2 ^ j * (n.choose j : ℝ) + (-Real.sqrt 2) ^ j * (n.choose j : ℝ)) =
        2 + ∑ x ∈ range (n + 1), Real.sqrt 2 ^ x * (n.choose x : ℝ) +
          ∑ x ∈ range (n + 1), (-Real.sqrt 2) ^ x * (n.choose x : ℝ) := by
      rw [sum_add_distrib, sum_add_distrib, hz]
    rw [← hsplit]
    refine sum_congr rfl fun j _ => ?_
    have := four_c j
    linear_combination (n.choose j : ℝ) * this
  have hp := pow_eq n
  rw [hp.1, hp.2] at key
  have : (2 : ℝ) * A171842 n = SqrtTwoOrbit.A n + 1 := by linarith
  exact_mod_cast this

/-! ### A163271: reduced numerators of the Möbius iteration -/

/-- The iteration `r(1) = 0`, `r(n) = (r(n-1) + 2)/(r(n-1) + 1)`, indexed from 0 (`r163 j = r(j+1)`). -/
def r163 : ℕ → ℚ
  | 0 => 0
  | j + 1 => (r163 j + 2) / (r163 j + 1)

/-- **A163271** (offset 1): the numerator of `r(n)` (as a reduced fraction). -/
def A163271 (n : ℕ) : ℤ := (r163 (n - 1)).num

lemma r163_eq (j : ℕ) : r163 j = (2 * B j : ℚ) / SqrtTwoOrbit.A j := by
  induction j with
  | zero => simp [r163, B, AB]
  | succ j ih =>
    have hA : (SqrtTwoOrbit.A j : ℚ) ≠ 0 := by exact_mod_cast (A_pos j).ne'
    have hA' : (SqrtTwoOrbit.A j : ℚ) + 2 * B j ≠ 0 := by
      have := A_pos j; have := B_nonneg j
      exact_mod_cast (show SqrtTwoOrbit.A j + 2 * B j ≠ 0 by omega)
    have hA'' : 2 * (B j : ℚ) + SqrtTwoOrbit.A j ≠ 0 := by rw [add_comm]; exact hA'
    rw [r163, ih, A_succ, B_succ]
    push_cast
    field_simp
    ring

lemma coprime_A_2B (j : ℕ) : IsCoprime (2 * B j) (SqrtTwoOrbit.A j) := by
  rcases norm_pm j with h | h
  · exact ⟨-B j, SqrtTwoOrbit.A j, by linear_combination h⟩
  · exact ⟨B j, -SqrtTwoOrbit.A j, by linear_combination -h⟩

/-- **A163271 is a coordinate**: the reduced numerator of `r(n)` is `2 B_{n-1}` (the entry's
indices are `n ≥ 1`). -/
theorem A163271_eq (n : ℕ) : A163271 n = 2 * B (n - 1) := by
  unfold A163271
  rw [r163_eq]
  have hc := coprime_A_2B (n - 1)
  have hA := A_pos (n - 1)
  have := Rat.num_div_eq_of_coprime (a := 2 * B (n - 1)) (b := SqrtTwoOrbit.A (n - 1)) hA
    (Int.isCoprime_iff_gcd_eq_one.mp hc)
  push_cast at this ⊢
  exact this

/-! ### A069306: paths in a `2 × n` binary array

A `2 × n` array is a function from the `n` columns to `(top, bottom)`.  A cell is `(row, column)`
with row `false` = top, `true` = bottom; two cells are adjacent when they share an edge.  An array
is **good** when a path of adjacent `1`s joins the upper-left cell to some cell of the right-hand
column (`Good`).

The proof tracks the **frontier**: which cells of the last column are reachable (`St`: none, top,
bottom, both), updated column by column by `next`.  `reach_iff` shows that the frontier is exactly
the set of reachable cells of the last column, for paths that may also run back to the left.  The
counts by frontier state then satisfy `top' = top + both`, `bottom' = bottom + both`,
`both' = top + bottom + both`, and the invariants `top + bottom = A_n`, `both = B_n`,
`top = bottom + 1` give `a(n) = A_n + B_n = B_{n+1}`. -/

/-- A `2 × n` binary array, as its columns `(top, bottom)`. -/
abbrev Arr (n : ℕ) := Fin n → Bool × Bool

/-- The entry of a column in row `r`. -/
def cv (c : Bool × Bool) (r : Bool) : Bool := if r then c.2 else c.1

/-- The entry at a cell `(row, column)`. -/
def val {n : ℕ} (f : Arr n) (x : Bool × Fin n) : Bool := cv (f x.2) x.1

/-- Cells sharing an edge. -/
def adj {n : ℕ} (x y : Bool × Fin n) : Prop :=
  (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) ∨ (x.2 = y.2 ∧ x.1 ≠ y.1)

/-- One step of a path of `1`s. -/
def stp {n : ℕ} (f : Arr n) (x y : Bool × Fin n) : Prop := adj x y ∧ val f x = true ∧ val f y = true

/-- A path of adjacent `1`s from the upper-left corner to a cell of the right-hand column. -/
def Good {n : ℕ} (f : Arr n) : Prop :=
  ∃ (h : 0 < n) (r : Bool), val f (false, ⟨0, h⟩) = true ∧
    Relation.ReflTransGen (stp f) (false, ⟨0, h⟩) (r, ⟨n - 1, by omega⟩)

open Classical in
/-- **A069306** (offset 2): the number of `2 × n` binary arrays with a path of adjacent `1`s from
the upper-left corner to anywhere in the right-hand column. -/
noncomputable def A069306 (n : ℕ) : ℕ := (univ.filter (fun f : Arr n => Good f)).card

/-- The frontier: which cells of the current column are reachable. -/
inductive St
  | dead
  | top
  | bot
  | both
  deriving DecidableEq, Fintype

/-- Whether row `r` is in the frontier. -/
def St.has : St → Bool → Bool
  | .top, r => !r
  | .bot, r => r
  | .both, _ => true
  | .dead, _ => false

/-- The frontier after one more column `c`. -/
def next (s : St) (c : Bool × Bool) : St :=
  if c.1 && c.2 && ((s.has false && c.1) || (s.has true && c.2)) then .both
  else if s.has false && c.1 then .top
  else if s.has true && c.2 then .bot
  else .dead

/-- The frontier of an array of width `m + 1` (the start acts as a frontier `top`). -/
def front : (m : ℕ) → Arr (m + 1) → St
  | 0, f => next .top (f 0)
  | m + 1, f => next (front m (Fin.init f)) (f (Fin.last (m + 1)))

lemma L_entry : ∀ s c r, s.has r = true → cv c r = true → (next s c).has r = true := by decide
lemma L_detour : ∀ s c r, next s c ≠ .dead → cv c r = true → (next s c).has r = true := by decide
lemma L_vert : ∀ s c r r', (next s c).has r = true → cv c r' = true → (next s c).has r' = true := by
  decide
lemma L_ne : ∀ s c r, (next s c).has r = true → next s c ≠ .dead := by decide
lemma L_back : ∀ s c r, (next s c).has r = true →
    ∃ r0 : Bool, s.has r0 = true ∧ cv c r0 = true ∧ (r0 = r ∨ cv c r = true) := by decide
lemma L_some : ∀ s : St, (∃ r, s.has r = true) ↔ s ≠ .dead := by decide

lemma rtg_val {n : ℕ} {f : Arr n} {a b : Bool × Fin n} (h : Relation.ReflTransGen (stp f) a b)
    (ha : val f a = true) : val f b = true := by
  induction h with
  | refl => exact ha
  | tail _ hs _ => exact hs.2.2

/-- The embedding of the first `m + 1` columns into `m + 2`. -/
def emb {m : ℕ} (x : Bool × Fin (m + 1)) : Bool × Fin (m + 2) := (x.1, x.2.castSucc)

lemma val_emb {m : ℕ} (f : Arr (m + 2)) (x : Bool × Fin (m + 1)) :
    val f (emb x) = val (Fin.init f) x := rfl

lemma lift {m : ℕ} (f : Arr (m + 2)) {a b : Bool × Fin (m + 1)}
    (h : Relation.ReflTransGen (stp (Fin.init f)) a b) :
    Relation.ReflTransGen (stp f) (emb a) (emb b) := by
  refine Relation.ReflTransGen.lift emb (fun x y hxy => ?_) h
  refine ⟨?_, by rw [val_emb]; exact hxy.2.1, by rw [val_emb]; exact hxy.2.2⟩
  rcases hxy.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1, by simpa [emb] using h2⟩
  · right; exact ⟨by simp [emb, h1], h2⟩

/-- **The frontier is the set of reachable cells of the last column.** -/
theorem reach_iff (m : ℕ) : ∀ (f : Arr (m + 1)) (r : Bool),
    (val f (false, 0) = true ∧ Relation.ReflTransGen (stp f) (false, 0) (r, Fin.last m)) ↔
      (front m f).has r = true := by
  induction m with
  | zero =>
    intro f r
    constructor
    · rintro ⟨hs, h⟩
      suffices ∀ y, Relation.ReflTransGen (stp f) (false, 0) y → (front 0 f).has y.1 = true from
        this _ h
      intro y hy
      induction hy with
      | refl => exact L_entry .top (f 0) false rfl hs
      | tail _ hxy ih =>
        rename_i x y _
        rcases hxy.1 with ⟨_, h2⟩ | ⟨h1, h2⟩
        · omega
        · have hy : val f y = true := hxy.2.2
          have hy0 : y.2 = 0 := Fin.ext (by simp)
          exact L_vert _ _ x.1 y.1 ih (by simpa [val, hy0] using hy)
    · intro h
      obtain ⟨r0, h0, hc, hr⟩ := L_back _ _ _ h
      have r0f : r0 = false := by cases r0 <;> simp_all [St.has]
      subst r0f
      have hs : val f (false, 0) = true := hc
      refine ⟨hs, ?_⟩
      rcases hr with rfl | hr
      · exact Relation.ReflTransGen.refl
      · cases r
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single ⟨Or.inr ⟨rfl, by simp⟩, hs, hr⟩
  | succ m ih =>
    intro f r
    set g := Fin.init f
    set c := f (Fin.last (m + 1))
    have hfront : front (m + 1) f = next (front m g) c := rfl
    have hstart : (false, (0 : Fin (m + 2))) = emb (false, (0 : Fin (m + 1))) := rfl
    constructor
    · rintro ⟨hs, h⟩
      -- the invariant along the path
      suffices H : ∀ y, Relation.ReflTransGen (stp f) (false, 0) y →
          (∀ hy : y.2.val < m + 1, (val g (false, 0) = true ∧
              Relation.ReflTransGen (stp g) (false, 0) (y.1, ⟨y.2.val, hy⟩)) ∨
            next (front m g) c ≠ .dead) ∧
          (y.2.val = m + 1 → (next (front m g) c).has y.1 = true) by
        rw [hfront]; exact (H _ h).2 (by simp)
      intro y hy
      induction hy with
      | refl =>
        refine ⟨fun _ => Or.inl ⟨hs, ?_⟩, fun h => by simp at h⟩
        exact Relation.ReflTransGen.refl
      | tail _ hxy ihx =>
        rename_i x y _
        obtain ⟨hadj, hvx, hvy⟩ := hxy
        rcases Nat.lt_or_ge y.2.val (m + 1) with hyl | hyl
        · refine ⟨fun hy' => ?_, fun h => by omega⟩
          rcases Nat.lt_or_ge x.2.val (m + 1) with hxl | hxl
          · rcases ihx.1 hxl with ⟨hg, hp⟩ | hne
            · left
              refine ⟨hg, hp.tail ⟨?_, ?_, ?_⟩⟩
              · rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · left; exact ⟨h1, by simpa using h2⟩
                · right; exact ⟨Fin.ext (by simp [h1]), h2⟩
              · exact hvx
              · exact hvy
            · exact Or.inr hne
          · have hx : x.2.val = m + 1 := by omega
            exact Or.inr (L_ne _ _ _ (ihx.2 hx))
        · have hy : y.2.val = m + 1 := by omega
          have hylast : y.2 = Fin.last (m + 1) := Fin.ext (by simp [hy])
          have hcy : cv c y.1 = true := by
            have := hvy; simp only [val, hylast] at this; exact this
          refine ⟨fun h => by omega, fun _ => ?_⟩
          rcases Nat.lt_or_ge x.2.val (m + 1) with hxl | hxl
          · -- the horizontal entry from column `m`
            have hrow : x.1 = y.1 ∧ x.2.val = m := by
              rcases hadj with ⟨h1, h2⟩ | ⟨h1, _⟩
              · exact ⟨h1, by omega⟩
              · exact absurd (congrArg Fin.val h1) (by omega)
            rcases ihx.1 hxl with ⟨hg, hp⟩ | hne
            · have hlast : (⟨x.2.val, hxl⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp [hrow.2])
              rw [hlast] at hp
              have hfr := (ih g x.1).1 ⟨hg, hp⟩
              rw [← hrow.1]
              exact L_entry _ _ _ hfr (by rw [hrow.1]; exact hcy)
            · exact L_detour _ _ _ hne hcy
          · have hx : x.2.val = m + 1 := by omega
            exact L_vert _ _ x.1 y.1 (ihx.2 hx) hcy
    · intro h
      rw [hfront] at h
      obtain ⟨r0, h0, hc0, hr⟩ := L_back _ _ _ h
      obtain ⟨hg, hp⟩ := (ih g r0).2 h0
      have hs : val f (false, 0) = true := hg
      refine ⟨hs, ?_⟩
      have p1 : Relation.ReflTransGen (stp f) (false, 0) (r0, (Fin.last m).castSucc) := by
        rw [hstart]; exact lift f hp
      have hv0 : val f (r0, (Fin.last m).castSucc) = true := rtg_val p1 hs
      have p2 : Relation.ReflTransGen (stp f) (false, 0) (r0, Fin.last (m + 1)) :=
        p1.tail ⟨Or.inl ⟨rfl, Or.inl (by simp)⟩, hv0, hc0⟩
      rcases hr with rfl | hr
      · exact p2
      · by_cases hrr : r0 = r
        · subst hrr; exact p2
        · exact p2.tail ⟨Or.inr ⟨rfl, hrr⟩, hc0, hr⟩

lemma good_iff (m : ℕ) (f : Arr (m + 1)) : Good f ↔ front m f ≠ .dead := by
  rw [← L_some]
  constructor
  · rintro ⟨_, r, hs, hp⟩
    refine ⟨r, (reach_iff m f r).1 ⟨hs, ?_⟩⟩
    convert hp using 2
  · rintro ⟨r, hr⟩
    obtain ⟨hs, hp⟩ := (reach_iff m f r).2 hr
    refine ⟨by omega, r, hs, ?_⟩
    convert hp using 2

/-! #### Counting by frontier state -/

/-- The number of arrays of width `m + 1` with frontier `s`. -/
def cnt (m : ℕ) (s : St) : ℕ := ∑ f : Arr (m + 1), if front m f = s then 1 else 0

lemma sum_front (m : ℕ) (h : St → ℕ) :
    ∑ f : Arr (m + 1), h (front m f) =
      h .dead * cnt m .dead + h .top * cnt m .top + h .bot * cnt m .bot + h .both * cnt m .both := by
  have e : ∀ f : Arr (m + 1), h (front m f) =
      h .dead * (if front m f = .dead then 1 else 0) + h .top * (if front m f = .top then 1 else 0) +
      h .bot * (if front m f = .bot then 1 else 0) + h .both * (if front m f = .both then 1 else 0) := by
    intro f; cases front m f <;> simp
  simp only [e, sum_add_distrib, ← mul_sum, cnt]

/-- Columns appended at the right. -/
def snocEquiv (m : ℕ) : Arr (m + 1) × (Bool × Bool) ≃ Arr (m + 2) where
  toFun p := Fin.snoc (α := fun _ => Bool × Bool) p.1 p.2
  invFun f := (Fin.init f, f (Fin.last _))
  left_inv p := by simp
  right_inv f := by simp

lemma cnt_succ (m : ℕ) (s' : St) :
    cnt (m + 1) s' = ∑ c : Bool × Bool,
      ((if next .dead c = s' then 1 else 0) * cnt m .dead +
        (if next .top c = s' then 1 else 0) * cnt m .top +
        (if next .bot c = s' then 1 else 0) * cnt m .bot +
        (if next .both c = s' then 1 else 0) * cnt m .both) := by
  unfold cnt
  rw [← Equiv.sum_comp (snocEquiv m), Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun c _ => ?_
  have : ∀ g : Arr (m + 1), front (m + 1) (snocEquiv m (g, c)) = next (front m g) c := by
    intro g; simp [snocEquiv, front]
  simp only [this]
  exact sum_front m (fun s => if next s c = s' then 1 else 0)

lemma cnt_zero : cnt 0 .top = 1 ∧ cnt 0 .bot = 0 ∧ cnt 0 .both = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

lemma cnt_rec (m : ℕ) : cnt (m + 1) .top = cnt m .top + cnt m .both ∧
    cnt (m + 1) .bot = cnt m .bot + cnt m .both ∧
    cnt (m + 1) .both = cnt m .top + cnt m .bot + cnt m .both := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [cnt_succ] <;>
    simp [Fintype.sum_prod_type, next, St.has]

lemma cnt_pell (m : ℕ) : (cnt m .top : ℤ) + cnt m .bot = SqrtTwoOrbit.A (m + 1) ∧
    (cnt m .both : ℤ) = B (m + 1) ∧ (cnt m .top : ℤ) = cnt m .bot + 1 := by
  induction m with
  | zero =>
    obtain ⟨h1, h2, h3⟩ := cnt_zero
    simp only [h1, h2, h3]; decide
  | succ m ih =>
    obtain ⟨r1, r2, r3⟩ := cnt_rec m
    obtain ⟨i1, i2, i3⟩ := ih
    rw [r1, r2, r3, A_succ (m + 1), B_succ (m + 1)]
    push_cast
    refine ⟨by linarith, by linarith, by linarith⟩

/-- **A069306 is a coordinate**: `a(n) = B_{n+1}` (the entry's indices are `n ≥ 2`; the identity
holds from `n = 1`). -/
theorem A069306_eq (n : ℕ) (hn : 1 ≤ n) : (A069306 n : ℤ) = B (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  classical
  have hc : A069306 (m + 1) = cnt m .top + cnt m .bot + cnt m .both := by
    unfold A069306
    rw [card_filter]
    have := sum_front m (fun s => if s ≠ .dead then 1 else 0)
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true, one_mul, not_true_eq_false,
      if_false, zero_mul, zero_add] at this
    rw [← this]
    refine sum_congr rfl fun f _ => ?_
    simp only [good_iff]
  obtain ⟨i1, i2, _⟩ := cnt_pell m
  rw [hc, B_succ (m + 1)]
  push_cast
  linarith

end PerfectPower.SqrtTwoDefs
