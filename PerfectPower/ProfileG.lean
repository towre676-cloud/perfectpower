import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PerfectPower

/-! ### Theorem G, the combinatorial half: `χ = d'(1 - S)` and the exceptional profiles

Theorem G of the research notes has a geometric half (Kummer theory and Riemann–Hurwitz for the
normalisation of `y^d = F(x)`: a component has `d'/t_i` points over `α_i`, `gcd(d', deg F / g)` over
`∞`, `d'` over every other `x`), which stays a paper proof, and a combinatorial half, proved here:

* `S_le_one_iff`: for a profile of positive integers `t_i`, `S = Σ (1 - 1/t_i) ≤ 1` iff at most one
  `t_i` exceeds `1` or the `t_i > 1` are exactly `{2, 2}`, i.e. iff the profile is of power,
  radical or Pell type;
* `chi_eq`: the integer `χ = d' - Σ (d' - d'/t_i)` equals `d'(1 - S)`;
* `profile_table_ok`: for every `2 ≤ d ≤ 12` and every multiplicity profile of degree `≤ 12`
  (the 1 as `F`-degree up to 12 partitions), the Riemann–Hurwitz genus
  `g_C = (2 - n_∞ - χ)/2` is a nonnegative integer, and `χ < 0` exactly for the finite type.
  Checked by the kernel (`decide +kernel`).

`crosscheck/theorem_g_sage.py` independently computes `g_C` and `n_∞` by normalisation in Sage over
the same range (`receipts/theorem_g_check.json`). -/

/-- `S(t) = Σ (1 - 1/t_i)`. -/
def profileS (ts : List ℕ) : ℚ := (ts.map fun t : ℕ => (1 : ℚ) - 1 / (t : ℚ)).sum

/-- Power, radical or Pell profile: at most one `t_i > 1`, or exactly two, both equal to `2`. -/
def exceptionalProfile (ts : List ℕ) : Bool :=
  let big := ts.filter (fun t => 1 < t)
  decide (big.length ≤ 1) || decide (big = [2, 2])

lemma profileS_nil : profileS [] = 0 := rfl

lemma profileS_cons (t : ℕ) (ts : List ℕ) : profileS (t :: ts) = (1 - 1 / (t : ℚ)) + profileS ts := by
  simp only [profileS, List.map_cons, List.sum_cons]

lemma profileS_filter (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) :
    profileS ts = profileS (ts.filter fun t => 1 < t) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have ht := hpos t (by simp)
    have ih' := ih fun s hs => hpos s (by simp [hs])
    by_cases h : 1 < t
    · rw [List.filter_cons_of_pos (by simpa using h), profileS_cons, profileS_cons, ih']
    · have : t = 1 := by omega
      rw [List.filter_cons_of_neg (by simpa using h), profileS_cons, ih', this]
      norm_num

/-- A term with `t ≥ 2` lies in `[1/2, 1)`. -/
lemma term_bounds {t : ℕ} (ht : 1 < t) : 1 / 2 ≤ 1 - 1 / (t : ℚ) ∧ 1 - 1 / (t : ℚ) < 1 := by
  have ht' : (2 : ℚ) ≤ t := by exact_mod_cast ht
  have h1 : 1 / (t : ℚ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) ht'
  have h2 : 0 < 1 / (t : ℚ) := by positivity
  constructor <;> linarith

lemma profileS_ge (ts : List ℕ) (hbig : ∀ t ∈ ts, 1 < t) : (ts.length : ℚ) / 2 ≤ profileS ts := by
  induction ts with
  | nil => simp [profileS_nil]
  | cons t ts ih =>
    rw [profileS_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have := (term_bounds (hbig t (by simp))).1
    have := ih fun s hs => hbig s (by simp [hs])
    linarith

/-- The two-element case: `(1 - 1/a) + (1 - 1/b) ≤ 1` iff `a = b = 2`. -/
lemma two_case {a b : ℕ} (ha : 1 < a) (hb : 1 < b) :
    (1 - 1 / (a : ℚ)) + ((1 - 1 / (b : ℚ)) + 0) ≤ 1 ↔ a = 2 ∧ b = 2 := by
  constructor
  · intro h
    have ha2 := (term_bounds ha).1
    have hb2 := (term_bounds hb).1
    rcases Nat.lt_or_ge a 3 with h3 | h3
    · rcases Nat.lt_or_ge b 3 with h4 | h4
      · exact ⟨by omega, by omega⟩
      · have : 1 / (b : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h4)
        linarith
    · have : 1 / (a : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h3)
      linarith
  · rintro ⟨rfl, rfl⟩; norm_num

/-- **The exceptional profiles.** -/
theorem S_le_one_iff (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) :
    profileS ts ≤ 1 ↔ exceptionalProfile ts = true := by
  rw [profileS_filter ts hpos]
  simp only [exceptionalProfile, Bool.or_eq_true, decide_eq_true_eq]
  have hbig : ∀ t ∈ ts.filter (fun t => 1 < t), 1 < t := fun t ht => by
    simpa using (List.mem_filter.mp ht).2
  generalize ts.filter (fun t => 1 < t) = big at hbig ⊢
  rcases big with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [profileS_nil]
  · have := (term_bounds (hbig a (by simp))).2
    simp only [profileS_cons, profileS_nil, List.length_singleton, le_refl, true_or, iff_true]
    linarith
  · rw [profileS_cons, profileS_cons, profileS_nil,
      two_case (hbig a (by simp)) (hbig b (by simp))]
    simp
  · have h := profileS_ge _ hbig
    simp only [List.length_cons] at h
    push_cast at h
    constructor
    · intro h'; nlinarith [show (0 : ℚ) ≤ rest.length by positivity]
    · rintro (h' | h')
      · simp at h'
      · simp at h'

/-- `t_i = d / gcd(d, r_i)`. -/
def tOf (d r : ℕ) : ℕ := d / Nat.gcd d r

/-- `g = gcd(d, r_1, …, r_s)`. -/
def gOf (d : ℕ) (rs : List ℕ) : ℕ := rs.foldl Nat.gcd d

/-- `χ = d' - Σ (d' - d'/t_i)`, an integer. -/
def chiInt (d : ℕ) (rs : List ℕ) : ℤ :=
  let dp := d / gOf d rs
  (dp : ℤ) - (rs.map fun r => ((dp : ℤ) - ((dp / tOf d r : ℕ) : ℤ))).sum

/-- `n_∞ = gcd(d', deg F / g)`. -/
def nInf (d : ℕ) (rs : List ℕ) : ℕ := Nat.gcd (d / gOf d rs) (rs.sum / gOf d rs)

/-- The Riemann–Hurwitz genus is a nonnegative integer, and `χ < 0` iff the profile is not
exceptional (and `χ = d'(1 - S)` holds in exact arithmetic, `S` from the `t_i`). -/
def rowOK (d : ℕ) (rs : List ℕ) : Bool :=
  let χ := chiInt d rs
  let twoG := 2 - (nInf d rs : ℤ) - χ
  let ts := rs.map (tOf d)
  let dp := d / gOf d rs
  decide (0 ≤ twoG) && decide (twoG % 2 = 0) &&
    ((decide (χ < 0)) == !exceptionalProfile ts) &&
    (ts.all fun t => decide (t ∣ dp)) &&
    decide ((χ : ℚ) = dp * (1 - profileS ts))

set_option maxRecDepth 20000

/-- All multiplicity profiles of total degree `1, …, 12` (partitions, largest part first). -/
def profiles12 : List (List ℕ) := [
  [1],
  [2],
  [1, 1],
  [3],
  [2, 1],
  [1, 1, 1],
  [4],
  [3, 1],
  [2, 2],
  [2, 1, 1],
  [1, 1, 1, 1],
  [5],
  [4, 1],
  [3, 2],
  [3, 1, 1],
  [2, 2, 1],
  [2, 1, 1, 1],
  [1, 1, 1, 1, 1],
  [6],
  [5, 1],
  [4, 2],
  [4, 1, 1],
  [3, 3],
  [3, 2, 1],
  [3, 1, 1, 1],
  [2, 2, 2],
  [2, 2, 1, 1],
  [2, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1],
  [7],
  [6, 1],
  [5, 2],
  [5, 1, 1],
  [4, 3],
  [4, 2, 1],
  [4, 1, 1, 1],
  [3, 3, 1],
  [3, 2, 2],
  [3, 2, 1, 1],
  [3, 1, 1, 1, 1],
  [2, 2, 2, 1],
  [2, 2, 1, 1, 1],
  [2, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1],
  [8],
  [7, 1],
  [6, 2],
  [6, 1, 1],
  [5, 3],
  [5, 2, 1],
  [5, 1, 1, 1],
  [4, 4],
  [4, 3, 1],
  [4, 2, 2],
  [4, 2, 1, 1],
  [4, 1, 1, 1, 1],
  [3, 3, 2],
  [3, 3, 1, 1],
  [3, 2, 2, 1],
  [3, 2, 1, 1, 1],
  [3, 1, 1, 1, 1, 1],
  [2, 2, 2, 2],
  [2, 2, 2, 1, 1],
  [2, 2, 1, 1, 1, 1],
  [2, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1],
  [9],
  [8, 1],
  [7, 2],
  [7, 1, 1],
  [6, 3],
  [6, 2, 1],
  [6, 1, 1, 1],
  [5, 4],
  [5, 3, 1],
  [5, 2, 2],
  [5, 2, 1, 1],
  [5, 1, 1, 1, 1],
  [4, 4, 1],
  [4, 3, 2],
  [4, 3, 1, 1],
  [4, 2, 2, 1],
  [4, 2, 1, 1, 1],
  [4, 1, 1, 1, 1, 1],
  [3, 3, 3],
  [3, 3, 2, 1],
  [3, 3, 1, 1, 1],
  [3, 2, 2, 2],
  [3, 2, 2, 1, 1],
  [3, 2, 1, 1, 1, 1],
  [3, 1, 1, 1, 1, 1, 1],
  [2, 2, 2, 2, 1],
  [2, 2, 2, 1, 1, 1],
  [2, 2, 1, 1, 1, 1, 1],
  [2, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1],
  [10],
  [9, 1],
  [8, 2],
  [8, 1, 1],
  [7, 3],
  [7, 2, 1],
  [7, 1, 1, 1],
  [6, 4],
  [6, 3, 1],
  [6, 2, 2],
  [6, 2, 1, 1],
  [6, 1, 1, 1, 1],
  [5, 5],
  [5, 4, 1],
  [5, 3, 2],
  [5, 3, 1, 1],
  [5, 2, 2, 1],
  [5, 2, 1, 1, 1],
  [5, 1, 1, 1, 1, 1],
  [4, 4, 2],
  [4, 4, 1, 1],
  [4, 3, 3],
  [4, 3, 2, 1],
  [4, 3, 1, 1, 1],
  [4, 2, 2, 2],
  [4, 2, 2, 1, 1],
  [4, 2, 1, 1, 1, 1],
  [4, 1, 1, 1, 1, 1, 1],
  [3, 3, 3, 1],
  [3, 3, 2, 2],
  [3, 3, 2, 1, 1],
  [3, 3, 1, 1, 1, 1],
  [3, 2, 2, 2, 1],
  [3, 2, 2, 1, 1, 1],
  [3, 2, 1, 1, 1, 1, 1],
  [3, 1, 1, 1, 1, 1, 1, 1],
  [2, 2, 2, 2, 2],
  [2, 2, 2, 2, 1, 1],
  [2, 2, 2, 1, 1, 1, 1],
  [2, 2, 1, 1, 1, 1, 1, 1],
  [2, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [11],
  [10, 1],
  [9, 2],
  [9, 1, 1],
  [8, 3],
  [8, 2, 1],
  [8, 1, 1, 1],
  [7, 4],
  [7, 3, 1],
  [7, 2, 2],
  [7, 2, 1, 1],
  [7, 1, 1, 1, 1],
  [6, 5],
  [6, 4, 1],
  [6, 3, 2],
  [6, 3, 1, 1],
  [6, 2, 2, 1],
  [6, 2, 1, 1, 1],
  [6, 1, 1, 1, 1, 1],
  [5, 5, 1],
  [5, 4, 2],
  [5, 4, 1, 1],
  [5, 3, 3],
  [5, 3, 2, 1],
  [5, 3, 1, 1, 1],
  [5, 2, 2, 2],
  [5, 2, 2, 1, 1],
  [5, 2, 1, 1, 1, 1],
  [5, 1, 1, 1, 1, 1, 1],
  [4, 4, 3],
  [4, 4, 2, 1],
  [4, 4, 1, 1, 1],
  [4, 3, 3, 1],
  [4, 3, 2, 2],
  [4, 3, 2, 1, 1],
  [4, 3, 1, 1, 1, 1],
  [4, 2, 2, 2, 1],
  [4, 2, 2, 1, 1, 1],
  [4, 2, 1, 1, 1, 1, 1],
  [4, 1, 1, 1, 1, 1, 1, 1],
  [3, 3, 3, 2],
  [3, 3, 3, 1, 1],
  [3, 3, 2, 2, 1],
  [3, 3, 2, 1, 1, 1],
  [3, 3, 1, 1, 1, 1, 1],
  [3, 2, 2, 2, 2],
  [3, 2, 2, 2, 1, 1],
  [3, 2, 2, 1, 1, 1, 1],
  [3, 2, 1, 1, 1, 1, 1, 1],
  [3, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 2, 2, 2, 2, 1],
  [2, 2, 2, 2, 1, 1, 1],
  [2, 2, 2, 1, 1, 1, 1, 1],
  [2, 2, 1, 1, 1, 1, 1, 1, 1],
  [2, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [12],
  [11, 1],
  [10, 2],
  [10, 1, 1],
  [9, 3],
  [9, 2, 1],
  [9, 1, 1, 1],
  [8, 4],
  [8, 3, 1],
  [8, 2, 2],
  [8, 2, 1, 1],
  [8, 1, 1, 1, 1],
  [7, 5],
  [7, 4, 1],
  [7, 3, 2],
  [7, 3, 1, 1],
  [7, 2, 2, 1],
  [7, 2, 1, 1, 1],
  [7, 1, 1, 1, 1, 1],
  [6, 6],
  [6, 5, 1],
  [6, 4, 2],
  [6, 4, 1, 1],
  [6, 3, 3],
  [6, 3, 2, 1],
  [6, 3, 1, 1, 1],
  [6, 2, 2, 2],
  [6, 2, 2, 1, 1],
  [6, 2, 1, 1, 1, 1],
  [6, 1, 1, 1, 1, 1, 1],
  [5, 5, 2],
  [5, 5, 1, 1],
  [5, 4, 3],
  [5, 4, 2, 1],
  [5, 4, 1, 1, 1],
  [5, 3, 3, 1],
  [5, 3, 2, 2],
  [5, 3, 2, 1, 1],
  [5, 3, 1, 1, 1, 1],
  [5, 2, 2, 2, 1],
  [5, 2, 2, 1, 1, 1],
  [5, 2, 1, 1, 1, 1, 1],
  [5, 1, 1, 1, 1, 1, 1, 1],
  [4, 4, 4],
  [4, 4, 3, 1],
  [4, 4, 2, 2],
  [4, 4, 2, 1, 1],
  [4, 4, 1, 1, 1, 1],
  [4, 3, 3, 2],
  [4, 3, 3, 1, 1],
  [4, 3, 2, 2, 1],
  [4, 3, 2, 1, 1, 1],
  [4, 3, 1, 1, 1, 1, 1],
  [4, 2, 2, 2, 2],
  [4, 2, 2, 2, 1, 1],
  [4, 2, 2, 1, 1, 1, 1],
  [4, 2, 1, 1, 1, 1, 1, 1],
  [4, 1, 1, 1, 1, 1, 1, 1, 1],
  [3, 3, 3, 3],
  [3, 3, 3, 2, 1],
  [3, 3, 3, 1, 1, 1],
  [3, 3, 2, 2, 2],
  [3, 3, 2, 2, 1, 1],
  [3, 3, 2, 1, 1, 1, 1],
  [3, 3, 1, 1, 1, 1, 1, 1],
  [3, 2, 2, 2, 2, 1],
  [3, 2, 2, 2, 1, 1, 1],
  [3, 2, 2, 1, 1, 1, 1, 1],
  [3, 2, 1, 1, 1, 1, 1, 1, 1],
  [3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 2, 2, 2, 2, 2],
  [2, 2, 2, 2, 2, 1, 1],
  [2, 2, 2, 2, 1, 1, 1, 1],
  [2, 2, 2, 1, 1, 1, 1, 1, 1],
  [2, 2, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

theorem profiles12_length : profiles12.length = 271 := by decide +kernel

/-- **Exhaustive table.** Every `2 ≤ d ≤ 12` and every profile of degree `≤ 12` passes `rowOK`. -/
theorem profile_table_ok :
    ((List.range' 2 11).all fun d => profiles12.all fun rs => rowOK d rs) = true := by
  decide +kernel

end PerfectPower
