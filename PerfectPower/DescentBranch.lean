import PerfectPower.Descent

/-!
# A finite, exhaustive branch compiler for `y^2 = x^3 - D`

`Descent.lean` requires every table entry `p^2 + D q^2 = k^3` to be a rational cube `± j^3`
together with a residue check (integral closedness at `j`).  That refuses, among others,
`y^2 = x^3 - 1`, where the entries are the units `± i` and `2 + 2i`.  Here the requirement is
replaced by an exhaustive treatment of **every** entry.

**Every point enters a branch.**  `ClassTwo.short_relation` (Thue's lemma on the lattice
`x ∣ a - y b`) gives, for every solution, `a, b` and an entry `(k, p, q)` of the finite table
(`1 ≤ k ≤ K`, `|q| ≤ Q`) with

  `k^3 (y + s) = (p + q s) (a + b s)^3`,  `s = √-D`,

in coordinates `k^3 y = p W1 + D q W2`, `k^3 = q W1 - p W2`.  Nothing assumes that `y + s` and
`y - s` are coprime, that the ring is maximal, that units are `± 1`, or anything about the class
number: common factors, conductors and units all appear as table entries.

**Each entry is closed, one of two ways** (`entryB`):
* **field cube** (`cubeB`): `g^3 (p + q s) = (c + d s)^3` with `g ≥ 1`.  This covers the Gaussian
  units (`i = (-i)^3`), element cubes (`2 + 2i = (i - 1)^3`), and cubes of non-integral elements
  such as `(c + d s)/2`.  With `A + B s = (c + d s)(a + b s)` the branch is
  `g^3 k^3 (y + s) = (A + B s)^3`, so `B (3 A^2 - D B^2) = n^3` (`n = g k`): the cubic is
  **reducible**, `|B|` is a product of three divisors of `n`, `A^2` is then determined, and every
  `y` of the branch is in the explicit list `divYs D n` (`divYs_complete`), which must lie in the
  certificate's candidate list `Ys`.
* **local obstruction** (`modB`): `q W1 - p W2 ≠ k^3` modulo `m` for all residues.

**Every accepted candidate returns to the curve**: the final list keeps `(x, y)` only when
`y^2 + D = x^3` exactly (`pointsB`).

`complete_of_branch`: the integral points of `y^2 = x^3 - D` are exactly the listed points.
An entry that is neither a field cube nor locally impossible is an irreducible Thue equation;
the checker then fails and nothing is claimed.
-/

namespace PerfectPower.DescentBranch

open PerfectPower ClassTwo

/-! ### Divisor enumeration for the reducible branches -/

/-- The positive divisors of `n`. -/
def divs (n : ℕ) : List ℕ := (List.range (n + 1)).filter fun d => decide (0 < d) && n % d == 0

lemma mem_divs {n d : ℕ} (hn : 0 < n) (h : d ∣ n) : d ∈ divs n := by
  simp only [divs, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hn h), Nat.pos_of_dvd_of_pos h hn,
    Nat.mod_eq_zero_of_dvd h⟩

/-- The values `y` with `M y = A^3 - 3 D A B^2`, `B (3 A^2 - D B^2) = M`, for one `B`;
`none` when the square-root bracket check fails. -/
def ysOf (D M B : ℤ) : Option (List ℤ) :=
  if B = 0 then some [] else
  if M % B ≠ 0 then some [] else
  let t := M / B + D * B ^ 2
  if t % 3 ≠ 0 then some [] else
  let u := t / 3
  if u < 0 then some [] else
  let r := isqrtZ u
  if ¬ (0 ≤ r ∧ r * r ≤ u ∧ u < (r + 1) * (r + 1)) then none else
  if r * r ≠ u then some [] else
  some ([r, -r].filterMap fun A =>
    if (A ^ 3 - 3 * D * A * B ^ 2) % M = 0 then some ((A ^ 3 - 3 * D * A * B ^ 2) / M) else none)

/-- Every branch value for `n`, checked to lie in `Ys`. -/
def divYsB (D : ℤ) (n : ℕ) (Ys : List ℤ) : Bool :=
  (divs n).all fun d1 => (divs n).all fun d2 => (divs n).all fun d3 =>
    !decide (d1 ≤ d2 ∧ d2 ≤ d3) || [(1 : ℤ), -1].all fun σ =>
      match ysOf D ((n : ℤ) ^ 3) (σ * d1 * d2 * d3) with
      | none => false
      | some l => l.all fun y => decide (y ∈ Ys)

lemma sq_bracket {A r : ℤ} (hr : 0 ≤ r) (h1 : r * r ≤ A ^ 2) (h2 : A ^ 2 < (r + 1) * (r + 1)) :
    r * r = A ^ 2 := by
  have habs : |A| ^ 2 = A ^ 2 := sq_abs A
  have e1 : r ≤ |A| := by
    by_contra hc; push_neg at hc
    have : |A| * |A| < r * r := mul_self_lt_mul_self (abs_nonneg A) hc
    nlinarith
  have e2 : |A| < r + 1 := by
    by_contra hc; push_neg at hc
    have : (r + 1) * (r + 1) ≤ |A| * |A| := mul_self_le_mul_self (by linarith) hc
    nlinarith
  have : r = |A| := by omega
  rw [this, ← habs]; ring

/-- What `ysOf` lists: every `y` of the branch for this `B`. -/
lemma ysOf_spec {D M B A y : ℤ} {l : List ℤ} (hM : 0 < M) (h1 : B * (3 * A ^ 2 - D * B ^ 2) = M)
    (h2 : M * y = A ^ 3 - 3 * D * A * B ^ 2) (h : ysOf D M B = some l) : y ∈ l := by
  have hB0 : B ≠ 0 := by rintro rfl; simp at h1; omega
  have hdivM : M % B = 0 := Int.emod_eq_zero_of_dvd ⟨_, h1.symm⟩
  have ht : M / B + D * B ^ 2 = 3 * A ^ 2 := by
    rw [← h1, Int.mul_ediv_cancel_left _ hB0]; ring
  have hu : 3 * A ^ 2 / 3 = A ^ 2 := by omega
  simp only [ysOf, ht, hu] at h
  split_ifs at h with c1 c2 c3 c4 c5 c6
  · exact absurd c1 hB0
  · exact absurd hdivM c2
  · omega
  · nlinarith [sq_nonneg A]
  · exact absurd (sq_bracket c5.1 c5.2.1 c5.2.2) c6
  · simp only [Option.some.injEq] at h
    subst h
    generalize isqrtZ (A ^ 2) = r at c5 c6 ⊢
    have hrr := sq_bracket c5.1 c5.2.1 c5.2.2
    have hA : A = r ∨ A = -r := by
      have : A ^ 2 = r ^ 2 := by rw [← hrr]; ring
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    have hnum : (A ^ 3 - 3 * D * A * B ^ 2) % M = 0 := Int.emod_eq_zero_of_dvd ⟨y, h2.symm⟩
    have hval : (A ^ 3 - 3 * D * A * B ^ 2) / M = y := by
      rw [← h2, Int.mul_ediv_cancel_left _ hM.ne']
    rw [List.mem_filterMap]
    refine ⟨A, ?_, ?_⟩
    · rcases hA with h | h <;> rw [h] <;> simp
    · simp only [hnum, if_true, hval]

lemma sort3 (d1 d2 d3 : ℕ) : ∃ f1 f2 f3 : ℕ, f1 ≤ f2 ∧ f2 ≤ f3 ∧ f1 * f2 * f3 = d1 * d2 * d3 ∧
    (f1 = d1 ∨ f1 = d2 ∨ f1 = d3) ∧ (f2 = d1 ∨ f2 = d2 ∨ f2 = d3) ∧ (f3 = d1 ∨ f3 = d2 ∨ f3 = d3) := by
  rcases le_total d1 d2 with h12 | h12 <;> rcases le_total d2 d3 with h23 | h23 <;>
    rcases le_total d1 d3 with h13 | h13
  all_goals first
    | exact ⟨d1, d2, d3, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨d1, d3, d2, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨d2, d1, d3, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨d2, d3, d1, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨d3, d1, d2, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨d3, d2, d1, by omega, by omega, by ring, by simp, by simp, by simp⟩

/-- **The reducible branch is finite and listed.** -/
theorem divYs_complete (D : ℤ) (n : ℕ) (hn : 0 < n) (Ys : List ℤ) (hB : divYsB D n Ys = true)
    (A B y : ℤ) (h1 : B * (3 * A ^ 2 - D * B ^ 2) = (n : ℤ) ^ 3)
    (h2 : (n : ℤ) ^ 3 * y = A ^ 3 - 3 * D * A * B ^ 2) : y ∈ Ys := by
  have hM : (0 : ℤ) < (n : ℤ) ^ 3 := by positivity
  have hB0 : B ≠ 0 := by rintro rfl; simp at h1; exact absurd h1.symm hM.ne'
  -- `|B|` is a product of three divisors of `n`
  have hdvd : B.natAbs ∣ n * (n * n) := by
    have h3 : B.natAbs ∣ ((n : ℤ) ^ 3).natAbs := Int.natAbs_dvd_natAbs.mpr ⟨_, h1.symm⟩
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h3
    rwa [show n ^ 3 = n * (n * n) by ring] at h3
  obtain ⟨d1, e, hd1, he, hde⟩ := (dvd_mul (k := B.natAbs)).mp hdvd
  obtain ⟨d2, d3, hd2, hd3, he'⟩ := (dvd_mul (k := e)).mp he
  -- sort the three divisors
  obtain ⟨f1, f2, f3, hs1, hs2, hprod, hf1, hf2, hf3⟩ := sort3 d1 d2 d3
  have hin : ∀ f, (f = d1 ∨ f = d2 ∨ f = d3) → f ∈ divs n := by
    rintro f (rfl | rfl | rfl)
    exacts [mem_divs hn hd1, mem_divs hn hd2, mem_divs hn hd3]
  have m1 := hin f1 hf1
  have m2 := hin f2 hf2
  have m3 := hin f3 hf3
  obtain ⟨σ, hσ, hBσ⟩ : ∃ σ : ℤ, σ ∈ [(1 : ℤ), -1] ∧ B = σ * f1 * f2 * f3 := by
    have hnat : (B.natAbs : ℤ) = (f1 : ℤ) * f2 * f3 := by
      rw [hde, he']; push_cast; rw [← mul_assoc]; exact_mod_cast hprod.symm
    rcases Int.natAbs_eq B with h | h
    · exact ⟨1, by simp, by rw [h, hnat]; ring⟩
    · exact ⟨-1, by simp, by rw [h, hnat]; ring⟩
  simp only [divYsB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hB
  have hl := (hB f1 m1 f2 m2 f3 m3).resolve_left (by push_neg; exact ⟨hs1, hs2⟩) σ hσ
  rw [← hBσ] at hl
  cases hys : ysOf D ((n : ℤ) ^ 3) B with
  | none => rw [hys] at hl; simp at hl
  | some l =>
    rw [hys] at hl
    simp only [List.all_eq_true, decide_eq_true_eq] at hl
    exact hl y (ysOf_spec hM h1 h2 hys)

/-! ### The entries -/

/-- A field-cube verdict: `g^3 (p + q s) = (c + d s)^3`, and the branch values lie in `Ys`. -/
def cubeB (D k p q c d g : ℤ) (Ys : List ℤ) : Bool :=
  decide (0 < g) && decide (0 < k) &&
    decide (c ^ 3 - 3 * D * c * d ^ 2 = g ^ 3 * p) && decide (3 * c ^ 2 * d - D * d ^ 3 = g ^ 3 * q) &&
    divYsB D (g * k).toNat Ys

/-- A local verdict: `q W1(a, b) - p W2(a, b) ≠ k^3` modulo `m` for all residues. -/
def modB (D k p q : ℤ) (m : ℕ) : Bool :=
  decide (0 < m) && (List.range m).all fun a => (List.range m).all fun b =>
    decide ((q * W1 D a b - p * W2 D a b - k ^ 3) % (m : ℤ) ≠ 0)

/-- The verdict lists: `cubes` holds `(k, p, q, c, d, g)`, `mods` holds `(k, p, q, m)`. -/
def entryB (D k p q : ℤ) (cubes : List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ)) (mods : List (ℤ × ℤ × ℤ × ℕ))
    (Ys : List ℤ) : Bool :=
  cubes.any (fun e => decide (e.1 = k ∧ e.2.1 = p ∧ e.2.2.1 = q) &&
      cubeB D k p q e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2 Ys) ||
    mods.any fun e => decide (e.1 = k ∧ e.2.1 = p ∧ e.2.2.1 = q) && modB D k p q e.2.2.2

/-- **The branch certificate**: every table entry `p^2 + D q^2 = k^3` (`1 ≤ k ≤ K`, `|q| ≤ Q`,
both signs of `p`) has a verdict.  Square roots are verified by their bracket. -/
def branchB (D : ℤ) (K Q : ℕ) (cubes : List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ)) (mods : List (ℤ × ℤ × ℤ × ℕ))
    (Ys : List ℤ) : Bool :=
  (List.range K).all fun i => (List.range (2 * Q + 1)).all fun iq =>
    let k : ℤ := (i : ℤ) + 1
    let q : ℤ := (iq : ℤ) - Q
    let t := k ^ 3 - D * q ^ 2
    let s := isqrtZ t
    decide (t < 0) ||
      (decide (0 ≤ s ∧ s * s ≤ t ∧ t < (s + 1) * (s + 1)) &&
        (!decide (s * s = t) ||
          (entryB D k s q cubes mods Ys && entryB D k (-s) q cubes mods Ys)))

lemma branch_entry {D : ℤ} {K Q : ℕ} {cubes mods Ys} (h : branchB D K Q cubes mods Ys = true)
    (k q p : ℤ) (hk1 : 1 ≤ k) (hkK : k ≤ K) (hq : |q| ≤ Q) (hp : p ^ 2 + D * q ^ 2 = k ^ 3) :
    entryB D k p q cubes mods Ys = true := by
  unfold branchB at h
  rw [List.all_eq_true] at h
  have hi : (k - 1).toNat ∈ List.range K := by rw [List.mem_range]; omega
  have hq' := abs_le.mp hq
  have hiq : (q + Q).toNat ∈ List.range (2 * Q + 1) := by rw [List.mem_range]; omega
  have h' := (List.all_eq_true.mp (h _ hi)) _ hiq
  have hkc : (((k - 1).toNat : ℕ) : ℤ) + 1 = k := by omega
  have hqc : (((q + Q).toNat : ℕ) : ℤ) - Q = q := by omega
  simp only [hkc, hqc] at h'
  have ht : k ^ 3 - D * q ^ 2 = p ^ 2 := by linarith
  rw [ht] at h'
  generalize isqrtZ (p ^ 2) = s at h'
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h'
  rcases h' with hneg | ⟨⟨hs0, hs1, hs2⟩, hrest⟩
  · nlinarith [sq_nonneg p]
  have hsp : s * s = p ^ 2 := sq_bracket hs0 hs1 hs2
  rcases hrest with hns | ⟨e1, e2⟩
  · exact absurd hsp hns
  have : p = s ∨ p = -s := by
    have : p ^ 2 = s ^ 2 := by rw [← hsp]; ring
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  rcases this with rfl | rfl
  · exact e1
  · simpa using e2

/-! ### Soundness of the verdicts -/

lemma W_mod {D a b a' b' : ℤ} {m : ℤ} (ha : a ≡ a' [ZMOD m]) (hb : b ≡ b' [ZMOD m]) (p q k : ℤ) :
    q * W1 D a b - p * W2 D a b - k ^ 3 ≡ q * W1 D a' b' - p * W2 D a' b' - k ^ 3 [ZMOD m] :=
  (((Int.ModEq.refl q).mul (Descent.W1_modEq ha hb)).sub
    ((Int.ModEq.refl p).mul (Descent.W2_modEq ha hb))).sub (Int.ModEq.refl _)

lemma mod_sound {D k p q : ℤ} {m : ℕ} (h : modB D k p q m = true) (a b : ℤ) :
    q * W1 D a b - p * W2 D a b ≠ k ^ 3 := by
  intro he
  simp only [modB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hm, hall⟩ := h
  have hM : (0 : ℤ) < m := by exact_mod_cast hm
  have hA0 := Int.emod_nonneg a hM.ne'
  have hA1 := Int.emod_lt_of_pos a hM
  have hB0 := Int.emod_nonneg b hM.ne'
  have hB1 := Int.emod_lt_of_pos b hM
  have hAc : (((a % m).toNat : ℕ) : ℤ) = a % m := Int.toNat_of_nonneg hA0
  have hBc : (((b % m).toNat : ℕ) : ℤ) = b % m := Int.toNat_of_nonneg hB0
  have h' := hall (a % m).toNat (by omega) (b % m).toNat (by omega)
  rw [hAc, hBc] at h'
  apply h'
  have := W_mod (D := D) (Int.mod_modEq a m) (Int.mod_modEq b m) p q k
  rw [he, sub_self] at this
  simpa [Int.ModEq] using this

/-- The branch relation of a field-cube entry. -/
lemma cube_branch {D k p q c d g a b y : ℤ}
    (hc1 : c ^ 3 - 3 * D * c * d ^ 2 = g ^ 3 * p) (hc2 : 3 * c ^ 2 * d - D * d ^ 3 = g ^ 3 * q)
    (hre : k ^ 3 * y = p * W1 D a b + D * q * W2 D a b)
    (him : k ^ 3 = q * W1 D a b - p * W2 D a b) :
    (c * b + d * a) * (3 * (c * a - D * d * b) ^ 2 - D * (c * b + d * a) ^ 2) = (g * k) ^ 3 ∧
      (g * k) ^ 3 * y = (c * a - D * d * b) ^ 3 - 3 * D * (c * a - D * d * b) * (c * b + d * a) ^ 2 := by
  constructor
  · have : (g * k) ^ 3 = g ^ 3 * (q * W1 D a b - p * W2 D a b) := by rw [← him]; ring
    rw [this]
    simp only [W1, W2]
    linear_combination (a ^ 3 - 3 * D * a * b ^ 2) * hc2 - (D * b ^ 3 - 3 * a ^ 2 * b) * hc1
  · have : (g * k) ^ 3 * y = g ^ 3 * (p * W1 D a b + D * q * W2 D a b) := by
      rw [← hre]; ring
    rw [this]
    simp only [W1, W2]
    linear_combination (-(a ^ 3 - 3 * D * a * b ^ 2)) * hc1 - D * (D * b ^ 3 - 3 * a ^ 2 * b) * hc2

/-- **Every solution's `y` is a candidate.** -/
theorem y_mem (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K Q : ℕ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < ((K : ℤ) + 1) * r * t)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (cubes mods Ys)
    (hcert : branchB D K Q cubes mods Ys = true) (x y : ℤ) (h : y ^ 2 + D = x ^ 3) : y ∈ Ys := by
  have hx : 0 < x := by
    by_contra hc
    push_neg at hc
    have : x ^ 3 ≤ 0 := Odd.pow_nonpos (⟨1, rfl⟩ : Odd 3) hc
    nlinarith [sq_nonneg y]
  obtain ⟨a, b, k, e1, e2, hk1, hkK, hnorm, hre, him⟩ :=
    short_relation D hD r t hr ht K hK x y h hx
  have hk3 : k ^ 3 ≤ (K : ℤ) ^ 3 := pow_le_pow_left₀ (by linarith) hkK 3
  have hq : |e2| ≤ Q := by
    have h1 : D * e2 ^ 2 < D * ((Q : ℤ) + 1) ^ 2 := by nlinarith [sq_nonneg e1]
    have h2 : e2 ^ 2 < ((Q : ℤ) + 1) ^ 2 := lt_of_mul_lt_mul_left h1 hD.le
    have h3 := abs_lt_of_sq_lt_sq' h2 (by positivity)
    rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
  have hent := branch_entry hcert k e2 e1 hk1 hkK hq hnorm
  have hre' : k ^ 3 * y = e1 * W1 D a b + D * e2 * W2 D a b := by linarith
  have him' : k ^ 3 = e2 * W1 D a b - e1 * W2 D a b := by linarith
  simp only [entryB, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hent
  rcases hent with ⟨⟨k', p', q', c, d, g⟩, -, ⟨e1', e2', e3'⟩, hcube⟩ | ⟨⟨k', p', q', m⟩, -, ⟨e1', e2', e3'⟩, hmod⟩
  · dsimp only at e1' e2' e3' hcube
    subst e1' e2' e3'
    simp only [cubeB, Bool.and_eq_true, decide_eq_true_eq] at hcube
    obtain ⟨⟨⟨⟨hg, -⟩, hc1⟩, hc2⟩, hdiv⟩ := hcube
    obtain ⟨b1, b2⟩ := cube_branch (a := a) (b := b) (y := y) hc1 hc2 hre' him'
    have hgk : 0 < g * k' := by positivity
    have hn : (((g * k').toNat : ℕ) : ℤ) = g * k' := Int.toNat_of_nonneg hgk.le
    refine divYs_complete D (g * k').toNat (by omega) Ys hdiv (c * a - D * d * b) (c * b + d * a) y ?_ ?_
    · rw [hn]; exact b1
    · rw [hn]; exact b2
  · dsimp only at e1' e2' e3' hmod
    subst e1' e2' e3'
    exact absurd him'.symm (mod_sound hmod a b)

/-! ### From candidates to the complete list -/

/-- Integer cube root of `v ≥ 0` by bisection (never trusted: `pointsB` checks a bracket). -/
def cbrtAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, lo, _ => lo
  | fuel + 1, v, lo, hi =>
    if hi ≤ lo + 1 then lo else
    let mid := (lo + hi) / 2
    if mid ^ 3 ≤ v then cbrtAux fuel v mid hi else cbrtAux fuel v lo mid

/-- `⌊v^{1/3}⌋` for `0 ≤ v < 2^600` (checked by the caller). -/
def cbrtZ (v : ℤ) : ℤ := (cbrtAux 700 v.toNat 0 (v.toNat + 1) : ℤ)

/-- The candidate list is exhausted: for every `y ∈ Ys`, `c = ⌊(y^2 + D)^{1/3}⌋` is verified by its
bracket, and `(c, y) ∈ P` whenever `c^3 = y^2 + D`; every listed point is on the curve. -/
def pointsB (D : ℤ) (Ys : List ℤ) (P : List (ℤ × ℤ)) : Bool :=
  Ys.all (fun y =>
    let v := y ^ 2 + D
    let c := cbrtZ v
    decide (0 ≤ c ∧ c ^ 3 ≤ v ∧ v < (c + 1) ^ 3) && (!decide (c ^ 3 = v) || decide ((c, y) ∈ P))) &&
  P.all fun pt => decide (pt.2 ^ 2 = pt.1 ^ 3 - D)

/-- **The complete list of integral points of `y^2 = x^3 - D`, from a branch certificate.** -/
theorem complete_of_branch (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K Q : ℕ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < ((K : ℤ) + 1) * r * t)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (cubes mods Ys) (P : List (ℤ × ℤ))
    (hcert : branchB D K Q cubes mods Ys = true) (hpts : pointsB D Ys P = true) (x y : ℤ) :
    y ^ 2 = x ^ 3 - D ↔ (x, y) ∈ P := by
  simp only [pointsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at hpts
  obtain ⟨hY, hP⟩ := hpts
  constructor
  · intro h
    have hy := y_mem D hD r t hr ht K Q hK hQ cubes mods Ys hcert x y (by linarith)
    obtain ⟨⟨hc0, hc1, hc2⟩, hc⟩ := hY y hy
    generalize cbrtZ (y ^ 2 + D) = c at hc0 hc1 hc2 hc
    have hv : y ^ 2 + D = x ^ 3 := by linarith
    rw [hv] at hc1 hc2
    have hx0 : 0 ≤ x := by
      by_contra hn; push_neg at hn
      have : x ^ 3 < 0 := Odd.pow_neg (⟨1, rfl⟩ : Odd 3) hn
      nlinarith [sq_nonneg y]
    have e1 : c ≤ x := by
      by_contra hn; push_neg at hn
      have : x ^ 3 < c ^ 3 := pow_lt_pow_left₀ hn hx0 (by norm_num)
      linarith
    have e2 : x < c + 1 := by
      by_contra hn; push_neg at hn
      have : (c + 1) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by linarith) hn 3
      linarith
    have hcx : c = x := by omega
    subst hcx
    rcases hc with hne | hmem
    · exact absurd (by rw [hv]) hne
    · exact hmem
  · intro hmem
    exact hP _ hmem

end PerfectPower.DescentBranch
