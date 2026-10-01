import PerfectPower.ThueLocal

/-!
# Complete Thue lists from a unit-exponent box, under a named external bound

Setting: `K = ℚ(x)` with `x³ = P x + Q` and `O_K = ℤ[x]`, elements as coordinates
`(A, B, C) = A + B x + C x²`.  For a form `F = (c₀, c₁, c₂, c₃)` with `c₀ ≠ 0` and
`φ = c₀ θ ∈ ℤ[x]` (`θ` a root of `F(X, 1)`), a solution of `F(a, b) = M` gives
`γ = c₀ a − b φ = enc a b` of norm `c₀² M` (`NormForm.det_mulMat`).

* **The external input** is the hypothesis `ExtBound`: every solution with `|b| > V` has
  `γ = ±γ₀ ε₁^{e₁} ε₂^{e₂}` for a listed `γ₀`, with `|eᵢ| ≤ B` (`fam`).  It is produced outside Lean:
  PARI's certified unit group and norm representatives, Matveev's theorem, and an interval
  reduction (`crosscheck/thue_bound.py`).
* **Checked by the kernel**: `boxB`, every element of the box (either sign) that lies in the
  lattice `ℤ c₀ + ℤ φ` and solves `F = M` decodes to a listed pair; `smallB`, an exhaustive search over `|b| ≤ V` with
  `|a|` below the Cauchy bound (`cauchy`).
* `thue_list`: under `ExtBound`, **`F(a, b) = M ⇔ (a, b) ∈ L`**.
-/

namespace PerfectPower.UnitBox

open PerfectPower ThueLocal

/-- Elements of `ℤ[x]`, `x³ = P x + Q`, as coordinates `(A, B, C)`. -/
abbrev Z3 := ℤ × ℤ × ℤ

/-- Multiplication in `ℤ[x]`, `x³ = P x + Q`. -/
def mul (P Q : ℤ) (x y : Z3) : Z3 :=
  let (a, b, c) := x
  let (d, e, f) := y
  let c0 := a * d
  let c1 := a * e + b * d
  let c2 := a * f + b * e + c * d
  let c3 := b * f + c * e
  let c4 := c * f
  -- x³ = P x + Q, x⁴ = P x² + Q x
  (c0 + Q * c3, c1 + P * c3 + Q * c4, c2 + P * c4)

/-- `x^k`. -/
def pow (P Q : ℤ) (x : Z3) : ℕ → Z3
  | 0 => (1, 0, 0)
  | k + 1 => mul P Q (pow P Q x k) x

/-- `ε^e` for `e ∈ [−B, B]`, indexed by `i = e + B`. -/
def zpow (P Q : ℤ) (x xinv : Z3) (B i : ℕ) : Z3 :=
  if B ≤ i then pow P Q x (i - B) else pow P Q xinv (B - i)

/-- The box `γ₀ ε₁^{e₁} ε₂^{e₂}`, `|eᵢ| ≤ B`. -/
def fam (P Q : ℤ) (g0 e1 e1i e2 e2i : Z3) (B : ℕ) : List Z3 :=
  (List.range (2 * B + 1)).flatMap fun i =>
    (List.range (2 * B + 1)).map fun j =>
      mul P Q (mul P Q g0 (zpow P Q e1 e1i B i)) (zpow P Q e2 e2i B j)

/-- `−g`. -/
def neg (g : Z3) : Z3 := (-g.1, -g.2.1, -g.2.2)

/-- `γ = c₀ a − b φ` in coordinates. -/
def enc (c0 : ℤ) (phi : Z3) (a b : ℤ) : Z3 := (c0 * a - b * phi.1, -(b * phi.2.1), -(b * phi.2.2))

/-- Read `(a, b)` back from `γ`, assuming `γ` is in the lattice. -/
def dec (c0 : ℤ) (phi : Z3) (g : Z3) : ℤ × ℤ :=
  let b := if phi.2.2 = 0 then -(g.2.1 / phi.2.1) else -(g.2.2 / phi.2.2)
  ((g.1 + b * phi.1) / c0, b)

theorem dec_enc (c0 : ℤ) (phi : Z3) (hc : c0 ≠ 0) (hphi : phi.2.1 ≠ 0 ∨ phi.2.2 ≠ 0) (a b : ℤ) :
    dec c0 phi (enc c0 phi a b) = (a, b) := by
  obtain ⟨p0, p1, p2⟩ := phi
  have hb : (if p2 = 0 then -(-(b * p1) / p1) else -(-(b * p2) / p2)) = b := by
    split_ifs with h
    · have h1 : p1 ≠ 0 := by simpa [h] using hphi
      rw [show -(b * p1) = (-b) * p1 by ring, Int.mul_ediv_cancel _ h1, neg_neg]
    · rw [show -(b * p2) = (-b) * p2 by ring, Int.mul_ediv_cancel _ h, neg_neg]
  simp only [dec, enc]
  rw [hb, show c0 * a - b * p0 + b * p0 = a * c0 by ring, Int.mul_ediv_cancel _ hc]

/-- **Cauchy's root bound**, the form used for the small-`b` search. -/
theorem cauchy {c0 u w z a : ℤ} (hc : c0 ≠ 0) (h : c0 * a ^ 3 + u * a ^ 2 + w * a + z = 0) :
    |a| ≤ |u| + |w| + |z| + 1 := by
  by_contra hlt
  push_neg at hlt
  have hu := abs_nonneg u
  have hw := abs_nonneg w
  have hz := abs_nonneg z
  have ht1 : 1 ≤ |a| := by linarith
  have hc1 : 1 ≤ |c0| := Int.one_le_abs hc
  have e1 : |c0 * a ^ 3| = |c0| * |a| ^ 3 := by rw [abs_mul, abs_pow]
  have e3 : |c0 * a ^ 3| = |u * a ^ 2 + w * a + z| := by
    rw [show c0 * a ^ 3 = -(u * a ^ 2 + w * a + z) by linarith, abs_neg]
  have e2 : |u * a ^ 2 + w * a + z| ≤ |u| * |a| ^ 2 + |w| * |a| + |z| := by
    calc |u * a ^ 2 + w * a + z| ≤ |u * a ^ 2 + w * a| + |z| := abs_add_le _ _
      _ ≤ |u * a ^ 2| + |w * a| + |z| := by linarith [abs_add_le (u * a ^ 2) (w * a)]
      _ = |u| * |a| ^ 2 + |w| * |a| + |z| := by rw [abs_mul, abs_mul, abs_pow]
  set t := |a|
  have htt : t ≤ t ^ 2 := by nlinarith
  have h2 : |w| * t ≤ |w| * t ^ 2 := mul_le_mul_of_nonneg_left htt hw
  have h3 : |z| * 1 ≤ |z| * t ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hz
  have h4 : (|u| + |w| + |z|) * t ^ 2 < t * t ^ 2 := by
    nlinarith
  have h5 : t ^ 3 ≤ |c0| * t ^ 3 := by
    have : 0 ≤ t ^ 3 := by positivity
    nlinarith
  nlinarith

/-- The exhaustive search over `|b| ≤ V`, with `|a|` up to the Cauchy bound. -/
def smallB (F : Form) (M : ℤ) (V : ℕ) (L : List (ℤ × ℤ)) : Bool :=
  (List.range (2 * V + 1)).all fun ib =>
    let b : ℤ := (ib : ℤ) - V
    let S := |F.2.1 * b| + |F.2.2.1 * b ^ 2| + |F.2.2.2 * b ^ 3 - M| + 1
    (List.range (2 * S.toNat + 1)).all fun ia =>
      let a : ℤ := (ia : ℤ) - S.toNat
      !decide (evalF F a b = M) || decide ((a, b) ∈ L)

theorem small_mem {F : Form} {M : ℤ} {V : ℕ} {L : List (ℤ × ℤ)} (hc : F.1 ≠ 0)
    (h : smallB F M V L = true) {a b : ℤ} (hb : |b| ≤ V) (hs : evalF F a b = M) : (a, b) ∈ L := by
  obtain ⟨c0, c1, c2, c3⟩ := F
  have hb' := abs_le.mp hb
  have hcau : |a| ≤ |c1 * b| + |c2 * b ^ 2| + |c3 * b ^ 3 - M| + 1 :=
    cauchy (u := c1 * b) (w := c2 * b ^ 2) (z := c3 * b ^ 3 - M) hc
      (by simp only [evalF] at hs; linear_combination hs)
  set S := |c1 * b| + |c2 * b ^ 2| + |c3 * b ^ 3 - M| + 1 with hS
  have hS0 : 0 ≤ S := by positivity
  have hSn : ((S.toNat : ℕ) : ℤ) = S := Int.toNat_of_nonneg hS0
  have ha := abs_le.mp (le_trans hcau le_rfl)
  unfold smallB at h
  rw [List.all_eq_true] at h
  have hi : (b + V).toNat ∈ List.range (2 * V + 1) := by rw [List.mem_range]; omega
  have h' := h _ hi
  have hbc : (((b + V).toNat : ℕ) : ℤ) - V = b := by omega
  simp only [hbc] at h'
  rw [← hS, List.all_eq_true] at h'
  have hia : (a + S.toNat).toNat ∈ List.range (2 * S.toNat + 1) := by
    rw [List.mem_range]; omega
  have h'' := h' _ hia
  have hac : (((a + S.toNat).toNat : ℕ) : ℤ) - S.toNat = a := by omega
  simp only [hac, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h''
  rcases h'' with h1 | h1
  · exact absurd hs h1
  · exact h1

/-- The kernel box check: every element of the box, of either sign, that lies in the lattice
`ℤ c₀ + ℤ φ` and decodes to a solution of `F = M` (not `F = −M`) decodes to a listed pair. -/
def boxB (F : Form) (M P Q : ℤ) (phi : Z3) (g0s : List Z3) (e1 e1i e2 e2i : Z3) (B : ℕ)
    (L : List (ℤ × ℤ)) : Bool :=
  g0s.all fun g0 => (fam P Q g0 e1 e1i e2 e2i B).all fun g => [g, neg g].all fun h =>
    !decide (enc F.1 phi (dec F.1 phi h).1 (dec F.1 phi h).2 = h) ||
      !decide (evalF F (dec F.1 phi h).1 (dec F.1 phi h).2 = M) || decide (dec F.1 phi h ∈ L)

/-- **The external bound, as an explicit hypothesis.** -/
def ExtBound (F : Form) (M P Q : ℤ) (phi : Z3) (g0s : List Z3) (e1 e1i e2 e2i : Z3) (B V : ℕ) : Prop :=
  ∀ a b : ℤ, evalF F a b = M → (V : ℤ) < |b| →
    ∃ g0 ∈ g0s, enc F.1 phi a b ∈ fam P Q g0 e1 e1i e2 e2i B ∨
      neg (enc F.1 phi a b) ∈ fam P Q g0 e1 e1i e2 e2i B

lemma neg_neg' (g : Z3) : neg (neg g) = g := by
  obtain ⟨a, b, c⟩ := g; simp [neg]

lemma box_mem {F : Form} {M P Q : ℤ} {phi : Z3} {g0s : List Z3} {e1 e1i e2 e2i : Z3} {B : ℕ}
    {L : List (ℤ × ℤ)} (hbox : boxB F M P Q phi g0s e1 e1i e2 e2i B L = true) {g0 g h : Z3}
    (hg0 : g0 ∈ g0s) (hg : g ∈ fam P Q g0 e1 e1i e2 e2i B) (hh : h = g ∨ h = neg g)
    (henc : enc F.1 phi (dec F.1 phi h).1 (dec F.1 phi h).2 = h)
    (hs : evalF F (dec F.1 phi h).1 (dec F.1 phi h).2 = M) : dec F.1 phi h ∈ L := by
  unfold boxB at hbox
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp hbox g0 hg0) g hg
  have hmem : h ∈ [g, neg g] := by
    rcases hh with rfl | rfl <;> simp
  have h2 := List.all_eq_true.mp h1 h hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h2
  rcases h2 with (h2 | h2) | h2
  · exact absurd henc h2
  · exact absurd hs h2
  · exact h2

/-- **A complete Thue list, under the external bound.** -/
theorem thue_list (F : Form) (M P Q : ℤ) (phi : Z3) (g0s : List Z3) (e1 e1i e2 e2i : Z3) (B V : ℕ)
    (L : List (ℤ × ℤ)) (hc : F.1 ≠ 0) (hphi : phi.2.1 ≠ 0 ∨ phi.2.2 ≠ 0)
    (hB : ExtBound F M P Q phi g0s e1 e1i e2 e2i B V)
    (hbox : boxB F M P Q phi g0s e1 e1i e2 e2i B L = true)
    (hsmall : smallB F M V L = true)
    (hL : (L.all fun p => decide (evalF F p.1 p.2 = M)) = true) (a b : ℤ) :
    evalF F a b = M ↔ (a, b) ∈ L := by
  constructor
  · intro hs
    by_cases hv : |b| ≤ V
    · exact small_mem hc hsmall hv hs
    · push_neg at hv
      obtain ⟨g0, hg0, hm⟩ := hB a b hs hv
      have hde := dec_enc F.1 phi hc hphi a b
      have key : ∀ g, g ∈ fam P Q g0 e1 e1i e2 e2i B → (enc F.1 phi a b = g ∨ enc F.1 phi a b = neg g) →
          (a, b) ∈ L := by
        intro g hg hh
        have := box_mem hbox hg0 hg hh (by rw [hde]) (by rw [hde]; exact hs)
        rwa [hde] at this
      rcases hm with hm | hm
      · exact key _ hm (Or.inl rfl)
      · exact key _ hm (Or.inr (neg_neg' _).symm)
  · intro hm
    have := List.all_eq_true.mp hL _ hm
    simpa using this

end PerfectPower.UnitBox
