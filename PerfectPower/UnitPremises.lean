import PerfectPower.UnitBox
import PerfectPower.DirectReduction

/-!
# The external bound, split into three named statements

`UnitBox.ExtBound` was one opaque premise per class.  Here it is **derived** from three smaller
statements, each reusable and each with its own evidence:

* `UnitGen P Q ε₁ ε₁⁻¹ ε₂ ε₂⁻¹` (**one per field**): every unit of `ℤ[x]` is `±ε₁^a ε₂^b`.
  **Proved** for both fields from a kernel-checked certificate (`UnitGen.lean`,
  `UnitGenProof.unitGen_of_cert`; the generated `unitGen_proved`).
* `NormRep P Q N reps` (**one per norm target**): every element of norm `N` is `γ₀ u` for a listed
  `γ₀` and a unit `u`.  **Proved** for every target in use by explicit division
  (`NormRepProof.lean`).
* `Analytic …` (**one per class**): for each solution with `|b| > V` and each way of writing
  `c₀a − bφ = ±γ₀ ε₁^{e₁} ε₂^{e₂}`, some case gives reals `κ, μ, c, A` inside its rational
  enclosures with `H ≤ M₀` and `|κ e₁ + e₂ + μ| ≤ A e^{−cH}`.  Evidence: Siegel's identity, the
  conjugate estimates and Matveev's theorem (`crosscheck/thue_bound.py`).

**Proved here**: `extBound_of`.  From the three statements, the norm identity of the class and a
kernel check of every reduction chain (`DirectReduction.chainCheck`), every solution with
`|b| > V` lies in the box `fam … B`.  So the reduction, the box and the bookkeeping between them
are no longer assumptions.
-/

namespace PerfectPower.UnitPremises

open PerfectPower ThueLocal UnitBox DirectReduction Real

/-- `x^e` for `e ∈ ℤ`, using the supplied inverse. -/
def zp (P Q : ℤ) (x xinv : Z3) (e : ℤ) : Z3 :=
  if 0 ≤ e then pow P Q x e.toNat else pow P Q xinv (-e).toNat

/-- The norm: the determinant of multiplication by `g` on `(1, x, x²)`, `x³ = P x + Q`. -/
def nrm (P Q : ℤ) (g : Z3) : ℤ :=
  let (a, b, c) := g
  a * ((a + P * c) * (a + P * c) - (P * b + Q * c) * b) -
    Q * c * (b * (a + P * c) - (P * b + Q * c) * c) +
    Q * b * (b * b - (a + P * c) * c)

/-- **Unit generation** (one per field). -/
def UnitGen (P Q : ℤ) (e1 e1i e2 e2i : Z3) : Prop :=
  ∀ u v : Z3, mul P Q u v = (1, 0, 0) → ∃ a b : ℤ,
    u = mul P Q (zp P Q e1 e1i a) (zp P Q e2 e2i b) ∨ u = neg (mul P Q (zp P Q e1 e1i a) (zp P Q e2 e2i b))

/-- **Norm representatives** (one per norm target). -/
def NormRep (P Q N : ℤ) (g0s : List Z3) : Prop :=
  ∀ g : Z3, nrm P Q g = N → ∃ g0 ∈ g0s, ∃ u v : Z3, mul P Q u v = (1, 0, 0) ∧ g = mul P Q g0 u

/-- One analytic case: rational enclosures of `κ, μ`, `c ≥ cl`, `A ≤ Au`, the first bound `M₀`
(Matveev), and the reduction chain `(q, B, J)`. -/
structure Case where
  /-- Lower end of the enclosure of `κ`. -/
  kl : ℚ
  /-- Upper end of the enclosure of `κ`. -/
  ku : ℚ
  /-- Lower end of the enclosure of `μ`. -/
  ml : ℚ
  /-- Upper end of the enclosure of `μ`. -/
  mu : ℚ
  /-- A lower bound for the decay rate `c`. -/
  cl : ℚ
  /-- An upper bound for the constant `A`. -/
  Au : ℚ
  /-- The first bound `H ≤ M₀` (Matveev). -/
  M0 : ℕ
  /-- The reduction chain, as `(q, B, J)` triples. -/
  steps : List (ℕ × ℕ × ℕ)

/-- The analytic inequality of one case, at exponents `(e₁, e₂)`. -/
def LinIneq (C : Case) (e1 e2 : ℤ) : Prop :=
  ∃ κ μ c A : ℝ, (C.kl : ℝ) ≤ κ ∧ κ ≤ C.ku ∧ (C.ml : ℝ) ≤ μ ∧ μ ≤ C.mu ∧ (C.cl : ℝ) ≤ c ∧ A ≤ C.Au ∧
    hmax e1 e2 ≤ C.M0 ∧ |κ * e1 + e2 + μ| ≤ A * exp (-(c * (hmax e1 e2 : ℝ)))

/-- **The analytic premise** (one per class). -/
def Analytic (F : Form) (M P Q : ℤ) (phi : Z3) (e1 e1i e2 e2i : Z3) (V : ℕ)
    (reps : List (Z3 × List Case)) : Prop :=
  ∀ a b : ℤ, evalF F a b = M → (V : ℤ) < |b| → ∀ r ∈ reps, ∀ x y : ℤ,
    (enc F.1 phi a b = mul P Q r.1 (mul P Q (zp P Q e1 e1i x) (zp P Q e2 e2i y)) ∨
      enc F.1 phi a b = neg (mul P Q r.1 (mul P Q (zp P Q e1 e1i x) (zp P Q e2 e2i y)))) →
    ∃ C ∈ r.2, LinIneq C x y

/-- Every reduction chain checks, and ends at most at `B`. -/
def chainsB (reps : List (Z3 × List Case)) (B : ℕ) : Bool :=
  reps.all fun r => r.2.all fun C =>
    chainCheck C.kl C.ku C.ml C.mu C.cl C.Au C.M0 C.steps && decide (chainEnd C.M0 C.steps ≤ B)

lemma mul_assoc' (P Q : ℤ) (x y z : Z3) : mul P Q (mul P Q x y) z = mul P Q x (mul P Q y z) := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  obtain ⟨g, h, i⟩ := z
  simp only [mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

lemma mul_neg' (P Q : ℤ) (x y : Z3) : mul P Q x (neg y) = neg (mul P Q x y) := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  simp only [mul, neg, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

lemma zpow_eq_zp (P Q : ℤ) (x xinv : Z3) (B i : ℕ) : zpow P Q x xinv B i = zp P Q x xinv ((i : ℤ) - B) := by
  unfold zpow zp
  by_cases h : B ≤ i
  · rw [if_pos h, if_pos (by omega)]
    congr 1
    omega
  · rw [if_neg h, if_neg (by omega)]
    congr 1
    omega

lemma mem_fam (P Q : ℤ) (g0 e1 e1i e2 e2i : Z3) (B : ℕ) (x y : ℤ) (hx : |x| ≤ B) (hy : |y| ≤ B) :
    mul P Q g0 (mul P Q (zp P Q e1 e1i x) (zp P Q e2 e2i y)) ∈ fam P Q g0 e1 e1i e2 e2i B := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  unfold fam
  rw [List.mem_flatMap]
  refine ⟨(x + B).toNat, by rw [List.mem_range]; omega, ?_⟩
  rw [List.mem_map]
  refine ⟨(y + B).toNat, by rw [List.mem_range]; omega, ?_⟩
  rw [zpow_eq_zp, zpow_eq_zp, mul_assoc']
  have e1 : (((x + B).toNat : ℕ) : ℤ) - B = x := by omega
  have e2 : (((y + B).toNat : ℕ) : ℤ) - B = y := by omega
  rw [e1, e2]

/-- **The external bound, derived.** -/
theorem extBound_of (F : Form) (M P Q : ℤ) (phi : Z3) (e1 e1i e2 e2i : Z3) (B V : ℕ)
    (reps : List (Z3 × List Case))
    (hU : UnitGen P Q e1 e1i e2 e2i) (hN : NormRep P Q (F.1 ^ 2 * M) (reps.map Prod.fst))
    (hnorm : ∀ a b, nrm P Q (enc F.1 phi a b) = F.1 ^ 2 * evalF F a b)
    (hA : Analytic F M P Q phi e1 e1i e2 e2i V reps) (hchk : chainsB reps B = true) :
    ExtBound F M P Q phi (reps.map Prod.fst) e1 e1i e2 e2i B V := by
  intro a b hs hb
  have hn : nrm P Q (enc F.1 phi a b) = F.1 ^ 2 * M := by rw [hnorm, hs]
  obtain ⟨g0, hg0, u, v, huv, hg⟩ := hN _ hn
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg0
  obtain ⟨x, y, hw⟩ := hU u v huv
  set w := mul P Q (zp P Q e1 e1i x) (zp P Q e2 e2i y)
  have hcases : enc F.1 phi a b = mul P Q r.1 w ∨ enc F.1 phi a b = neg (mul P Q r.1 w) := by
    rcases hw with hw | hw
    · left; rw [hg, hw]
    · right; rw [hg, hw, mul_neg']
  obtain ⟨C, hC, κ, μ, c, A, hk1, hk2, hm1, hm2, hc, hAA, hH, hlin⟩ := hA a b hs hb r hr x y hcases
  simp only [chainsB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hch, hend⟩ := hchk r hr C hC
  have hHB : hmax x y ≤ B := le_trans (chain_sound κ μ c A hk1 hk2 hm1 hm2 hc hAA x y hlin _ _ hch hH)
    (by exact_mod_cast hend)
  have hx : |x| ≤ B := le_trans (le_max_left _ _) hHB
  have hy : |y| ≤ B := le_trans (le_max_right _ _) hHB
  refine ⟨r.1, List.mem_map_of_mem hr, ?_⟩
  have hm := mem_fam P Q r.1 e1 e1i e2 e2i B x y hx hy
  rcases hcases with h | h
  · left; rw [h]; exact hm
  · right; rw [h, neg_neg']; exact hm

/-- The finite part of the unit-domain witness: every triple `(A, B, C)` with `|A| ≤ a`, `|B| ≤ b`,
`|C| ≤ c` and norm `±1` is one of the listed candidates. -/
def unitBoxB (P Q : ℤ) (a b c : ℕ) (cands : List Z3) : Bool :=
  (List.range (2 * a + 1)).all fun i => (List.range (2 * b + 1)).all fun j =>
    (List.range (2 * c + 1)).all fun k =>
      let g : Z3 := ((i : ℤ) - a, (j : ℤ) - b, (k : ℤ) - c)
      !decide (nrm P Q g = 1 ∨ nrm P Q g = -1) || decide (g ∈ cands)

theorem unitBox_sound {P Q : ℤ} {a b c : ℕ} {cands : List Z3} (h : unitBoxB P Q a b c cands = true)
    (g : Z3) (ha : |g.1| ≤ a) (hb : |g.2.1| ≤ b) (hc : |g.2.2| ≤ c)
    (hn : nrm P Q g = 1 ∨ nrm P Q g = -1) : g ∈ cands := by
  obtain ⟨x, y, z⟩ := g
  simp only at ha hb hc
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  unfold unitBoxB at h
  have h1 := List.all_eq_true.mp h (x + a).toNat (by rw [List.mem_range]; omega)
  have h2 := List.all_eq_true.mp h1 (y + b).toNat (by rw [List.mem_range]; omega)
  have h3 := List.all_eq_true.mp h2 (z + c).toNat (by rw [List.mem_range]; omega)
  have ex : (((x + a).toNat : ℕ) : ℤ) - a = x := by omega
  have ey : (((y + b).toNat : ℕ) : ℤ) - b = y := by omega
  have ez : (((z + c).toNat : ℕ) : ℤ) - c = z := by omega
  simp only [ex, ey, ez, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h3
  exact h3.resolve_left (not_not.mpr hn)

/-! ### Sign transport: the premises for `−M` from those for `M`

A cubic form is odd, `F(−a, −b) = −F(a, b)`, and so are `enc` and the norm.  So the premises of
the target `−M` (representative `−γ₀`, the same analytic cases) follow from those of `M`. -/

lemma nrm_neg (P Q : ℤ) (g : Z3) : nrm P Q (neg g) = -nrm P Q g := by
  obtain ⟨a, b, c⟩ := g
  simp only [nrm, neg]
  ring

lemma neg_mul' (P Q : ℤ) (x y : Z3) : mul P Q (neg x) y = neg (mul P Q x y) := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  simp only [mul, neg, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

lemma enc_neg (c0 : ℤ) (phi : Z3) (a b : ℤ) : enc c0 phi (-a) (-b) = neg (enc c0 phi a b) := by
  simp only [enc, neg, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

lemma evalF_neg (F : Form) (a b : ℤ) : evalF F (-a) (-b) = -evalF F a b := by
  simp only [evalF]
  ring

/-- The representatives and cases of the target `−M`. -/
def negReps (reps : List (Z3 × List Case)) : List (Z3 × List Case) :=
  reps.map fun r => (neg r.1, r.2)

/-- **`NormRep` transports to the negated target.** -/
theorem normRep_neg_of {P Q N : ℤ} {reps : List (Z3 × List Case)}
    (h : NormRep P Q N (reps.map Prod.fst)) : NormRep P Q (-N) ((negReps reps).map Prod.fst) := by
  intro g hg
  have hg' : nrm P Q (neg g) = N := by rw [nrm_neg, hg, neg_neg]
  obtain ⟨g0, hg0, u, v, huv, he⟩ := h _ hg'
  refine ⟨neg g0, ?_, u, v, huv, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg0
    exact List.mem_map.mpr ⟨(neg r.1, r.2), List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩
  · rw [neg_mul', ← he, neg_neg']

/-- **`Analytic` transports to the negated target**, with the same cases. -/
theorem analytic_neg_of {F : Form} {M P Q : ℤ} {phi : Z3} {e1 e1i e2 e2i : Z3} {V : ℕ}
    {reps : List (Z3 × List Case)} (h : Analytic F M P Q phi e1 e1i e2 e2i V reps) :
    Analytic F (-M) P Q phi e1 e1i e2 e2i V (negReps reps) := by
  intro a b hs hb r' hr' x y hcase
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  have hs' : evalF F (-a) (-b) = M := by rw [evalF_neg, hs, neg_neg]
  have hb' : (V : ℤ) < |-b| := by rwa [abs_neg]
  set w := mul P Q (zp P Q e1 e1i x) (zp P Q e2 e2i y)
  have hcase' : enc F.1 phi (-a) (-b) = mul P Q r.1 w ∨ enc F.1 phi (-a) (-b) = neg (mul P Q r.1 w) := by
    rw [enc_neg]
    simp only [neg_mul'] at hcase
    rcases hcase with h1 | h1
    · left; rw [h1, neg_neg']
    · right; rw [h1, neg_neg']
  exact h (-a) (-b) hs' hb' r hr x y hcase'

/-- Negative control: every chain of `reps`, with its final bound lowered by one, is rejected. -/
def forgedRejectedB (reps : List (Z3 × List Case)) : Bool :=
  reps.all fun r => r.2.all fun C => !chainCheck C.kl C.ku C.ml C.mu C.cl C.Au C.M0 (lowerLast C.steps)

end PerfectPower.UnitPremises
