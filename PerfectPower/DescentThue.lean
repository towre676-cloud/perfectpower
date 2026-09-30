import PerfectPower.DescentBranch
import PerfectPower.ThueLocal

/-!
# Branch certificates with transported Thue obligations

`DescentBranch.complete_of_branch` closes an entry `(k, p, q)` of the Thue-lattice table when it
is a field cube or locally impossible modulo `m`.  An entry that is neither gives an irreducible
Thue equation `F_{p,q}(a, b) = k³` with

  `F_{p,q} = (q, 3p, -3Dq, -pD)`,  i.e. `F_{p,q}(a, b) = q W₁(a, b) - p W₂(a, b)`.

Here such an entry may be closed by **transport to a proved obligation**.
- An *obligation* is a pair `(G, M)` with a proof, supplied separately, that `G(u, v) = M` has no
  integral solution. The generated files prove it once per equivalence class, for instance by a
  p-adic lifting tree (`ThueLocal.no_solution_of_lvl`).
- The entry carries a matrix `T` with `det T = ± 1` and `F_{p,q} ∘ T = G`, and `M = k³`. This is
  checked by evaluation, and `ThueLocal.empty_transport` carries the emptiness back.

The proofs of the obligations are hypotheses of `complete_of_thue` (`hclosed`), so one proof
serves every branch, of every curve, that transports to it.
-/

namespace PerfectPower.DescentThue

open PerfectPower ClassTwo DescentBranch ThueLocal

/-- The branch form of the entry `(p, q)`: `q W₁ - p W₂` as a binary cubic. -/
def branchForm (D p q : ℤ) : Form := (q, 3 * p, -3 * D * q, -p * D)

lemma branchForm_eval (D p q a b : ℤ) : evalF (branchForm D p q) a b = q * W1 D a b - p * W2 D a b := by
  simp only [evalF, branchForm, W1, W2]; ring

/-- A transported verdict: `(k, p, q, T)` with `F_{p,q} ∘ T = G`, `(G, k³)` an obligation. -/
def thueB (D k p q : ℤ) (thues : List (ℤ × ℤ × ℤ × Mat)) (closed : List (Form × ℤ)) : Bool :=
  thues.any fun e => decide (e.1 = k ∧ e.2.1 = p ∧ e.2.2.1 = q) &&
    decide (detM e.2.2.2 = 1 ∨ detM e.2.2.2 = -1) &&
    decide ((compF (branchForm D p q) e.2.2.2, k ^ 3) ∈ closed)

/-- Entry verdicts: field cube, local, or transported. -/
def entryT (D k p q : ℤ) (cubes : List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ)) (mods : List (ℤ × ℤ × ℤ × ℕ))
    (thues : List (ℤ × ℤ × ℤ × Mat)) (closed : List (Form × ℤ)) (Ys : List ℤ) : Bool :=
  entryB D k p q cubes mods Ys || thueB D k p q thues closed

/-- The branch certificate with transported verdicts (as `branchB`). -/
def branchT (D : ℤ) (K Q : ℕ) (cubes : List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ)) (mods : List (ℤ × ℤ × ℤ × ℕ))
    (thues : List (ℤ × ℤ × ℤ × Mat)) (closed : List (Form × ℤ)) (Ys : List ℤ) : Bool :=
  (List.range K).all fun i => (List.range (2 * Q + 1)).all fun iq =>
    let k : ℤ := (i : ℤ) + 1
    let q : ℤ := (iq : ℤ) - Q
    let t := k ^ 3 - D * q ^ 2
    let s := isqrtZ t
    decide (t < 0) ||
      (decide (0 ≤ s ∧ s * s ≤ t ∧ t < (s + 1) * (s + 1)) &&
        (!decide (s * s = t) ||
          (entryT D k s q cubes mods thues closed Ys && entryT D k (-s) q cubes mods thues closed Ys)))

lemma branchT_entry {D : ℤ} {K Q : ℕ} {cubes mods thues closed Ys}
    (h : branchT D K Q cubes mods thues closed Ys = true)
    (k q p : ℤ) (hk1 : 1 ≤ k) (hkK : k ≤ K) (hq : |q| ≤ Q) (hp : p ^ 2 + D * q ^ 2 = k ^ 3) :
    entryT D k p q cubes mods thues closed Ys = true := by
  unfold branchT at h
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

/-- **Every solution's `y` is a candidate**, with transported verdicts. -/
theorem y_mem_thue (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K Q : ℕ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < ((K : ℤ) + 1) * r * t)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (cubes mods thues) (closed : List (Form × ℤ)) (Ys)
    (hclosed : ∀ c ∈ closed, ∀ u v, evalF c.1 u v ≠ c.2)
    (hcert : branchT D K Q cubes mods thues closed Ys = true) (x y : ℤ) (h : y ^ 2 + D = x ^ 3) :
    y ∈ Ys := by
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
  have hent := branchT_entry hcert k e2 e1 hk1 hkK hq hnorm
  have hre' : k ^ 3 * y = e1 * W1 D a b + D * e2 * W2 D a b := by linarith
  have him' : k ^ 3 = e2 * W1 D a b - e1 * W2 D a b := by linarith
  simp only [entryT, Bool.or_eq_true] at hent
  rcases hent with hold | hnew
  · -- the old verdicts: exactly the proof of `DescentBranch.y_mem`
    simp only [entryB, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hold
    rcases hold with ⟨⟨k', p', q', c, d, g⟩, -, ⟨f1, f2, f3⟩, hcube⟩ | ⟨⟨k', p', q', m⟩, -, ⟨f1, f2, f3⟩, hmod⟩
    · dsimp only at f1 f2 f3 hcube
      subst f1 f2 f3
      simp only [cubeB, Bool.and_eq_true, decide_eq_true_eq] at hcube
      obtain ⟨⟨⟨⟨hg, -⟩, hc1⟩, hc2⟩, hdiv⟩ := hcube
      obtain ⟨b1, b2⟩ := cube_branch (a := a) (b := b) (y := y) hc1 hc2 hre' him'
      have hgk : 0 < g * k' := by positivity
      have hn : (((g * k').toNat : ℕ) : ℤ) = g * k' := Int.toNat_of_nonneg hgk.le
      refine divYs_complete D (g * k').toNat (by omega) Ys hdiv (c * a - D * d * b) (c * b + d * a) y ?_ ?_
      · rw [hn]; exact b1
      · rw [hn]; exact b2
    · dsimp only at f1 f2 f3 hmod
      subst f1 f2 f3
      exact absurd him'.symm (mod_sound hmod a b)
  · -- a transported Thue obligation
    simp only [thueB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hnew
    obtain ⟨⟨k', p', q', T⟩, -, ⟨⟨f1, f2, f3⟩, hdet⟩, hmem⟩ := hnew
    dsimp only at f1 f2 f3 hdet hmem
    subst f1 f2 f3
    have hG := hclosed _ hmem
    have := empty_transport (branchForm D p' q') _ T hdet rfl (k' ^ 3) hG a b
    rw [branchForm_eval] at this
    exact absurd him'.symm this

/-- **The complete list of integral points of `y² = x³ - D`, from a branch certificate whose
Thue entries transport to proved obligations.** -/
theorem complete_of_thue (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K Q : ℕ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < ((K : ℤ) + 1) * r * t)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (cubes mods thues) (closed : List (Form × ℤ))
    (hclosed : ∀ c ∈ closed, ∀ u v, evalF c.1 u v ≠ c.2) (Ys : List ℤ) (P : List (ℤ × ℤ))
    (hcert : branchT D K Q cubes mods thues closed Ys = true) (hpts : pointsB D Ys P = true)
    (x y : ℤ) : y ^ 2 = x ^ 3 - D ↔ (x, y) ∈ P := by
  simp only [pointsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at hpts
  obtain ⟨hY, hP⟩ := hpts
  constructor
  · intro h
    have hy := y_mem_thue D hD r t hr ht K Q hK hQ cubes mods thues closed Ys hclosed hcert x y
      (by linarith)
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

end PerfectPower.DescentThue
