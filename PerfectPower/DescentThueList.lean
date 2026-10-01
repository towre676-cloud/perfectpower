import PerfectPower.DescentThue

/-!
# Branch certificates with transported Thue obligations that carry solution lists

`DescentThue.complete_of_thue` closes a branch only when its Thue obligation is **empty**.  Many
obligations have solutions that give no point of the curve, or give exactly the known points.
Here an obligation may instead be a triple `(G, M, L)` with a proof, supplied separately, that
**every** solution of `G(u, v) = M` is in `L` (`hlisted`).

For a branch `(k, p, q)` carried to `(G, k³, L)` by a unimodular `T`, every solution `(a, b)` of
the branch equation is `T (u, v)` for some `(u, v) ∈ L` (`ThueLocal.sols_transport`).  The branch
relation `k³ y = p W₁(a, b) + D q W₂(a, b)` then gives `y` exactly, so the check `listB` asks, for
each listed `(u, v)`, that either `k³` does not divide `p W₁ + D q W₂` or the quotient is in the
candidate list `Ys`.  `pointsB` finishes as in `DescentBranch`.
-/

namespace PerfectPower.DescentThueList

open PerfectPower ClassTwo DescentBranch ThueLocal DescentThue

/-- A transported verdict with a solution list. -/
def listB (D k p q : ℤ) (thuesL : List (ℤ × ℤ × ℤ × Mat)) (listed : List (Form × ℤ × List (ℤ × ℤ)))
    (Ys : List ℤ) : Bool :=
  thuesL.any fun e => decide (e.1 = k ∧ e.2.1 = p ∧ e.2.2.1 = q) &&
    decide (detM e.2.2.2 = 1 ∨ detM e.2.2.2 = -1) &&
    listed.any fun c => decide (c.1 = compF (branchForm D p q) e.2.2.2 ∧ c.2.1 = k ^ 3) &&
      c.2.2.all fun uv =>
        let a := e.2.2.2.1.1 * uv.1 + e.2.2.2.1.2 * uv.2
        let b := e.2.2.2.2.1 * uv.1 + e.2.2.2.2.2 * uv.2
        let W := p * W1 D a b + D * q * W2 D a b
        !decide (W % k ^ 3 = 0) || decide (W / k ^ 3 ∈ Ys)

/-- Entry verdicts: field cube, local, transported to an empty obligation, or transported to a
listed one. -/
def entryL (D k p q : ℤ) (cubes : List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ)) (mods : List (ℤ × ℤ × ℤ × ℕ))
    (thues : List (ℤ × ℤ × ℤ × Mat)) (closed : List (Form × ℤ)) (thuesL : List (ℤ × ℤ × ℤ × Mat))
    (listed : List (Form × ℤ × List (ℤ × ℤ))) (Ys : List ℤ) : Bool :=
  entryT D k p q cubes mods thues closed Ys || listB D k p q thuesL listed Ys

/-- The branch certificate with all four verdicts (as `DescentThue.branchT`). -/
def branchL (D : ℤ) (K Q : ℕ) (cubes : List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ)) (mods : List (ℤ × ℤ × ℤ × ℕ))
    (thues : List (ℤ × ℤ × ℤ × Mat)) (closed : List (Form × ℤ)) (thuesL : List (ℤ × ℤ × ℤ × Mat))
    (listed : List (Form × ℤ × List (ℤ × ℤ))) (Ys : List ℤ) : Bool :=
  (List.range K).all fun i => (List.range (2 * Q + 1)).all fun iq =>
    let k : ℤ := (i : ℤ) + 1
    let q : ℤ := (iq : ℤ) - Q
    let t := k ^ 3 - D * q ^ 2
    let s := isqrtZ t
    decide (t < 0) ||
      (decide (0 ≤ s ∧ s * s ≤ t ∧ t < (s + 1) * (s + 1)) &&
        (!decide (s * s = t) ||
          (entryL D k s q cubes mods thues closed thuesL listed Ys &&
            entryL D k (-s) q cubes mods thues closed thuesL listed Ys)))

lemma branchL_entry {D : ℤ} {K Q : ℕ} {cubes mods thues closed thuesL listed Ys}
    (h : branchL D K Q cubes mods thues closed thuesL listed Ys = true)
    (k q p : ℤ) (hk1 : 1 ≤ k) (hkK : k ≤ K) (hq : |q| ≤ Q) (hp : p ^ 2 + D * q ^ 2 = k ^ 3) :
    entryL D k p q cubes mods thues closed thuesL listed Ys = true := by
  unfold branchL at h
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

/-- A listed verdict puts `y` in the candidates. -/
lemma y_of_listB {D k p q : ℤ} {thuesL listed Ys} (hk : 1 ≤ k)
    (hlisted : ∀ c ∈ listed, ∀ u v, evalF c.1 u v = c.2.1 → (u, v) ∈ c.2.2)
    (hB : listB D k p q thuesL listed Ys = true) {a b y : ℤ}
    (hre : k ^ 3 * y = p * W1 D a b + D * q * W2 D a b) (him : k ^ 3 = q * W1 D a b - p * W2 D a b) :
    y ∈ Ys := by
  simp only [listB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hB
  obtain ⟨⟨k', p', q', T⟩, -, ⟨⟨f1, f2, f3⟩, hdet⟩, c, hc, ⟨hcF, hcM⟩, hall⟩ := hB
  dsimp only at f1 f2 f3 hdet hcF hall
  subst f1 f2 f3
  have hF : evalF (branchForm D p' q') a b = k' ^ 3 := by rw [branchForm_eval]; exact him.symm
  obtain ⟨u, v, huv, ha, hb⟩ := sols_transport _ T hdet _ a b hF
  have hmem := hlisted c hc u v (by rw [hcF, hcM]; exact huv)
  have h1 := List.all_eq_true.mp hall _ hmem
  dsimp only at h1
  rw [← ha, ← hb, ← hre] at h1
  have hk3 : k' ^ 3 ≠ 0 := by positivity
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    Int.mul_emod_right, Int.mul_ediv_cancel_left _ hk3] at h1
  rcases h1 with h1 | h1
  · exact absurd trivial h1
  · exact h1

/-- **Every solution's `y` is a candidate**, with all four verdicts. -/
theorem y_mem_list (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K Q : ℕ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < ((K : ℤ) + 1) * r * t)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (cubes mods thues) (closed : List (Form × ℤ))
    (thuesL) (listed : List (Form × ℤ × List (ℤ × ℤ))) (Ys)
    (hclosed : ∀ c ∈ closed, ∀ u v, evalF c.1 u v ≠ c.2)
    (hlisted : ∀ c ∈ listed, ∀ u v, evalF c.1 u v = c.2.1 → (u, v) ∈ c.2.2)
    (hcert : branchL D K Q cubes mods thues closed thuesL listed Ys = true) (x y : ℤ)
    (h : y ^ 2 + D = x ^ 3) : y ∈ Ys := by
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
  have hent := branchL_entry hcert k e2 e1 hk1 hkK hq hnorm
  have hre' : k ^ 3 * y = e1 * W1 D a b + D * e2 * W2 D a b := by linarith
  have him' : k ^ 3 = e2 * W1 D a b - e1 * W2 D a b := by linarith
  simp only [entryL, Bool.or_eq_true] at hent
  rcases hent with hT | hL
  · -- the verdicts of `DescentThue`: the same certificate with no listed entries
    simp only [entryT, Bool.or_eq_true] at hT
    rcases hT with hold | hnew
    · simp only [entryB, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hold
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
    · simp only [thueB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hnew
      obtain ⟨⟨k', p', q', T⟩, -, ⟨⟨f1, f2, f3⟩, hdet⟩, hmem⟩ := hnew
      dsimp only at f1 f2 f3 hdet hmem
      subst f1 f2 f3
      have hG := hclosed _ hmem
      have := empty_transport (branchForm D p' q') _ T hdet rfl (k' ^ 3) hG a b
      rw [branchForm_eval] at this
      exact absurd him'.symm this
  · exact y_of_listB hk1 hlisted hL hre' him'

/-- **The complete list of integral points of `y² = x³ − D`, from a branch certificate whose
Thue entries transport to obligations that are empty or carry complete solution lists.** -/
theorem complete_of_lists (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K Q : ℕ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < ((K : ℤ) + 1) * r * t)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (cubes mods thues) (closed : List (Form × ℤ))
    (thuesL) (listed : List (Form × ℤ × List (ℤ × ℤ)))
    (hclosed : ∀ c ∈ closed, ∀ u v, evalF c.1 u v ≠ c.2)
    (hlisted : ∀ c ∈ listed, ∀ u v, evalF c.1 u v = c.2.1 → (u, v) ∈ c.2.2)
    (Ys : List ℤ) (P : List (ℤ × ℤ))
    (hcert : branchL D K Q cubes mods thues closed thuesL listed Ys = true) (hpts : pointsB D Ys P = true)
    (x y : ℤ) : y ^ 2 = x ^ 3 - D ↔ (x, y) ∈ P := by
  simp only [pointsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at hpts
  obtain ⟨hY, hP⟩ := hpts
  constructor
  · intro h
    have hy := y_mem_list D hD r t hr ht K Q hK hQ cubes mods thues closed thuesL listed Ys hclosed
      hlisted hcert x y (by linarith)
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

end PerfectPower.DescentThueList
