import PerfectPower.PositiveKCurve

/-!
# Complete point lists with supplied square roots

`PositiveKCurve.pointsB` computes `Int.sqrt (x³ + k)` in the kernel. For large points (`x = 5234`
for `k = 17`, `x = 8158` for `k = 24`) that unfolding overflows the stack. Here each candidate `x`
comes with a supplied integer `s ≥ 0` and the kernel only checks `s² ≤ x³ + k < (s + 1)²`
(or `x³ + k < 0`), which pins `|y| = s` (`complete_of_sols_root`).
-/

namespace PerfectPower.PositiveKCurveRoot

open PerfectPower MordellCubicForm PositiveKCurve

/-- One candidate `(x, s)`: `s` is the floor square root of `x³ + k` (or `x³ + k < 0`), and if
`x³ + k = s²` both points are listed. -/
def rootOkB (k : ℤ) (L : List (ℤ × ℤ)) (p : ℤ × ℤ) : Bool :=
  let n := p.1 ^ 3 + k
  decide (n < 0) ||
    (decide (0 ≤ p.2) && decide (p.2 ^ 2 ≤ n) && decide (n < (p.2 + 1) ^ 2) &&
      (decide (p.2 ^ 2 ≠ n) || (decide ((p.1, p.2) ∈ L) && decide ((p.1, -p.2) ∈ L))))

/-- The `Int.sqrt` check of `PositiveKCurve.pointsB` for one small `x`. -/
def sqrtOkB (k : ℤ) (L : List (ℤ × ℤ)) (x : ℤ) : Bool :=
  let n := x ^ 3 + k
  decide (Int.sqrt n ^ 2 ≠ n) || (decide ((x, Int.sqrt n) ∈ L) && decide ((x, -Int.sqrt n) ∈ L))

/-- The finite check with supplied roots `XS`; an `x` without a supplied root falls back to
`Int.sqrt` (used for the small candidates of reducible classes). -/
def pointsRB (k : ℤ) (X : List ℤ) (XS L : List (ℤ × ℤ)) : Bool :=
  (X.all fun x => XS.any (fun p => decide (p.1 = x)) || sqrtOkB k L x) && XS.all (rootOkB k L) &&
    L.all fun w => decide (w.2 ^ 2 = w.1 ^ 3 + k)

lemma abs_eq_of_floor {y s : ℤ} (hs : 0 ≤ s) (h1 : s ^ 2 ≤ y ^ 2) (h2 : y ^ 2 < (s + 1) ^ 2) :
    y = s ∨ y = -s := by
  have ha : |y| ^ 2 = y ^ 2 := sq_abs y
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have l1 : s ≤ |y| := by nlinarith
  have l2 : |y| < s + 1 := by nlinarith
  rcases abs_choice y with h | h <;> [left; right] <;> omega

/-- **The complete list**, under the class-list premise, with supplied square roots. -/
theorem complete_of_sols_root {k : ℤ} {cs : List ((ℤ × ℤ × ℤ × ℤ) × List (ℤ × ℤ))} {XS L : List (ℤ × ℤ)}
    (hcls : ClassList k (cs.map Prod.fst)) (hs : ∀ c ∈ cs, SolsIn c.1 c.2)
    (hL : pointsRB k (cs.flatMap fun c => c.2.map fun w => hess c.1 w.1 w.2) XS L = true) (x y : ℤ) :
    y ^ 2 = x ^ 3 + k ↔ (x, y) ∈ L := by
  simp only [pointsRB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hL
  obtain ⟨⟨hX, hR⟩, hP⟩ := hL
  constructor
  · intro h
    rcases hX x (x_mem hcls hs h) with ⟨p, hp, rfl⟩ | hq
    swap
    · simp only [sqrtOkB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hq
      rcases hq with hn | ⟨h1, h2⟩
      · exact absurd (sqrt_sq_of h) hn
      · rcases sq_cases h with e | e <;> rw [e]
        · exact h1
        · exact h2
    have hr := hR p hp
    simp only [rootOkB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
    rcases hr with hn | ⟨⟨⟨hs0, h1⟩, h2⟩, hne | ⟨hm1, hm2⟩⟩
    · nlinarith [sq_nonneg y]
    · exfalso
      rcases abs_eq_of_floor hs0 (by rw [h]; exact h1) (by rw [h]; exact h2) with e | e <;>
        exact hne (by simpa [e, neg_sq] using h)
    · rcases abs_eq_of_floor hs0 (by rw [h]; exact h1) (by rw [h]; exact h2) with e | e <;> rw [e]
      · exact hm1
      · exact hm2
  · intro hm
    exact hP _ hm

/-! ### Reducible classes with supplied square roots

`ReducibleThue.redSols` computes `Int.sqrt` of a discriminant in the kernel; for some curves
(`k = 97`) that unfolding exhausts memory. `redSolsR` takes the two roots as data, and `rootB`
checks them by multiplication only. -/

open ReducibleThue

/-- `r` is the integer square root of `D` (`r = 0` when `D < 0`). -/
def rootB (D r : ℤ) : Bool :=
  decide (0 ≤ r) && decide (r * r ≤ max D 0) && decide (max D 0 < (r + 1) * (r + 1))

lemma sqrt_of_rootB {D r : ℤ} (h : rootB D r = true) : Int.sqrt D = r := by
  simp only [rootB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hD : ((D.toNat : ℕ) : ℤ) = max D 0 := Int.toNat_eq_max D
  have hr : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg h0
  have e : r.toNat = Nat.sqrt D.toNat := by
    rw [Nat.eq_sqrt]
    constructor
    · zify; rw [hD, hr]; exact h1
    · zify; rw [hD, hr]; exact h2
  rw [Int.sqrt, ← e, hr]

/-- `tCands` with the square root supplied. -/
def tCandsR (α β γ r : ℤ) : List ℤ :=
  if α ≠ 0 then
    ([r, -r].filter fun z => (z - β) % (2 * α) = 0).map fun z => (z - β) / (2 * α)
  else if β ≠ 0 then (if γ % β = 0 then [-γ / β] else []) else []

lemma tCands_eq {α β γ r : ℤ} (h : rootB (β ^ 2 - 4 * α * γ) r = true) : tCands α β γ = tCandsR α β γ r := by
  unfold tCands tCandsR
  rw [sqrt_of_rootB h]

/-- `redSols` with the two square roots supplied (`s = 1`, `s = −1`). -/
def redSolsR (c : RedCert) (r₁ r₂ : ℤ) : List (ℤ × ℤ) :=
  (tCandsR (alpha c) (beta c 1) (gamma c 1) r₁).map (fun t => (1 * c.h + c.q * t, 1 * c.j - c.p * t)) ++
    (tCandsR (alpha c) (beta c (-1)) (gamma c (-1)) r₂).map (fun t => (-1 * c.h + c.q * t, -1 * c.j - c.p * t))

lemma redSols_eq {c : RedCert} {r₁ r₂ : ℤ}
    (h₁ : rootB (beta c 1 ^ 2 - 4 * alpha c * gamma c 1) r₁ = true)
    (h₂ : rootB (beta c (-1) ^ 2 - 4 * alpha c * gamma c (-1)) r₂ = true) :
    redSols c = redSolsR c r₁ r₂ := by
  simp only [redSols, redSolsR, List.flatMap_cons, List.flatMap_nil, List.append_nil, tCands_eq h₁, tCands_eq h₂]

/-- **A reducible class with supplied roots.** -/
theorem solsIn_of_redR {G : ℤ × ℤ × ℤ × ℤ} {c : RedCert} {r₁ r₂ : ℤ}
    (h : redCertB (G.1, 3 * G.2.1, 3 * G.2.2.1, G.2.2.2) c = true)
    (h₁ : rootB (beta c 1 ^ 2 - 4 * alpha c * gamma c 1) r₁ = true)
    (h₂ : rootB (beta c (-1) ^ 2 - 4 * alpha c * gamma c (-1)) r₂ = true) :
    SolsIn G (redSolsR c r₁ r₂) := by
  rw [← redSols_eq h₁ h₂]; exact solsIn_of_red h

end PerfectPower.PositiveKCurveRoot
