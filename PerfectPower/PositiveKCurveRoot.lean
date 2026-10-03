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

/-- The finite check with supplied roots `XS`. -/
def pointsRB (k : ℤ) (X : List ℤ) (XS L : List (ℤ × ℤ)) : Bool :=
  (X.all fun x => XS.any fun p => decide (p.1 = x)) && XS.all (rootOkB k L) &&
    L.all fun w => decide (w.2 ^ 2 = w.1 ^ 3 + k)

lemma abs_eq_of_floor {y s : ℤ} (hs : 0 ≤ s) (h1 : s ^ 2 ≤ y ^ 2) (h2 : y ^ 2 < (s + 1) ^ 2) :
    y = s ∨ y = -s := by
  have ha : |y| ^ 2 = y ^ 2 := sq_abs y
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have l1 : s ≤ |y| := by nlinarith
  have l2 : |y| < s + 1 := by nlinarith
  have : |y| = s := by omega
  rcases abs_choice y with h | h <;> [left; right] <;> omega

/-- **The complete list**, under the class-list premise, with supplied square roots. -/
theorem complete_of_sols_root {k : ℤ} {cs : List ((ℤ × ℤ × ℤ × ℤ) × List (ℤ × ℤ))} {XS L : List (ℤ × ℤ)}
    (hcls : ClassList k (cs.map Prod.fst)) (hs : ∀ c ∈ cs, SolsIn c.1 c.2)
    (hL : pointsRB k (cs.flatMap fun c => c.2.map fun w => hess c.1 w.1 w.2) XS L = true) (x y : ℤ) :
    y ^ 2 = x ^ 3 + k ↔ (x, y) ∈ L := by
  simp only [pointsRB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hL
  obtain ⟨⟨hX, hR⟩, hP⟩ := hL
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := hX x (x_mem hcls hs h)
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

end PerfectPower.PositiveKCurveRoot
