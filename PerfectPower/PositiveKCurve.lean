import PerfectPower.MordellCubicForm
import PerfectPower.ReducibleThue

/-!
# Positive `k`: complete point lists from the class solutions

Under `ClassList k Gs`, a point `(x, y)` of `y² = x³ + k` gives a class `G ∈ Gs` and a solution
`G(u, v) = 1` with `x = H_G(u, v)`, where `H_G = (b² − ac)u² + (bc − ad)uv + (c² − bd)v²` is the
Hessian covariant (`x_mem`): `H` at `(1, 0)` of `(1, 0, −x, −2y)` is `x`, and
`H_{G ∘ T}(1, 0) = det(T)² H_G(T(1, 0))` (`hess_act`).  So the `x`-coordinates are read off the
solution lists of the classes, and `y = ±√(x³ + k)`.

A class's solution list comes from a residue obstruction (`solsIn_of_loc`: no solution) or from a
factorization (`solsIn_of_red`, `ReducibleThue.redSolsIn`).  `complete_of_sols` assembles the
curve theorem `y² = x³ + k ↔ (x, y) ∈ L`, still under the class-list premise.
-/

namespace PerfectPower.PositiveKCurve

open PerfectPower MordellCubicForm ReducibleThue

/-- The Hessian covariant of `G = (a, b, c, d)` (shape `(a, 3b, 3c, d)`) at `(u, v)`. -/
def hess (G : ℤ × ℤ × ℤ × ℤ) (u v : ℤ) : ℤ :=
  (G.2.1 ^ 2 - G.1 * G.2.2.1) * u ^ 2 + (G.2.1 * G.2.2.1 - G.1 * G.2.2.2) * u * v +
    (G.2.2.1 ^ 2 - G.2.1 * G.2.2.2) * v ^ 2

theorem hess_act (G : ℤ × ℤ × ℤ × ℤ) (p q r s : ℤ) :
    hess (act G p q r s) 1 0 = (p * s - q * r) ^ 2 * hess G p r := by
  obtain ⟨a, b, c, d⟩ := G
  simp only [hess, act]
  ring

/-- Every solution of `G = 1` is in `S`. -/
def SolsIn (G : ℤ × ℤ × ℤ × ℤ) (S : List (ℤ × ℤ)) : Prop := ∀ u v : ℤ, ev G u v = 1 → (u, v) ∈ S

/-- **The `x`-coordinates come from the class solutions.** -/
theorem x_mem {k : ℤ} {cs : List ((ℤ × ℤ × ℤ × ℤ) × List (ℤ × ℤ))}
    (hcls : ClassList k (cs.map Prod.fst)) (hs : ∀ c ∈ cs, SolsIn c.1 c.2) {x y : ℤ}
    (h : y ^ 2 = x ^ 3 + k) : x ∈ cs.flatMap fun c => c.2.map fun w => hess c.1 w.1 w.2 := by
  obtain ⟨hd, hv⟩ := form_of_point h
  obtain ⟨G, hG, p, q, r, s, hdet, hT⟩ := hcls _ hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hG
  have hev : ev c.1 p r = 1 := by
    have := ev_act c.1 p q r s 1 0
    rw [hT, hv] at this
    simpa using this.symm
  have hx : hess c.1 p r = x := by
    have := hess_act c.1 p q r s
    rw [hT, hdet, one_mul] at this
    rw [← this]
    simp [hess]
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨c, hc, (p, r), hs c hc p r hev, hx⟩

theorem solsIn_of_loc {G : ℤ × ℤ × ℤ × ℤ} {m : ℕ} (hm : 0 < m) (h : locImpB G m = true) :
    SolsIn G [] := fun u v hv => absurd hv (locImpB_sound hm h u v)

theorem ev_eq_evS (G : ℤ × ℤ × ℤ × ℤ) (u v : ℤ) :
    ev G u v = evS (G.1, 3 * G.2.1, 3 * G.2.2.1, G.2.2.2) u v := by
  obtain ⟨a, b, c, d⟩ := G
  show a * u ^ 3 + 3 * b * u ^ 2 * v + 3 * c * u * v ^ 2 + d * v ^ 3 =
    a * u ^ 3 + 3 * b * u ^ 2 * v + 3 * c * u * v ^ 2 + d * v ^ 3
  rfl

theorem solsIn_of_red {G : ℤ × ℤ × ℤ × ℤ} {c : RedCert}
    (h : redCertB (G.1, 3 * G.2.1, 3 * G.2.2.1, G.2.2.2) c = true) : SolsIn G (redSols c) :=
  fun u v hv => redSolsIn h (by rwa [← ev_eq_evS])

lemma sq_cases {y n : ℤ} (h : y ^ 2 = n) : y = Int.sqrt n ∨ y = -Int.sqrt n := by
  have : Int.sqrt n = (y.natAbs : ℤ) := by rw [← h, sq, Int.sqrt_eq]
  rw [this]
  rcases Int.natAbs_eq y with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by omega)

lemma sqrt_sq_of {y n : ℤ} (h : y ^ 2 = n) : Int.sqrt n ^ 2 = n := by
  have : Int.sqrt n = (y.natAbs : ℤ) := by rw [← h, sq, Int.sqrt_eq]
  rw [this, Int.natAbs_sq, h]

/-- The finite check: every candidate `x` with `x³ + k` a square has both its points in `L`, and
every listed point is on the curve. -/
def pointsB (k : ℤ) (X : List ℤ) (L : List (ℤ × ℤ)) : Bool :=
  (X.all fun x => let n := x ^ 3 + k
    decide (Int.sqrt n ^ 2 ≠ n) || (decide ((x, Int.sqrt n) ∈ L) && decide ((x, -Int.sqrt n) ∈ L))) &&
  L.all fun w => decide (w.2 ^ 2 = w.1 ^ 3 + k)

/-- **The complete list**, under the class-list premise. -/
theorem complete_of_sols {k : ℤ} {cs : List ((ℤ × ℤ × ℤ × ℤ) × List (ℤ × ℤ))} {L : List (ℤ × ℤ)}
    (hcls : ClassList k (cs.map Prod.fst)) (hs : ∀ c ∈ cs, SolsIn c.1 c.2)
    (hL : pointsB k (cs.flatMap fun c => c.2.map fun w => hess c.1 w.1 w.2) L = true) (x y : ℤ) :
    y ^ 2 = x ^ 3 + k ↔ (x, y) ∈ L := by
  simp only [pointsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hL
  obtain ⟨hX, hP⟩ := hL
  constructor
  · intro h
    have hx := x_mem hcls hs h
    rcases hX x hx with hn | ⟨h1, h2⟩
    · exact absurd (sqrt_sq_of h) hn
    · rcases sq_cases h with e | e <;> rw [e]
      · exact h1
      · exact h2
  · intro hm
    exact hP _ hm

end PerfectPower.PositiveKCurve
