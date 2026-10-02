import Mathlib.Tactic

/-!
# Reducible cubic Thue equations, solved completely

For `F(u, v) = (pu + qv)(Au² + Buv + Cv²)` the equation `F(u, v) = 1` forces both factors to be
the same sign `s = ±1`.  With a Bezout pair `ph + qj = 1`, every solution of `pu + qv = s` is
`u = sh + qt`, `v = sj − pt` with `t = ju − hv`, and the quadratic factor becomes
`αt² + βt + γ = 0`.  Its integer roots satisfy `(2αt + β)² = β² − 4αγ`, so `|2αt + β|` is the
integer square root of the discriminant (`tCands`): there is no search bound.

`redSolsIn` gives every solution of `F = 1` in an explicit list (`redSols`), from a certificate
checked by `redCertB`.  Design and the 54 positive-`k` certificates are from the five-frontiers
review of `d2c2a91`.
-/

namespace PerfectPower.ReducibleThue

/-- `a u³ + B u²v + C uv² + d v³` for `F = (a, B, C, d)` (standard coefficients). -/
def evS (F : ℤ × ℤ × ℤ × ℤ) (u v : ℤ) : ℤ :=
  F.1 * u ^ 3 + F.2.1 * u ^ 2 * v + F.2.2.1 * u * v ^ 2 + F.2.2.2 * v ^ 3

/-- A factorization certificate: `F = (pu + qv)(Au² + Buv + Cv²)` and `ph + qj = 1`. -/
structure RedCert where
  p : ℤ
  q : ℤ
  A : ℤ
  B : ℤ
  C : ℤ
  h : ℤ
  j : ℤ

/-- The quadratic in `t` for the sign `s`: `α t² + β t + γ`. -/
def alpha (c : RedCert) : ℤ := c.A * c.q ^ 2 - c.B * c.q * c.p + c.C * c.p ^ 2
def beta (c : RedCert) (s : ℤ) : ℤ := s * (2 * c.A * c.h * c.q + c.B * (c.j * c.q - c.h * c.p) - 2 * c.C * c.j * c.p)
def gamma (c : RedCert) (s : ℤ) : ℤ := s ^ 2 * (c.A * c.h ^ 2 + c.B * c.h * c.j + c.C * c.j ^ 2) - s

/-- The only possible integer roots of `α t² + β t + γ = 0` (one of `α`, `β` nonzero). -/
def tCands (α β γ : ℤ) : List ℤ :=
  if α ≠ 0 then
    let r : ℤ := Int.sqrt (β ^ 2 - 4 * α * γ)
    ([r, -r].filter fun z => (z - β) % (2 * α) = 0).map fun z => (z - β) / (2 * α)
  else if β ≠ 0 then (if γ % β = 0 then [-γ / β] else []) else []

theorem mem_tCands {α β γ t : ℤ} (hne : α ≠ 0 ∨ β ≠ 0) (ht : α * t ^ 2 + β * t + γ = 0) :
    t ∈ tCands α β γ := by
  unfold tCands
  by_cases hα : α ≠ 0
  · simp only [hα, ne_eq, not_false_eq_true, ↓reduceIte, List.mem_map, List.mem_filter,
      List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq]
    have hsq : (2 * α * t + β) ^ 2 = β ^ 2 - 4 * α * γ := by linear_combination 4 * α * ht
    have hr : Int.sqrt (β ^ 2 - 4 * α * γ) = ((2 * α * t + β).natAbs : ℤ) := by
      rw [← hsq, sq, Int.sqrt_eq]
    have h2 : (2 * α) ≠ 0 := by positivity
    rcases Int.natAbs_eq (2 * α * t + β) with he | he
    · refine ⟨Int.sqrt (β ^ 2 - 4 * α * γ), ⟨Or.inl rfl, ?_⟩, ?_⟩
      · rw [hr, ← he]; simp [Int.mul_emod_right]
      · rw [hr, ← he, show 2 * α * t + β - β = 2 * α * t by ring, Int.mul_ediv_cancel_left _ h2]
    · refine ⟨-Int.sqrt (β ^ 2 - 4 * α * γ), ⟨Or.inr rfl, ?_⟩, ?_⟩
      · rw [hr, show -((2 * α * t + β).natAbs : ℤ) = 2 * α * t + β by omega]
        simp [Int.mul_emod_right]
      · rw [hr, show -((2 * α * t + β).natAbs : ℤ) = 2 * α * t + β by omega,
          show 2 * α * t + β - β = 2 * α * t by ring, Int.mul_ediv_cancel_left _ h2]
  · have hα0 : α = 0 := not_not.mp hα
    have hβ : β ≠ 0 := hne.resolve_left (by simpa using hα0)
    subst hα0
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, hβ, not_false_eq_true]
    have hbt : β * t = -γ := by linarith
    have hd : γ % β = 0 := by
      have : γ = β * (-t) := by linarith
      rw [this]; simp
    simp only [hd, ↓reduceIte, List.mem_singleton]
    rw [show -γ = β * t by linarith, Int.mul_ediv_cancel_left _ hβ]

/-- The candidate solutions: for `s = ±1` and each candidate `t`, `(sh + qt, sj − pt)`. -/
def redSols (c : RedCert) : List (ℤ × ℤ) :=
  ([1, -1] : List ℤ).flatMap fun s =>
    (tCands (alpha c) (beta c s) (gamma c s)).map fun t => (s * c.h + c.q * t, s * c.j - c.p * t)

/-- The certificate: the factorization of `F`, the Bezout pair, and a nondegenerate quadratic. -/
def redCertB (F : ℤ × ℤ × ℤ × ℤ) (c : RedCert) : Bool :=
  decide (F.1 = c.p * c.A) && decide (F.2.1 = c.p * c.B + c.q * c.A) &&
  decide (F.2.2.1 = c.p * c.C + c.q * c.B) && decide (F.2.2.2 = c.q * c.C) &&
  decide (c.p * c.h + c.q * c.j = 1) &&
  decide (alpha c ≠ 0 ∨ beta c 1 ≠ 0) && decide (alpha c ≠ 0 ∨ beta c (-1) ≠ 0)

/-- **Every solution of `F(u, v) = 1` is in `redSols c`.** -/
theorem redSolsIn {F : ℤ × ℤ × ℤ × ℤ} {c : RedCert} (hc : redCertB F c = true) {u v : ℤ}
    (h : evS F u v = 1) : (u, v) ∈ redSols c := by
  obtain ⟨a, B', C', d⟩ := F
  obtain ⟨p, q, A, B, C, hh, j⟩ := c
  simp only [redCertB, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hb⟩, hn1⟩, hn2⟩ := hc
  have hf : (p * u + q * v) * (A * u ^ 2 + B * u * v + C * v ^ 2) = 1 := by
    simp only [evS] at h
    rw [h1, h2, h3, h4] at h
    linear_combination h
  set t := j * u - hh * v with ht
  have key : ∀ s : ℤ, s = 1 ∨ s = -1 → p * u + q * v = s → A * u ^ 2 + B * u * v + C * v ^ 2 = s →
      (u, v) ∈ redSols ⟨p, q, A, B, C, hh, j⟩ := by
    intro s hs hl hq
    have hu : u = s * hh + q * t := by rw [ht]; linear_combination hh * hl - u * hb
    have hv : v = s * j - p * t := by rw [ht]; linear_combination j * hl - v * hb
    have hq' : alpha ⟨p, q, A, B, C, hh, j⟩ * t ^ 2 + beta ⟨p, q, A, B, C, hh, j⟩ s * t +
        gamma ⟨p, q, A, B, C, hh, j⟩ s = 0 := by
      simp only [alpha, beta, gamma]
      rw [hu, hv] at hq
      linear_combination hq
    have hne : alpha ⟨p, q, A, B, C, hh, j⟩ ≠ 0 ∨ beta ⟨p, q, A, B, C, hh, j⟩ s ≠ 0 := by
      rcases hs with rfl | rfl
      · exact hn1
      · exact hn2
    have hmem := mem_tCands hne hq'
    simp only [redSols, List.mem_flatMap, List.mem_map]
    refine ⟨s, by rcases hs with rfl | rfl <;> simp, t, hmem, ?_⟩
    rw [← hu, ← hv]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hf with ⟨hl, hq⟩ | ⟨hl, hq⟩
  · exact key 1 (Or.inl rfl) hl hq
  · exact key (-1) (Or.inr rfl) hl hq

/-- The exact solution set: the candidates that are solutions. -/
theorem redSols_exact {F : ℤ × ℤ × ℤ × ℤ} {c : RedCert} (hc : redCertB F c = true) (u v : ℤ) :
    evS F u v = 1 ↔ (u, v) ∈ (redSols c).filter fun w => evS F w.1 w.2 = 1 := by
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => ⟨redSolsIn hc h, h⟩, fun h => h.2⟩

end PerfectPower.ReducibleThue
