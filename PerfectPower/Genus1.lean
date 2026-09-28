import PerfectPower.Reflect

namespace PerfectPower.Genus1

open PerfectPower PerfectPower.Reflect

/-! ### Genus-one families reduced to Weierstrass models (checked reduction, external points)

For `m^2 = a n^3 + b n^2 + c n + e` put `U = 9 a n + 3 b`, `V = 27 a m`; then
`V^2 - (U^3 + A U + B) = 729 a^2 (m^2 - F(n))` with `A = 81 a c - 27 b^2`,
`B = 54 b^3 - 243 a b c + 729 a^2 e`.  For `m^3 = a n^2 + b n + c` put `U = 4 a m`,
`V = 4 a (2 a n + b)`; then `V^2 - (U^3 + 16 a^2 Δ) = 64 a^3 (F(n) - m^3)`, `Δ = b^2 - 4 a c`.

The integral points of the model are an explicit hypothesis `IntegralPointsOn A B L` (every
integral point is in the list `L`), certified outside Lean by Sage.  Given it, the checkers
`cubicOK` and `quadOK` (kernel evaluation) and their soundness theorems prove the complete hit
list: every listed point is re-verified to lie on the model, every point pulls back to a recorded
hit or to nothing, and every recorded hit carries a witness.  **Completeness of `L` is not proved
here.** -/

/-- The hypothesis: every integral point of `V^2 = U^3 + A U + B` is listed. -/
def IntegralPointsOn (A B : ℤ) (L : List (ℤ × ℤ)) : Prop :=
  ∀ U V : ℤ, V ^ 2 = U ^ 3 + A * U + B → (U, V) ∈ L

/-- The Weierstrass model of `m^2 = a n^3 + b n^2 + c n + e`. -/
def cubicModel (a b c e : ℤ) : ℤ × ℤ :=
  (81 * a * c - 27 * b ^ 2, 54 * b ^ 3 - 243 * a * b * c + 729 * a ^ 2 * e)

/-- The Weierstrass model of `m^3 = a n^2 + b n + c`. -/
def quadModel (a b c : ℤ) : ℤ × ℤ := (0, 16 * a ^ 2 * (b ^ 2 - 4 * a * c))

/-- Pull a model point back to an index `n ≥ 1` (cubic case). -/
def cubicPull (a b : ℤ) (p : ℤ × ℤ) : Option ℕ :=
  if 9 * a ∣ p.1 - 3 * b ∧ 27 * a ∣ p.2 ∧ 1 ≤ (p.1 - 3 * b) / (9 * a) then
    some ((p.1 - 3 * b) / (9 * a)).toNat else none

/-- Pull a model point back to an index `n ≥ 1` (cube-of-quadratic case). -/
def quadPull (a b : ℤ) (p : ℤ × ℤ) : Option ℕ :=
  if 4 * a ∣ p.1 ∧ 4 * a ∣ p.2 ∧ 2 * a ∣ p.2 / (4 * a) - b ∧ 1 ≤ (p.2 / (4 * a) - b) / (2 * a) then
    some ((p.2 / (4 * a) - b) / (2 * a)).toNat else none

/-- The cubic checker: `hits` lists `(n, m)` with `m^2 = F(n)`. -/
def cubicOK (a b c e : ℤ) (L : List (ℤ × ℤ)) (hits : List (ℕ × ℤ)) : Bool :=
  decide (a ≠ 0) &&
  L.all (fun p => p.2 ^ 2 == p.1 ^ 3 + (cubicModel a b c e).1 * p.1 + (cubicModel a b c e).2) &&
  L.all (fun p => match cubicPull a b p with
    | none => true
    | some n => (hits.map Prod.fst).contains n) &&
  hits.all (fun h => 1 ≤ h.1 && h.2 ^ 2 == ev [e, c, b, a] h.1)

/-- The cube-of-quadratic checker: `hits` lists `(n, m)` with `m^3 = F(n)`. -/
def quadOK (a b c : ℤ) (L : List (ℤ × ℤ)) (hits : List (ℕ × ℤ)) : Bool :=
  decide (a ≠ 0) &&
  L.all (fun p => p.2 ^ 2 == p.1 ^ 3 + (quadModel a b c).1 * p.1 + (quadModel a b c).2) &&
  L.all (fun p => match quadPull a b p with
    | none => true
    | some n => (hits.map Prod.fst).contains n) &&
  hits.all (fun h => 1 ≤ h.1 && h.2 ^ 3 == ev [c, b, a] h.1)

lemma ev_cubic (a b c e x : ℤ) : ev [e, c, b, a] x = a * x ^ 3 + b * x ^ 2 + c * x + e := by
  simp [ev]; ring

lemma ev_quad (a b c x : ℤ) : ev [c, b, a] x = a * x ^ 2 + b * x + c := by
  simp [ev]; ring

/-- **Soundness, cubic case.** -/
theorem cubic_sound {a b c e : ℤ} {L : List (ℤ × ℤ)} {hits : List (ℕ × ℤ)}
    (hpts : IntegralPointsOn (cubicModel a b c e).1 (cubicModel a b c e).2 L)
    (hok : cubicOK a b c e L hits = true) (n : ℕ) (hn : 1 ≤ n) :
    IsHit 2 (ev [e, c, b, a] n) ↔ n ∈ hits.map Prod.fst := by
  simp only [cubicOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨ha, -⟩, hpull⟩, hwit⟩ := hok
  constructor
  · rintro ⟨m, hm⟩
    rw [ev_cubic] at hm
    have hmem := hpts (9 * a * n + 3 * b) (27 * a * m) (by
      simp only [cubicModel]; linear_combination (-(729 * a ^ 2)) * hm)
    have := hpull _ hmem
    have hp : cubicPull a b (9 * a * n + 3 * b, 27 * a * m) = some n := by
      have e1 : (9 * a * (n : ℤ) + 3 * b - 3 * b) / (9 * a) = n := by
        rw [show 9 * a * (n : ℤ) + 3 * b - 3 * b = 9 * a * n by ring]
        exact Int.mul_ediv_cancel_left _ (by positivity)
      simp only [cubicPull, e1]
      rw [if_pos ⟨⟨n, by ring⟩, ⟨m, by ring⟩, by exact_mod_cast hn⟩]
      simp
    rw [hp] at this
    simpa using this
  · intro hmem
    obtain ⟨⟨k, m⟩, hkm, rfl⟩ := List.mem_map.mp hmem
    have := hwit _ hkm
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨m, this.2.symm⟩

/-- **Soundness, cube-of-quadratic case.** -/
theorem quad_sound {a b c : ℤ} {L : List (ℤ × ℤ)} {hits : List (ℕ × ℤ)}
    (hpts : IntegralPointsOn (quadModel a b c).1 (quadModel a b c).2 L)
    (hok : quadOK a b c L hits = true) (n : ℕ) (hn : 1 ≤ n) :
    IsHit 3 (ev [c, b, a] n) ↔ n ∈ hits.map Prod.fst := by
  simp only [quadOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨ha, -⟩, hpull⟩, hwit⟩ := hok
  constructor
  · rintro ⟨m, hm⟩
    rw [ev_quad] at hm
    have hmem := hpts (4 * a * m) (4 * a * (2 * a * n + b)) (by
      simp only [quadModel]; linear_combination (64 * a ^ 3) * hm)
    have := hpull _ hmem
    have hp : quadPull a b (4 * a * m, 4 * a * (2 * a * n + b)) = some n := by
      have h4 : 4 * a ≠ 0 := by positivity
      have h2 : 2 * a ≠ 0 := by positivity
      have e1 : 4 * a * (2 * a * (n : ℤ) + b) / (4 * a) = 2 * a * n + b :=
        Int.mul_ediv_cancel_left _ h4
      have e2 : (2 * a * (n : ℤ) + b - b) / (2 * a) = n := by
        rw [show 2 * a * (n : ℤ) + b - b = 2 * a * n by ring]; exact Int.mul_ediv_cancel_left _ h2
      simp only [quadPull, e1, e2]
      rw [if_pos ⟨⟨m, by ring⟩, ⟨2 * a * n + b, by ring⟩, ⟨n, by ring⟩, by exact_mod_cast hn⟩]
      simp
    rw [hp] at this
    simpa using this
  · intro hmem
    obtain ⟨⟨k, m⟩, hkm, rfl⟩ := List.mem_map.mp hmem
    have := hwit _ hkm
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨m, this.2.symm⟩

end PerfectPower.Genus1
