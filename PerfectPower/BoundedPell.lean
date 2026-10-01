import PerfectPower.QuadOrbit

/-!
# Bounded Pell queries, kernel-checked

A bounded query asks for **every** integer solution of `a S² + b S + c = q N² + p N + r` with
`lo ≤ N ≤ hi`.  The solution set can be infinite without the bound, and the bound can be huge
(`hi = 10⁹`).  This file turns such a query into a theorem the kernel checks by evaluation.

* `orbit_fst_pow`: along a unit orbit the `X` coordinate at least doubles at every step,
  `2^j X₀ ≤ X_j`.  So a bound `X ≤ Xmax` leaves only `log₂ Xmax` orbit steps: no root box, no
  scan of `[lo, hi]`.
* `bounded_list`: under `QuadOrbit.seedCheck`, every solution of `X² − D Y² = Δ` with
  `0 < X ≤ Xmax`, `Y ≥ 0` is in an explicit list, checked by enumerating `J` orbit steps.
* `quad_bounded`: the query in its own variables.  With `X = a(2qN + p)`, `Y = 2aS + b`,
  `D = a q` and `Δ = a(q(4ac − b²) − a(4qr − p²))`,

    `a S² + b S + c = q N² + p N + r  ⇔  X² − D Y² = Δ`     (for `a, q ≠ 0`),

  and the finite checks recover `(N, S)` from `(X, ±Y)`.  The range must satisfy
  `2 q lo + p > 0` (so `X > 0`); a query reaching below it is split, and `N ↦ −N` handles the
  other side.
-/

namespace PerfectPower.BoundedPell

open PerfectPower PellExact FilteredPell QuadOrbit

variable {D u v Δ : ℤ}

/-- **Each unit step at least doubles `X`.** -/
theorem orbit_fst_pow (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v)
    {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) : ∀ j : ℕ, 2 ^ j * ρ.1 ≤ (unitOrbit D u v ρ j).1
  | 0 => by simp [unitOrbit]
  | j + 1 => by
    have ih := orbit_fst_pow hD hu hu1 hv hρ j
    obtain ⟨hX, hY, -⟩ := orbit_sol hD hu hu1.le hv hρ j
    rw [orbit_succ]
    simp only [unitAct]
    have h0 : 0 ≤ D * (unitOrbit D u v ρ j).2 * v := by positivity
    have h2 : 2 * (unitOrbit D u v ρ j).1 ≤ (unitOrbit D u v ρ j).1 * u := by nlinarith
    rw [pow_succ]
    nlinarith

/-- **Bounded completeness**: every solution with `X ≤ Xmax` is listed. -/
theorem bounded_list (hD : 0 < D) (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1)
    {seeds : List (ℤ × ℤ)} {Ymax : ℕ} (hc : seedCheck D u v Δ seeds Ymax = true)
    (Xmax : ℤ) (J : ℕ) (hJ : Xmax < 2 ^ J) (L : List (ℤ × ℤ))
    (hL : (seeds.all fun ρ => (List.range J).all fun j =>
      !decide ((unitOrbit D u v ρ j).1 ≤ Xmax) || decide (unitOrbit D u v ρ j ∈ L)) = true)
    (p : ℤ × ℤ) (hp : Sol D Δ p) (hx : p.1 ≤ Xmax) : p ∈ L := by
  obtain ⟨ρ, hρ, j, rfl⟩ := (complete hD hu1 hv hu hc p).mp hp
  have hρs := (seeds_roots hc ρ hρ).1
  have hpow := orbit_fst_pow hD.le hu hu1 hv.le hρs j
  have hρ1 : 1 ≤ ρ.1 := hρs.1
  have hj : j < J := by
    by_contra hcon
    push_neg at hcon
    have : (2 : ℤ) ^ J ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hcon
    nlinarith [pow_pos (by norm_num : (0 : ℤ) < 2) j]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, not_le] at hL
  rcases hL ρ hρ j hj with h | h
  · exact absurd hx (not_le.mpr h)
  · exact h

/-- The query's equation is the norm equation `X² − D Y² = Δ`. -/
theorem quad_iff_norm (a b c q p r N S : ℤ) (ha : a ≠ 0) (hq : q ≠ 0) :
    a * S ^ 2 + b * S + c = q * N ^ 2 + p * N + r ↔
      (a * (2 * q * N + p)) ^ 2 - (a * q) * (2 * a * S + b) ^ 2 =
        a * (q * (4 * a * c - b ^ 2) - a * (4 * q * r - p ^ 2)) := by
  have key : (a * (2 * q * N + p)) ^ 2 - (a * q) * (2 * a * S + b) ^ 2 -
      a * (q * (4 * a * c - b ^ 2) - a * (4 * q * r - p ^ 2)) =
      4 * a ^ 2 * q * ((q * N ^ 2 + p * N + r) - (a * S ^ 2 + b * S + c)) := by ring
  have h4 : (4 * a ^ 2 * q) ≠ 0 := by positivity
  constructor
  · intro h
    have : (a * (2 * q * N + p)) ^ 2 - (a * q) * (2 * a * S + b) ^ 2 -
        a * (q * (4 * a * c - b ^ 2) - a * (4 * q * r - p ^ 2)) = 0 := by rw [key, h]; ring
    linarith
  · intro h
    have : 4 * a ^ 2 * q * ((q * N ^ 2 + p * N + r) - (a * S ^ 2 + b * S + c)) = 0 := by
      rw [← key]; linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 h4
    · linarith

/-- The recovery check: every listed `(X, Y)` and sign of `Y` that comes from some `(N, S)` with
`lo ≤ N ≤ hi` gives a pair in `L0`. -/
def recoverB (a b q p lo hi : ℤ) (L L0 : List (ℤ × ℤ)) : Bool :=
  L.all fun xy => [xy.2, -xy.2].all fun Y =>
    !(decide ((xy.1 - a * p) % (2 * a * q) = 0) && decide ((Y - b) % (2 * a) = 0)) ||
      (let N := (xy.1 - a * p) / (2 * a * q)
       let S := (Y - b) / (2 * a)
       !(decide (lo ≤ N) && decide (N ≤ hi)) || decide ((N, S) ∈ L0))

/-- **A bounded quadratic query, in its own variables.**  Every solution with `lo ≤ N ≤ hi`
is in `L0`, and every listed pair is a solution in range. -/
theorem quad_bounded (a b c q p r lo hi : ℤ) (ha : 0 < a) (hq : 0 < q) (hlo : 0 < 2 * q * lo + p)
    (hD : 0 < a * q) (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - (a * q) * v ^ 2 = 1)
    {seeds : List (ℤ × ℤ)} {Ymax : ℕ}
    (hc : seedCheck (a * q) u v (a * (q * (4 * a * c - b ^ 2) - a * (4 * q * r - p ^ 2))) seeds Ymax = true)
    (J : ℕ) (hJ : a * (2 * q * hi + p) < 2 ^ J) (L L0 : List (ℤ × ℤ))
    (hL : (seeds.all fun ρ => (List.range J).all fun j =>
      !decide ((unitOrbit (a * q) u v ρ j).1 ≤ a * (2 * q * hi + p)) ||
        decide (unitOrbit (a * q) u v ρ j ∈ L)) = true)
    (hrec : recoverB a b q p lo hi L L0 = true)
    (hL0 : (L0.all fun ns => decide (lo ≤ ns.1) && decide (ns.1 ≤ hi) &&
      decide (a * ns.2 ^ 2 + b * ns.2 + c = q * ns.1 ^ 2 + p * ns.1 + r)) = true)
    (N S : ℤ) (h1 : lo ≤ N) (h2 : N ≤ hi) :
    a * S ^ 2 + b * S + c = q * N ^ 2 + p * N + r ↔ (N, S) ∈ L0 := by
  constructor
  · intro h
    have hn := (quad_iff_norm a b c q p r N S ha.ne' hq.ne').mp h
    set X := a * (2 * q * N + p) with hXdef
    set Y := 2 * a * S + b with hYdef
    have hXpos : 0 < X := by
      have : 0 < 2 * q * N + p := by nlinarith
      positivity
    have hsol : Sol (a * q) (a * (q * (4 * a * c - b ^ 2) - a * (4 * q * r - p ^ 2))) (X, |Y|) :=
      ⟨hXpos, abs_nonneg Y, by simp only [sq_abs]; exact hn⟩
    have hXle : X ≤ a * (2 * q * hi + p) := by
      have : 2 * q * N + p ≤ 2 * q * hi + p := by nlinarith
      exact mul_le_mul_of_nonneg_left this ha.le
    have hmem := bounded_list hD hu1 hv hu hc _ J hJ L hL (X, |Y|) hsol hXle
    simp only [recoverB, List.all_eq_true, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq] at hrec
    have hr := hrec (X, |Y|) hmem
    have hNx : (X - a * p) = (2 * a * q) * N := by rw [hXdef]; ring
    have hdivN : (X - a * p) % (2 * a * q) = 0 := by rw [hNx]; simp
    have hNq : (X - a * p) / (2 * a * q) = N := by
      rw [hNx]; exact Int.mul_ediv_cancel_left N (by positivity)
    rcases abs_choice Y with hy | hy
    · have hSy : (|Y| - b) = (2 * a) * S := by rw [hy, hYdef]; ring
      have hdivS : (|Y| - b) % (2 * a) = 0 := by rw [hSy]; simp
      have hSq : (|Y| - b) / (2 * a) = S := by rw [hSy]; exact Int.mul_ediv_cancel_left S (by positivity)
      rcases hr.1 with h' | h'
      · rcases h' with h' | h'
        · exact absurd hdivN h'
        · exact absurd hdivS h'
      · rw [hNq, hSq] at h'
        rcases h' with h' | h'
        · rcases h' with h' | h'
          · exact absurd h1 h'
          · exact absurd h2 h'
        · exact h'
    · have hSy : (-|Y| - b) = (2 * a) * S := by rw [hy, hYdef]; ring
      have hdivS : (-|Y| - b) % (2 * a) = 0 := by rw [hSy]; simp
      have hSq : (-|Y| - b) / (2 * a) = S := by rw [hSy]; exact Int.mul_ediv_cancel_left S (by positivity)
      rcases hr.2 with h' | h'
      · rcases h' with h' | h'
        · exact absurd hdivN h'
        · exact absurd hdivS h'
      · rw [hNq, hSq] at h'
        rcases h' with h' | h'
        · rcases h' with h' | h'
          · exact absurd h1 h'
          · exact absurd h2 h'
        · exact h'
  · intro h
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hL0
    exact (hL0 (N, S) h).2

end PerfectPower.BoundedPell
