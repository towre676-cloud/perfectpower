import PerfectPower.QuadOrbit
import Mathlib.Data.List.GetD

/-!
# Support for generated OEIS definitions

`python/perfectpower/oeis_dsl.py` translates supported OEIS definitions into a small language
and emits Lean for them (`Generated/OEISAuto.lean`).  The generated proofs use only the lemmas
here, the orbit coordinates (`FibOrbit`, `SqrtTwoOrbit`), and `decide`.

* `stride_one`, `stride_two`: for a sequence with `x(k+2) = t x(k+1) + x(k)` (the coordinates of
  the orbit of a unit of trace `t` and norm `-1`: `t = 1` for `φ`, `t = 2` for `1 + √2`),
  `x(k + 2α) = T_α x(k + α) - (-1)^α x(k)`, where `T_α` is the trace of the `α`-th power.  A
  subsequence `x(α n + β)` therefore satisfies an order-two recurrence, which is how generated
  proofs discharge an entry's stated recurrence.
* `rec_unique3`: uniqueness for order-three recurrences (affine coordinates such as
  `(A - 1)/2`).
* `gf2`, `gf3`: **the expansion of `P(x)/Q(x)`**, for `Q = 1 - q₁x - q₂x^2` or
  `1 - q₁x - q₂x^2 - q₃x^3`, defined by the coefficient recursion of `Q · A = P`:
  `a(n) = p_n + q₁ a(n-1) + q₂ a(n-2) (+ q₃ a(n-3))`.  `gf2_eq`, `gf3_eq`: such an expansion
  equals any sequence with the homogeneous recurrence that agrees with it on the first
  `deg P + order` indices (checked by `decide`).
-/

namespace PerfectPower.OEISLib

open PerfectPower

/-- Strides of a sequence with `x(k+2) = x(k+1) + x(k)` (traces `1, 3, 4, 7, 11, 18` of `φ^α`). -/
lemma stride_one {X : ℕ → ℤ} (hX : ∀ k, X (k + 2) = X (k + 1) + X k) (k : ℕ) :
    X (k + 2) = 1 * X (k + 1) + 1 * X k ∧
    X (k + 4) = 3 * X (k + 2) + (-1) * X k ∧
    X (k + 6) = 4 * X (k + 3) + 1 * X k ∧
    X (k + 8) = 7 * X (k + 4) + (-1) * X k ∧
    X (k + 10) = 11 * X (k + 5) + 1 * X k ∧
    X (k + 12) = 18 * X (k + 6) + (-1) * X k := by
  have h0 : X (k + 2) = X (k + 1) + X k := hX k
  have h1 : X (k + 3) = X (k + 2) + X (k + 1) := hX (k + 1)
  have h2 : X (k + 4) = X (k + 3) + X (k + 2) := hX (k + 2)
  have h3 : X (k + 5) = X (k + 4) + X (k + 3) := hX (k + 3)
  have h4 : X (k + 6) = X (k + 5) + X (k + 4) := hX (k + 4)
  have h5 : X (k + 7) = X (k + 6) + X (k + 5) := hX (k + 5)
  have h6 : X (k + 8) = X (k + 7) + X (k + 6) := hX (k + 6)
  have h7 : X (k + 9) = X (k + 8) + X (k + 7) := hX (k + 7)
  have h8 : X (k + 10) = X (k + 9) + X (k + 8) := hX (k + 8)
  have h9 : X (k + 11) = X (k + 10) + X (k + 9) := hX (k + 9)
  have h10 : X (k + 12) = X (k + 11) + X (k + 10) := hX (k + 10)
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Strides of a sequence with `x(k+2) = 2 x(k+1) + x(k)` (traces `2, 6, 14, 34` of `(1+√2)^α`). -/
lemma stride_two {X : ℕ → ℤ} (hX : ∀ k, X (k + 2) = 2 * X (k + 1) + X k) (k : ℕ) :
    X (k + 2) = 2 * X (k + 1) + 1 * X k ∧
    X (k + 4) = 6 * X (k + 2) + (-1) * X k ∧
    X (k + 6) = 14 * X (k + 3) + 1 * X k ∧
    X (k + 8) = 34 * X (k + 4) + (-1) * X k := by
  have h0 : X (k + 2) = 2 * X (k + 1) + X k := hX k
  have h1 : X (k + 3) = 2 * X (k + 2) + X (k + 1) := hX (k + 1)
  have h2 : X (k + 4) = 2 * X (k + 3) + X (k + 2) := hX (k + 2)
  have h3 : X (k + 5) = 2 * X (k + 4) + X (k + 3) := hX (k + 3)
  have h4 : X (k + 6) = 2 * X (k + 5) + X (k + 4) := hX (k + 4)
  have h5 : X (k + 7) = 2 * X (k + 6) + X (k + 5) := hX (k + 5)
  have h6 : X (k + 8) = 2 * X (k + 7) + X (k + 6) := hX (k + 6)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Strides of a sequence with `x(k+2) = 4 x(k+1) - x(k)` (traces `4, 14, 52, 194` of
`(2+√3)^α`, a unit of norm `+1`). -/
lemma stride_four {X : ℕ → ℤ} (hX : ∀ k, X (k + 2) = 4 * X (k + 1) - X k) (k : ℕ) :
    X (k + 2) = 4 * X (k + 1) + (-1) * X k ∧
    X (k + 4) = 14 * X (k + 2) + (-1) * X k ∧
    X (k + 6) = 52 * X (k + 3) + (-1) * X k ∧
    X (k + 8) = 194 * X (k + 4) + (-1) * X k := by
  have h0 := hX k
  have h1 := hX (k + 1)
  have h2 := hX (k + 2)
  have h3 := hX (k + 3)
  have h4 := hX (k + 4)
  have h5 := hX (k + 5)
  have h6 := hX (k + 6)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Strides of a sequence with `x(k+2) = t x(k+1) - x(k)` (a unit of norm `+1`, trace `t`). -/
lemma stride_norm1 {X : ℕ → ℤ} {t : ℤ} (hX : ∀ k, X (k + 2) = t * X (k + 1) - X k) (k : ℕ) :
    X (k + 2) = t * X (k + 1) + (-1) * X k ∧
    X (k + 4) = (t ^ 2 - 2) * X (k + 2) + (-1) * X k := by
  have h0 : X (k + 2) = t * X (k + 1) - X k := hX k
  have h1 : X (k + 3) = t * X (k + 2) - X (k + 1) := hX (k + 1)
  have h2 : X (k + 4) = t * X (k + 3) - X (k + 2) := hX (k + 2)
  exact ⟨by linarith, by linear_combination h2 + t * h1 + h0⟩

/-- The coordinates of the orbit of `(1, 0)` under a unit `u + v √D` of norm `+1`. -/
def ox (D u v : ℤ) (k : ℕ) : ℤ := (unitOrbit D u v (1, 0) k).1
/-- The second coordinate. -/
def oy (D u v : ℤ) (k : ℕ) : ℤ := (unitOrbit D u v (1, 0) k).2

lemma ox_rec {D u v : ℤ} (hu : u ^ 2 - D * v ^ 2 = 1) (k : ℕ) :
    ox D u v (k + 2) = 2 * u * ox D u v (k + 1) - ox D u v k :=
  (QuadOrbit.orbit_rec hu (1, 0) k).1

lemma oy_rec {D u v : ℤ} (hu : u ^ 2 - D * v ^ 2 = 1) (k : ℕ) :
    oy D u v (k + 2) = 2 * u * oy D u v (k + 1) - oy D u v k :=
  (QuadOrbit.orbit_rec hu (1, 0) k).2

/-- The `√3` family: `(2 + √3)^k = X_k + Y_k √3`. -/
lemma s3x_rec (k : ℕ) : ox 3 2 1 (k + 2) = 4 * ox 3 2 1 (k + 1) - ox 3 2 1 k := by
  have := ox_rec (D := 3) (u := 2) (v := 1) (by norm_num) k; linarith

lemma s3y_rec (k : ℕ) : oy 3 2 1 (k + 2) = 4 * oy 3 2 1 (k + 1) - oy 3 2 1 k := by
  have := oy_rec (D := 3) (u := 2) (v := 1) (by norm_num) k; linarith

/-- Order-three uniqueness. -/
lemma rec_unique3 {f g : ℕ → ℤ} (c d e : ℤ)
    (hf : ∀ n, f (n + 3) = c * f (n + 2) + d * f (n + 1) + e * f n)
    (hg : ∀ n, g (n + 3) = c * g (n + 2) + d * g (n + 1) + e * g n)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) : ∀ n, f n = g n := by
  have key : ∀ n, f n = g n ∧ f (n + 1) = g (n + 1) ∧ f (n + 2) = g (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2⟩
    | succ n ih => exact ⟨ih.2.1, ih.2.2, by rw [hf, hg, ih.1, ih.2.1, ih.2.2]⟩
  exact fun n => (key n).1

/-! ### Rational generating functions -/

/-- The expansion of `P(x) / (1 - q₁ x - q₂ x^2)`, `P = p₀ + p₁ x + ⋯` given as a list. -/
def gf2 (p : List ℤ) (q₁ q₂ : ℤ) : ℕ → ℤ
  | 0 => p.getD 0 0
  | 1 => p.getD 1 0 + q₁ * p.getD 0 0
  | n + 2 => p.getD (n + 2) 0 + q₁ * gf2 p q₁ q₂ (n + 1) + q₂ * gf2 p q₁ q₂ n

/-- The expansion of `P(x) / (1 - q₁ x - q₂ x^2 - q₃ x^3)`. -/
def gf3 (p : List ℤ) (q₁ q₂ q₃ : ℤ) : ℕ → ℤ
  | 0 => p.getD 0 0
  | 1 => p.getD 1 0 + q₁ * p.getD 0 0
  | 2 => p.getD 2 0 + q₁ * (p.getD 1 0 + q₁ * p.getD 0 0) + q₂ * p.getD 0 0
  | n + 3 => p.getD (n + 3) 0 + q₁ * gf3 p q₁ q₂ q₃ (n + 2) + q₂ * gf3 p q₁ q₂ q₃ (n + 1) +
      q₃ * gf3 p q₁ q₂ q₃ n

/-- An order-two expansion, scaled and shifted, equals a sequence with the matching recurrence
that agrees with it up to index `p.length + 1`. -/
theorem gf2_eq (p : List ℤ) (q₁ q₂ c s : ℤ) (r : ℕ) (g : ℕ → ℤ)
    (hg : ∀ n, g (n + 2) = q₁ * g (n + 1) + q₂ * g n + s * (1 - q₁ - q₂))
    (hstart : ∀ i < p.length + 2, c * gf2 p q₁ q₂ (i + r) + s = g i) :
    ∀ n, c * gf2 p q₁ q₂ (n + r) + s = g n := by
  have key : ∀ m n, n ≤ m → c * gf2 p q₁ q₂ (n + r) + s = g n := by
    intro m
    induction m with
    | zero => intro n hn; exact hstart n (by omega)
    | succ m ih =>
      intro n hn
      rcases Nat.lt_or_ge n (p.length + 2) with h | h
      · exact hstart n h
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        rw [show k + 2 + r = (k + r) + 2 by ring, gf2, hg, List.getD_eq_default _ _ (by omega),
          ← ih (k + 1) (by omega), ← ih k (by omega), show k + 1 + r = k + r + 1 by ring]
        ring
  exact fun n => key n n le_rfl

/-- The order-three version. -/
theorem gf3_eq (p : List ℤ) (q₁ q₂ q₃ c s : ℤ) (r : ℕ) (g : ℕ → ℤ)
    (hg : ∀ n, g (n + 3) = q₁ * g (n + 2) + q₂ * g (n + 1) + q₃ * g n + s * (1 - q₁ - q₂ - q₃))
    (hstart : ∀ i < p.length + 3, c * gf3 p q₁ q₂ q₃ (i + r) + s = g i) :
    ∀ n, c * gf3 p q₁ q₂ q₃ (n + r) + s = g n := by
  have key : ∀ m n, n ≤ m → c * gf3 p q₁ q₂ q₃ (n + r) + s = g n := by
    intro m
    induction m with
    | zero => intro n hn; exact hstart n (by omega)
    | succ m ih =>
      intro n hn
      rcases Nat.lt_or_ge n (p.length + 3) with h | h
      · exact hstart n h
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
        rw [show k + 3 + r = (k + r) + 3 by ring, gf3, hg, List.getD_eq_default _ _ (by omega),
          ← ih (k + 2) (by omega), ← ih (k + 1) (by omega), ← ih k (by omega),
          show k + 2 + r = k + r + 2 by ring, show k + 1 + r = k + r + 1 by ring]
        ring
  exact fun n => key n n le_rfl

/-! ### Sets `{k : D k^2 + c is a square}` -/

open PellExact QuadOrbit in
/-- **The set is the union of the second coordinates of the certified seed orbits.** -/
theorem setsq_iff (D u v c : ℤ) (seeds : List (ℤ × ℤ)) (Ymax : ℕ) (hD : 0 < D) (hu1 : 1 < u)
    (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1) (hcert : seedCheck D u v c seeds Ymax = true)
    (hx0 : ∀ k : ℤ, D * k ^ 2 + c ≠ 0) (k : ℤ) :
    (0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = D * k ^ 2 + c) ↔ ∃ ρ ∈ seeds, ∃ j, (unitOrbit D u v ρ j).2 = k := by
  constructor
  · rintro ⟨hk, x, hx⟩
    have hx' : 0 < |x| := abs_pos.mpr (fun h => hx0 k (by rw [← hx, h]; ring))
    have hp : Sol D c (|x|, k) := ⟨hx', hk, by show |x| ^ 2 - D * k ^ 2 = c; rw [sq_abs]; linarith⟩
    obtain ⟨ρ, hρ, j, hj⟩ := (complete hD hu1 hv hu hcert _).mp hp
    exact ⟨ρ, hρ, j, by rw [hj]⟩
  · rintro ⟨ρ, hρ, j, rfl⟩
    obtain ⟨-, hY, hN⟩ := (complete hD hu1 hv hu hcert _).mpr ⟨ρ, hρ, j, rfl⟩
    exact ⟨hY, (unitOrbit D u v ρ j).1, by linarith⟩

/-! ### Several seed orbits, in increasing order -/

open PellExact in
/-- On one equation, the unit preserves the order of the second coordinate. -/
lemma snd_act_lt {D u v Δ : ℤ} (hD : 0 < D) (hu1 : 0 < u) (hv : 0 < v) {p q : ℤ × ℤ}
    (hp : Sol D Δ p) (hq : Sol D Δ q) (h : p.2 < q.2) :
    (unitAct D u v p).2 < (unitAct D u v q).2 := by
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hX : p.1 ≤ q.1 := by
    by_contra hc
    push_neg at hc
    have h1 : q.1 ^ 2 < p.1 ^ 2 := by nlinarith
    have : p.2 ^ 2 < q.2 ^ 2 := by nlinarith
    nlinarith
  simp only [unitAct]
  nlinarith

open PellExact in
lemma orbit_snd_lt {D u v Δ : ℤ} (hD : 0 < D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u)
    (hv : 0 < v) {p q : ℤ × ℤ} (hp : Sol D Δ p) (hq : Sol D Δ q) (h : p.2 < q.2) :
    ∀ j, (unitOrbit D u v p j).2 < (unitOrbit D u v q j).2 := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih =>
    rw [orbit_succ, orbit_succ]
    exact snd_act_lt hD (by omega) hv (orbit_sol hD.le hu hu1.le hv.le hp j)
      (orbit_sol hD.le hu hu1.le hv.le hq j) ih

/-- The seed orbits merged: the `n`-th term is the second coordinate of seed `n mod s` at index
`n / s`. -/
def interleave (D u v : ℤ) (seeds : List (ℤ × ℤ)) (n : ℕ) : ℤ :=
  (unitOrbit D u v (seeds.getD (n % seeds.length) (0, 0)) (n / seeds.length)).2

/-- The finite order check: seeds sorted by `Y`, and the last below the first one's successor. -/
def orderB (D u v : ℤ) (seeds : List (ℤ × ℤ)) : Bool :=
  decide (seeds ≠ []) &&
  (List.range (seeds.length - 1)).all (fun i => decide ((seeds.getD i (0, 0)).2 < (seeds.getD (i + 1) (0, 0)).2)) &&
  decide ((seeds.getD (seeds.length - 1) (0, 0)).2 < (unitAct D u v (seeds.getD 0 (0, 0))).2)

open PellExact in
/-- **The merged sequence is strictly increasing.** -/
theorem interleave_strictMono {D u v Δ : ℤ} (hD : 0 < D) (hu : u ^ 2 - D * v ^ 2 = 1)
    (hu1 : 1 < u) (hv : 0 < v) {seeds : List (ℤ × ℤ)} (hsol : ∀ ρ ∈ seeds, Sol D Δ ρ)
    (hord : orderB D u v seeds = true) : StrictMono (interleave D u v seeds) := by
  simp only [orderB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hord
  obtain ⟨⟨hne, hsorted⟩, hwrap⟩ := hord
  set s := seeds.length with hs
  have hs0 : 0 < s := List.length_pos_of_ne_nil hne
  have hmem : ∀ i < s, seeds.getD i (0, 0) ∈ seeds := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hSol : ∀ i < s, Sol D Δ (seeds.getD i (0, 0)) := fun i hi => hsol _ (hmem i hi)
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [interleave, ← hs]
  have hi := Nat.mod_lt n hs0
  have hn := Nat.mod_add_div n s
  by_cases hlast : n % s + 1 < s
  · have hsplit : n + 1 = (n % s + 1) + s * (n / s) := by
      generalize s * (n / s) = w at hn ⊢; omega
    have e1 : (n + 1) % s = n % s + 1 := by
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlast]
    have e2 : (n + 1) / s = n / s := by
      rw [hsplit, Nat.add_mul_div_left _ _ hs0, Nat.div_eq_of_lt hlast, zero_add]
    rw [e1, e2]
    exact orbit_snd_lt hD hu hu1 hv (hSol _ hi) (hSol _ hlast) (hsorted _ (by omega)) _
  · have hlast' : n % s = s - 1 := by omega
    have hsplit : n + 1 = 0 + s * (n / s + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      generalize s * (n / s) = w at hn ⊢; omega
    have e1 : (n + 1) % s = 0 := by
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.zero_mod]
    have e2 : (n + 1) / s = n / s + 1 := by
      rw [hsplit, Nat.add_mul_div_left _ _ hs0, Nat.zero_div, zero_add]
    have hsl : ∀ p j, unitOrbit D u v p (j + 1) = unitOrbit D u v (unitAct D u v p) j :=
      fun p j => Function.iterate_succ_apply _ _ _
    rw [e1, e2, hlast', hsl]
    exact orbit_snd_lt hD hu hu1 hv (hSol _ (by omega))
      (unitAct_sol hD.le hu hu1.le hv.le (hSol 0 hs0)) hwrap _

open PellExact QuadOrbit in
/-- **The set is listed, in increasing order, by the merged orbits.** -/
theorem setsq_enum (D u v c : ℤ) (seeds : List (ℤ × ℤ)) (Ymax : ℕ) (hD : 0 < D) (hu1 : 1 < u)
    (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1) (hcert : seedCheck D u v c seeds Ymax = true)
    (hord : orderB D u v seeds = true) (hx0 : ∀ k : ℤ, D * k ^ 2 + c ≠ 0) :
    StrictMono (interleave D u v seeds) ∧
      ∀ k, (0 ≤ k ∧ ∃ x : ℤ, x ^ 2 = D * k ^ 2 + c) ↔ ∃ n, interleave D u v seeds n = k := by
  have hsol : ∀ ρ ∈ seeds, Sol D c ρ := fun ρ hρ => (seeds_roots hcert ρ hρ).1
  refine ⟨interleave_strictMono hD hu hu1 hv hsol hord, fun k => ?_⟩
  rw [setsq_iff D u v c seeds Ymax hD hu1 hv hu hcert hx0 k]
  have hs0 : 0 < seeds.length := by
    simp only [orderB, Bool.and_eq_true, decide_eq_true_eq] at hord
    exact List.length_pos_of_ne_nil hord.1.1
  constructor
  · rintro ⟨ρ, hρ, j, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hρ
    refine ⟨seeds.length * j + i, ?_⟩
    simp only [interleave]
    rw [show (seeds.length * j + i) % seeds.length = i by
          rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi],
        show (seeds.length * j + i) / seeds.length = j by
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ hs0, Nat.div_eq_of_lt hi, zero_add],
        List.getD_eq_getElem _ _ hi]
  · rintro ⟨n, rfl⟩
    refine ⟨_, ?_, n / seeds.length, rfl⟩
    rw [List.getD_eq_getElem _ _ (Nat.mod_lt n hs0)]
    exact List.getElem_mem _

/-- `a(n)`, `n ≥ off`, lists `S` in increasing order. -/
def Enumerates (a : ℕ → ℤ) (off : ℕ) (S : Set ℤ) : Prop :=
  StrictMono (fun n => a (n + off)) ∧ ∀ v, v ∈ S ↔ ∃ n, a (n + off) = v

/-- **An entry defined as the set `{k ≥ lo : D k^2 + c is a square}`, listed from offset `off`,
is the merged seed orbits**, from merged index `skip` on (the merged values below `lo`, e.g. a
seed with `k = 0` when the entry lists positive `k` only, are skipped). -/
theorem setsq_enumerates (D u v c : ℤ) (seeds : List (ℤ × ℤ)) (Ymax : ℕ) (hD : 0 < D)
    (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1)
    (hcert : QuadOrbit.seedCheck D u v c seeds Ymax = true) (hord : orderB D u v seeds = true)
    (hx0 : ∀ k : ℤ, D * k ^ 2 + c ≠ 0) (lo : ℤ) (hlo0 : 0 ≤ lo) (skip : ℕ)
    (hlo : lo ≤ interleave D u v seeds skip) (hbelow : ∀ n < skip, interleave D u v seeds n < lo)
    (off : ℕ) :
    Enumerates (fun n => interleave D u v seeds (n - off + skip)) off
      {k | lo ≤ k ∧ ∃ x : ℤ, x ^ 2 = D * k ^ 2 + c} := by
  obtain ⟨hm, h⟩ := setsq_enum D u v c seeds Ymax hD hu1 hv hu hcert hord hx0
  have e : ∀ n, n + off - off = n := fun n => Nat.add_sub_cancel n off
  refine ⟨by simp only [e]; exact fun a b hab => hm (by omega), fun k => ?_⟩
  simp only [e, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, hx⟩
    obtain ⟨n, rfl⟩ := (h k).mp ⟨by omega, hx⟩
    have hn : skip ≤ n := by
      by_contra hc; have := hbelow n (by omega); omega
    exact ⟨n - skip, by rw [Nat.sub_add_cancel hn]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨le_trans hlo (hm.monotone (by omega)), ((h _).mpr ⟨_, rfl⟩).2⟩

end PerfectPower.OEISLib
