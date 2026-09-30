import PerfectPower.FilteredCount

/-!
# The quadratic-unit orbit engine

Fix `D > 0`, a unit `u + v √D` of norm `u^2 - D v^2 = 1` with `u > 1`, `v > 0`, and `Δ ≠ 0`.
The solutions of `X^2 - D Y^2 = Δ` with `X > 0`, `Y ≥ 0` fall into finitely many orbits under the
unit, one for each **root** (a solution whose predecessor leaves the quadrant; `PellExact`).
This file turns that into a reusable engine with a kernel-checkable completeness certificate.

* `seedCheck D u v Δ seeds Ymax`: one Boolean.  It checks that every listed seed is a root, and
  that every root is listed, by enumerating the box `D Y^2 ≤ |Δ| u^2` (which contains every root,
  `root_in_box`) with verified integer square roots.  General equations have **several** orbits;
  the seed list is a list from the start.
* `complete`: under the certificate, the solutions are exactly `unitOrbit ρ j`, `ρ ∈ seeds`.
* `unique`: the pair `(ρ, j)` is determined by the solution.
* `orbit_rec`: every coordinate of every orbit satisfies `a(j+2) = 2u a(j+1) - a(j)`.

**Collisions and inversion** (`fst_inj`, `snd_inj`, `cross_collision`).  On one equation each
coordinate determines the solution: `X` determines it, and so does `Y`.  So an observation made of
one coordinate of one equation loses nothing, and its values count its orbit indices.  Collisions
appear only between **different** equations sharing a coordinate: for `Δ` and `-Δ`,
`cross_collision` shows that equal `Y` forces `(X - X')(X + X') = 2Δ`, so the collisions are
finitely many and are listed by a finite search; the repairing coordinate is the sign of the norm.

The unit here is a unit of `ℤ[√D]` of norm `+1`.  When the ring of integers is larger
(`D ≡ 1 mod 4`, as for `√5`), or the fundamental unit has norm `-1`, its orbits are recovered as
several seeds of `ℤ[√D]` for `±Δ` (see `FibOrbit.lean`).
-/

namespace PerfectPower.QuadOrbit

open PerfectPower PellExact FilteredPell

/-- The seed certificate: the seeds are roots, and every root in the box is a seed. -/
def seedCheck (D u v Δ : ℤ) (seeds : List (ℤ × ℤ)) (Ymax : ℕ) : Bool :=
  decide (|Δ| * u ^ 2 < D * ((Ymax : ℤ) + 1) ^ 2) &&
  seeds.all (fun ρ => solB D Δ ρ && !solB D Δ (pred D u v ρ)) &&
  (List.range (Ymax + 1)).all (fun Y =>
    let t := Δ + D * (Y : ℤ) ^ 2
    let q := isqrtZ t
    decide (t ≤ 0) ||
      (decide (0 ≤ q ∧ q * q ≤ t ∧ t < (q + 1) * (q + 1)) &&
        (!decide (q * q = t) || !decide (0 < q) || solB D Δ (pred D u v (q, (Y : ℤ))) ||
          decide ((q, (Y : ℤ)) ∈ seeds))))

variable {D u v Δ : ℤ} {seeds : List (ℤ × ℤ)} {Ymax : ℕ}

lemma seeds_roots (hc : seedCheck D u v Δ seeds Ymax = true) : ∀ ρ ∈ seeds, IsRoot D u v Δ ρ := by
  simp only [seedCheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hc
  intro ρ hρ
  obtain ⟨h1, h2⟩ := hc.1.2 ρ hρ
  exact ⟨(solB_iff _).mp h1, fun h => by rw [(solB_iff _).mpr h] at h2; exact absurd h2 (by decide)⟩

lemma roots_seeds (hD : 0 < D) (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1)
    (hc : seedCheck D u v Δ seeds Ymax = true) (ρ : ℤ × ℤ) (hρ : IsRoot D u v Δ ρ) :
    ρ ∈ seeds := by
  simp only [seedCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
  obtain ⟨⟨hbox, -⟩, hlist⟩ := hc
  have hρbox := root_in_box hD hu1 hv hu hρ
  obtain ⟨hρX, hρY, hρN⟩ := hρ.1
  have hρY' : ρ.2 < (Ymax : ℤ) + 1 := by
    by_contra h'
    push_neg at h'
    have : D * ((Ymax : ℤ) + 1) ^ 2 ≤ D * ρ.2 ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact pow_le_pow_left₀ (by positivity) h' 2
    linarith
  have hYn : ρ.2.toNat < Ymax + 1 := by omega
  have hYc : ((ρ.2.toNat : ℕ) : ℤ) = ρ.2 := Int.toNat_of_nonneg hρY
  have ht : Δ + D * ((ρ.2.toNat : ℕ) : ℤ) ^ 2 = ρ.1 * ρ.1 := by rw [hYc]; linarith
  rcases hlist _ hYn with hneg | ⟨⟨hq0, hq1, hq2⟩, hsq⟩
  · rw [ht] at hneg; nlinarith
  rw [ht] at hq0 hq1 hq2 hsq
  generalize isqrtZ (ρ.1 * ρ.1) = q at hq0 hq1 hq2 hsq
  have hqX : q = ρ.1 := by
    have h1 : q ≤ ρ.1 := by nlinarith
    have h2 : ρ.1 < q + 1 := by nlinarith
    omega
  rw [hqX, hYc] at hsq
  rcases hsq with ((hnot | hnot) | hpred) | hmem
  · exact absurd rfl hnot
  · exact absurd hρX hnot
  · exact absurd ((solB_iff _).mp hpred) hρ.2
  · exact hmem

/-- **Completeness.**  Under the certificate, the solutions are exactly the orbit points. -/
theorem complete (hD : 0 < D) (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1)
    (hc : seedCheck D u v Δ seeds Ymax = true) (p : ℤ × ℤ) :
    Sol D Δ p ↔ ∃ ρ ∈ seeds, ∃ j, unitOrbit D u v ρ j = p := by
  constructor
  · intro hp
    obtain ⟨ρ, j, hρ, hj⟩ := exists_root hD hu1 hv hu p.1 p rfl hp
    exact ⟨ρ, roots_seeds hD hu1 hv hu hc ρ hρ, j, hj⟩
  · rintro ⟨ρ, hρ, j, rfl⟩
    exact orbit_sol hD.le hu hu1.le hv.le (seeds_roots hc ρ hρ).1 j

/-- **Uniqueness.**  A solution is on exactly one orbit, at exactly one index. -/
theorem unique (hu1 : 1 < u) (hv : 0 ≤ v) (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1)
    (hc : seedCheck D u v Δ seeds Ymax = true) {ρ₁ ρ₂ : ℤ × ℤ} (h₁ : ρ₁ ∈ seeds) (h₂ : ρ₂ ∈ seeds)
    {j₁ j₂ : ℕ} (h : unitOrbit D u v ρ₁ j₁ = unitOrbit D u v ρ₂ j₂) : ρ₁ = ρ₂ ∧ j₁ = j₂ :=
  root_unique hD hu1 hv hu j₁ j₂ (seeds_roots hc ρ₁ h₁) (seeds_roots hc ρ₂ h₂) h

/-- **The orbit recurrence**, for both coordinates of every orbit. -/
theorem orbit_rec (hu : u ^ 2 - D * v ^ 2 = 1) (ρ : ℤ × ℤ) (j : ℕ) :
    (unitOrbit D u v ρ (j + 2)).1 = 2 * u * (unitOrbit D u v ρ (j + 1)).1 - (unitOrbit D u v ρ j).1 ∧
    (unitOrbit D u v ρ (j + 2)).2 = 2 * u * (unitOrbit D u v ρ (j + 1)).2 - (unitOrbit D u v ρ j).2 := by
  simp only [orbit_succ, unitAct]
  constructor
  · linear_combination (-(unitOrbit D u v ρ j).1) * hu
  · linear_combination (-(unitOrbit D u v ρ j).2) * hu

/-! ### Collisions and inversion -/

/-- On one equation, `X` determines the solution. -/
theorem fst_inj (hD : 0 < D) {p q : ℤ × ℤ} (hp : Sol D Δ p) (hq : Sol D Δ q) (h : p.1 = q.1) :
    p = q := sol_eq_of_fst hD hp hq h

/-- On one equation, `Y` determines the solution. -/
theorem snd_inj {p q : ℤ × ℤ} (hp : Sol D Δ p) (hq : Sol D Δ q) (h : p.2 = q.2) : p = q := by
  obtain ⟨hp1, -, hp3⟩ := hp
  obtain ⟨hq1, -, hq3⟩ := hq
  have : p.1 ^ 2 = q.1 ^ 2 := by rw [h] at hp3; linarith
  exact Prod.ext ((sq_eq_sq₀ hp1.le hq1.le).mp this) h

/-- **Collisions between `Δ` and `-Δ`.**  Equal `Y` forces `(X - X')(X + X') = 2Δ`, so
`X + X' ≤ 2|Δ|`: the collisions are finitely many. -/
theorem cross_collision (hΔ : Δ ≠ 0) {p q : ℤ × ℤ} (hp : Sol D Δ p) (hq : Sol D (-Δ) q) (h : p.2 = q.2) :
    (p.1 - q.1) * (p.1 + q.1) = 2 * Δ ∧ p.1 + q.1 ≤ 2 * |Δ| := by
  obtain ⟨hp1, -, hp3⟩ := hp
  obtain ⟨hq1, -, hq3⟩ := hq
  have e : (p.1 - q.1) * (p.1 + q.1) = 2 * Δ := by rw [h] at hp3; linear_combination hp3 - hq3
  refine ⟨e, ?_⟩
  have hs : 0 < p.1 + q.1 := by omega
  have hd : p.1 - q.1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e
    exact hΔ (by linarith)
  have h1 : 1 ≤ |p.1 - q.1| := Int.one_le_abs hd
  have : |p.1 - q.1| * (p.1 + q.1) = 2 * |Δ| := by
    rw [← abs_of_pos hs, ← abs_mul, e, abs_mul]; norm_num
  nlinarith

/-! ### Growth of both coordinates -/

/-- `X_j` lies between two multiples of `ε^j`. -/
theorem fst_between (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v)
    {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ j, c₁ * eps D u v ^ j ≤ (unitOrbit D u v ρ j).1 ∧
      ((unitOrbit D u v ρ j).1 : ℝ) ≤ c₂ * eps D u v ^ j := by
  have hb := orbit_fst_bracket hD hu hu1 hv ρ
  have hη := eta_pos hρ
  obtain ⟨c₁, hc₁, hlow⟩ := geometric_lower (one_lt_eps hu1 hv) (by positivity : 0 < eta D ρ / 2)
    hb (fun j => Int.cast_pos.mpr (orbit_sol hD hu hu1.le hv hρ j).1)
  refine ⟨c₁, eta D ρ / 2 + |etaBar D ρ| / 2, hc₁, by positivity, fun j => ⟨hlow j, ?_⟩⟩
  have h1 := (abs_le.mp (hb j)).2
  have hE : 1 ≤ eps D u v ^ j := one_le_pow₀ (one_lt_eps hu1 hv).le
  nlinarith [abs_nonneg (etaBar D ρ)]

/-- `Y_{j+1}` lies between two multiples of `ε^j`. -/
theorem snd_between (hD : 0 < D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 < v)
    {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ j, c₁ * eps D u v ^ j ≤ (unitOrbit D u v ρ (j + 1)).2 ∧
      ((unitOrbit D u v ρ (j + 1)).2 : ℝ) ≤ c₂ * eps D u v ^ j := by
  obtain ⟨a, b, ha, hb, h⟩ := fst_between hD.le hu hu1 hv.le hρ
  have hε := one_lt_eps (D := D) hu1 hv.le
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  refine ⟨v * a, b * eps D u v + |Δ| + 1, mul_pos hv' ha, by positivity, fun j => ⟨?_, ?_⟩⟩
  · have hs := orbit_sol hD.le hu hu1.le hv.le hρ j
    have e : (unitOrbit D u v ρ (j + 1)).2 =
        (unitOrbit D u v ρ j).1 * v + (unitOrbit D u v ρ j).2 * u := by
      rw [orbit_succ]; rfl
    have hY : (0 : ℝ) ≤ (unitOrbit D u v ρ j).2 := by exact_mod_cast hs.2.1
    have hu0 : (0 : ℝ) ≤ u := by exact_mod_cast (by omega : (0 : ℤ) ≤ u)
    rw [e]; push_cast
    have := (h j).1
    nlinarith [mul_nonneg hY hu0]
  · have hs := orbit_sol hD.le hu hu1.le hv.le hρ (j + 1)
    obtain ⟨hX, hY, hN⟩ := hs
    -- Y ≤ X + |Δ|, from Y^2 ≤ D Y^2 = X^2 - Δ ≤ (X + |Δ|)^2
    have hYX : (unitOrbit D u v ρ (j + 1)).2 ≤ (unitOrbit D u v ρ (j + 1)).1 + |Δ| := by
      have h1 : (unitOrbit D u v ρ (j + 1)).2 ^ 2 ≤ D * (unitOrbit D u v ρ (j + 1)).2 ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) (by omega)
      have h2 := neg_abs_le Δ
      have h3 := abs_nonneg Δ
      nlinarith
    have hYXr : ((unitOrbit D u v ρ (j + 1)).2 : ℝ) ≤ (unitOrbit D u v ρ (j + 1)).1 + |(Δ : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast hYX
    have hXb := (h (j + 1)).2
    rw [pow_succ] at hXb
    have hE : 1 ≤ eps D u v ^ j := one_le_pow₀ hε.le
    have : |(Δ : ℝ)| ≤ |(Δ : ℝ)| * eps D u v ^ j := le_mul_of_one_le_right (abs_nonneg _) hE
    push_cast
    nlinarith

/-! ### Recurrences -/

/-- Two sequences with the same order-two recurrence and the same initial values agree. -/
lemma rec_unique {f g : ℕ → ℤ} (c d e : ℤ) (hf : ∀ n, f (n + 2) = c * f (n + 1) + d * f n + e)
    (hg : ∀ n, g (n + 2) = c * g (n + 1) + d * g n + e) (h0 : f 0 = g 0) (h1 : f 1 = g 1) :
    ∀ n, f n = g n := by
  have key : ∀ n, f n = g n ∧ f (n + 1) = g (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih => exact ⟨ih.2, by rw [hf, hg, ih.1, ih.2]⟩
  exact fun n => (key n).1

/-! ### Residues along an orbit: the finite-state filter -/

/-- The residues of an orbit follow the reduced step map. -/
theorem orbit_mod (M : ℤ) (ρ : ℤ × ℤ) : ∀ j,
    ((unitOrbit D u v ρ j).1 % M, (unitOrbit D u v ρ j).2 % M) =
      (stepInt M D u v)^[j] (ρ.1 % M, ρ.2 % M)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', ← orbit_mod M ρ j, orbit_succ]
    simp only [unitAct, stepInt]
    have hX := Int.mod_modEq (unitOrbit D u v ρ j).1 M
    have hY := Int.mod_modEq (unitOrbit D u v ρ j).2 M
    ext
    · exact ((hX.mul_right u).add (((Int.ModEq.refl D).mul hY).mul_right v)).symm
    · exact ((hX.mul_right v).add (hY.mul_right u)).symm

/-- **The compiled filter.**  If the reduced state returns after `P` steps (checked), the
residues at index `j` are those at `j % P`, so any condition on residues holds on a union of
index classes mod `P`, which is read off the `P` states. -/
theorem residues_periodic (M : ℤ) (ρ : ℤ × ℤ) (P : ℕ)
    (hper : iterForce (stepInt M D u v) P (ρ.1 % M, ρ.2 % M) = (ρ.1 % M, ρ.2 % M)) (j : ℕ) :
    ((unitOrbit D u v ρ j).1 % M, (unitOrbit D u v ρ j).2 % M) =
      (stepInt M D u v)^[j % P] (ρ.1 % M, ρ.2 % M) := by
  rw [iterForce_eq] at hper
  rw [orbit_mod, (Function.IsPeriodicPt.iterate_mod_apply hper j)]

end PerfectPower.QuadOrbit
