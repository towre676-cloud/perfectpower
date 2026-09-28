import PerfectPower.PellGeneral

namespace PerfectPower.PellExact

open PerfectPower

/-! ### The exact Pell count, part 1: canonical orbit roots

Fix `D > 0`, a unit `(u, v)` with `u > 1`, `v > 0`, `u^2 - D v^2 = 1`, and `Δ`.  `Sol` is the set of
solutions of `X^2 - D Y^2 = Δ` in the quadrant `X > 0`, `Y ≥ 0`; `pred` is the inverse unit.  A
*root* is a solution whose predecessor leaves the quadrant.  We prove that every solution is
`unitOrbit ρ j` for exactly one root `ρ` and one `j`, and that the roots lie in the finite box
`D Y^2 ≤ |Δ| u^2`.  This canonicalisation removes duplicate orbit representatives, so each orbit
is counted once in the exact constant `κ`. -/

variable {D u v Δ : ℤ}

/-- Solutions in the quadrant `X > 0`, `Y ≥ 0`. -/
def Sol (D Δ : ℤ) (p : ℤ × ℤ) : Prop := 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 - D * p.2 ^ 2 = Δ

/-- The inverse unit. -/
def pred (D u v : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (p.1 * u - D * p.2 * v, u * p.2 - v * p.1)

/-- A root: a solution whose predecessor is not a solution. -/
def IsRoot (D u v Δ : ℤ) (p : ℤ × ℤ) : Prop := Sol D Δ p ∧ ¬ Sol D Δ (pred D u v p)

lemma pred_unitAct (hu : u ^ 2 - D * v ^ 2 = 1) (p : ℤ × ℤ) :
    pred D u v (unitAct D u v p) = p := by
  ext
  · simp only [pred, unitAct]; linear_combination p.1 * hu
  · simp only [pred, unitAct]; linear_combination p.2 * hu

lemma unitAct_pred (hu : u ^ 2 - D * v ^ 2 = 1) (p : ℤ × ℤ) :
    unitAct D u v (pred D u v p) = p := by
  simpa [pred] using unitAct_descend hu p.1 p.2

lemma unitAct_sol (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 ≤ u) (hv : 0 ≤ v)
    {p : ℤ × ℤ} (hp : Sol D Δ p) : Sol D Δ (unitAct D u v p) := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · simp only [unitAct]; nlinarith [mul_nonneg (mul_nonneg hD h2) hv]
  · simp only [unitAct]; nlinarith
  · rw [unitAct_norm hu, h3]

lemma unitAct_fst_gt (hD : 0 ≤ D) (hu1 : 1 < u) (hv : 0 ≤ v) {p : ℤ × ℤ} (hp : Sol D Δ p) :
    p.1 < (unitAct D u v p).1 := by
  obtain ⟨h1, h2, -⟩ := hp
  simp only [unitAct]
  nlinarith [mul_nonneg (mul_nonneg hD h2) hv]

lemma orbit_succ (p : ℤ × ℤ) (j : ℕ) :
    unitOrbit D u v p (j + 1) = unitAct D u v (unitOrbit D u v p j) := by
  rw [unitOrbit, Function.iterate_succ_apply', ← unitOrbit]

lemma orbit_sol (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 ≤ u) (hv : 0 ≤ v)
    {p : ℤ × ℤ} (hp : Sol D Δ p) : ∀ j, Sol D Δ (unitOrbit D u v p j)
  | 0 => hp
  | j + 1 => by rw [orbit_succ]; exact unitAct_sol hD hu hu1 hv (orbit_sol hD hu hu1 hv hp j)

/-- Outside the box, the predecessor of a solution is again a solution. -/
lemma pred_sol_of_outside (hD : 0 < D) (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1)
    {p : ℤ × ℤ} (hp : Sol D Δ p) (hbox : |Δ| * u ^ 2 < D * p.2 ^ 2) : Sol D Δ (pred D u v p) := by
  obtain ⟨hX0, hY0, hN⟩ := hp
  obtain ⟨X, Y⟩ := p
  simp only at hX0 hY0 hN hbox
  have habs : -|Δ| ≤ Δ ∧ Δ ≤ |Δ| := ⟨neg_abs_le Δ, le_abs_self Δ⟩
  have hDy : D * v ^ 2 < u ^ 2 := by linarith
  have hA0 : 0 ≤ |Δ| := abs_nonneg Δ
  have c2 : -Δ * u ^ 2 < D * Y ^ 2 := by nlinarith
  have c3 : v ^ 2 * Δ ≤ Y ^ 2 := by
    have h2 : |Δ| * v ^ 2 < Y ^ 2 := by
      by_contra h; push_neg at h
      have := mul_le_mul_of_nonneg_left h hD.le
      have h1 : |Δ| * (D * v ^ 2) ≤ |Δ| * u ^ 2 := mul_le_mul_of_nonneg_left hDy.le hA0
      nlinarith
    have h3 : v ^ 2 * Δ ≤ v ^ 2 * |Δ| := mul_le_mul_of_nonneg_left habs.2 (sq_nonneg _)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [pred]
    have h := lt_of_sq_lt_sq' (a := D * Y * v) (b := X * u) (by positivity) (by
      have e1 : (D * Y * v) ^ 2 = D * Y ^ 2 * (u ^ 2 - 1) := by linear_combination (-(D * Y ^ 2)) * hu
      have e2 : (X * u) ^ 2 = (Δ + D * Y ^ 2) * u ^ 2 := by rw [mul_pow, ← hN]; ring
      rw [e1, e2]; nlinarith)
    linarith
  · simp only [pred]
    have hle : v * X ≤ u * Y := by
      by_contra hlt; push_neg at hlt
      have h0 : 0 ≤ u * Y := by positivity
      have hsq : (u * Y) ^ 2 < (v * X) ^ 2 := by nlinarith
      have e2 : (v * X) ^ 2 = v ^ 2 * (Δ + D * Y ^ 2) := by rw [mul_pow, ← hN]; ring
      have e1 : (u * Y) ^ 2 = (1 + D * v ^ 2) * Y ^ 2 := by
        rw [mul_pow]; linear_combination Y ^ 2 * hu
      rw [e1, e2] at hsq
      nlinarith
    linarith
  · simp only [pred]; linear_combination (X ^ 2 - D * Y ^ 2) * hu + hN

/-- Roots lie in the box. -/
lemma root_in_box (hD : 0 < D) (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1)
    {p : ℤ × ℤ} (hp : IsRoot D u v Δ p) : D * p.2 ^ 2 ≤ |Δ| * u ^ 2 := by
  by_contra h; push_neg at h
  exact hp.2 (pred_sol_of_outside hD hu1 hv hu hp.1 h)

/-- The roots form a finite set. -/
lemma roots_finite (hD : 0 < D) (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1) :
    {p : ℤ × ℤ | IsRoot D u v Δ p}.Finite :=
  (pell_box_finite (x₁ := u) (Δ := Δ) hD).subset fun _ hp =>
    ⟨hp.1.1, hp.1.2.1, hp.1.2.2, root_in_box hD hu1 hv hu hp⟩

/-- **Every solution lies on the forward orbit of a root.** -/
theorem exists_root (hD : 0 < D) (hu1 : 1 < u) (hv : 0 < v) (hu : u ^ 2 - D * v ^ 2 = 1) :
    ∀ (X : ℤ) (p : ℤ × ℤ), p.1 = X → Sol D Δ p →
      ∃ ρ j, IsRoot D u v Δ ρ ∧ unitOrbit D u v ρ j = p := by
  intro X
  induction X using Int.strongRec (m := 1) with
  | lt X hX => intro p hpX hp; have := hp.1; omega
  | ge X _ ih =>
    intro p hpX hp
    by_cases hr : Sol D Δ (pred D u v p)
    · have hlt : (pred D u v p).1 < X := by
        have := unitAct_fst_gt hD.le hu1 hv.le hr
        rw [unitAct_pred hu] at this
        omega
      obtain ⟨ρ, j, hρ, hj⟩ := ih _ hlt (pred D u v p) rfl hr
      refine ⟨ρ, j + 1, hρ, ?_⟩
      rw [orbit_succ, hj, unitAct_pred hu]
    · exact ⟨p, 0, ⟨hp, hr⟩, rfl⟩

lemma pred_orbit_succ (hu : u ^ 2 - D * v ^ 2 = 1) (p : ℤ × ℤ) (j : ℕ) :
    pred D u v (unitOrbit D u v p (j + 1)) = unitOrbit D u v p j := by
  rw [orbit_succ, pred_unitAct hu]

/-- **The root and the index are unique.** -/
theorem root_unique (hD : 0 ≤ D) (hu1 : 1 < u) (hv : 0 ≤ v) (hu : u ^ 2 - D * v ^ 2 = 1) :
    ∀ (j₁ j₂ : ℕ) {ρ₁ ρ₂ : ℤ × ℤ}, IsRoot D u v Δ ρ₁ → IsRoot D u v Δ ρ₂ →
      unitOrbit D u v ρ₁ j₁ = unitOrbit D u v ρ₂ j₂ → ρ₁ = ρ₂ ∧ j₁ = j₂
  | 0, 0, _, _, _, _, h => ⟨h, rfl⟩
  | 0, j + 1, ρ₁, ρ₂, h₁, h₂, h => by
    exfalso
    have : pred D u v ρ₁ = unitOrbit D u v ρ₂ j := by
      simp only [unitOrbit, Function.iterate_zero, id] at h
      rw [show ρ₁ = unitOrbit D u v ρ₂ (j + 1) from h, pred_orbit_succ hu]
    exact h₁.2 (this ▸ orbit_sol hD hu hu1.le hv h₂.1 j)
  | j + 1, 0, ρ₁, ρ₂, h₁, h₂, h => by
    exfalso
    have : pred D u v ρ₂ = unitOrbit D u v ρ₁ j := by
      simp only [unitOrbit, Function.iterate_zero, id] at h
      rw [← show unitOrbit D u v ρ₁ (j + 1) = ρ₂ from h, pred_orbit_succ hu]
    exact h₂.2 (this ▸ orbit_sol hD hu hu1.le hv h₁.1 j)
  | j₁ + 1, j₂ + 1, ρ₁, ρ₂, h₁, h₂, h => by
    have h' := congrArg (pred D u v) h
    rw [pred_orbit_succ hu, pred_orbit_succ hu] at h'
    obtain ⟨e1, e2⟩ := root_unique hD hu1 hv hu j₁ j₂ h₁ h₂ h'
    exact ⟨e1, by omega⟩

/-! ### Part 2: growth at the rate of the real unit `ε = u + v √D` -/

section Growth

variable (D u v : ℤ)

/-- `ε = u + v √D`. -/
noncomputable def eps : ℝ := u + v * Real.sqrt D

/-- `ε' = u - v √D = ε⁻¹`. -/
noncomputable def eps' : ℝ := u - v * Real.sqrt D

/-- `η(p) = X + Y √D`. -/
noncomputable def eta (p : ℤ × ℤ) : ℝ := p.1 + p.2 * Real.sqrt D

/-- `η̄(p) = X - Y √D`. -/
noncomputable def etaBar (p : ℤ × ℤ) : ℝ := p.1 - p.2 * Real.sqrt D

variable {D u v}

lemma sqrt_sq_D (hD : 0 ≤ D) : Real.sqrt D ^ 2 = D := Real.sq_sqrt (by exact_mod_cast hD)

lemma eta_unitAct (hD : 0 ≤ D) (p : ℤ × ℤ) :
    eta D (unitAct D u v p) = eta D p * eps D u v := by
  simp only [eta, eps, unitAct]; push_cast
  have := sqrt_sq_D hD
  linear_combination (-(p.2 : ℝ) * v) * this

lemma etaBar_unitAct (hD : 0 ≤ D) (p : ℤ × ℤ) :
    etaBar D (unitAct D u v p) = etaBar D p * eps' D u v := by
  simp only [etaBar, eps', unitAct]; push_cast
  have := sqrt_sq_D hD
  linear_combination (-(p.2 : ℝ) * v) * this

lemma eta_orbit (hD : 0 ≤ D) (p : ℤ × ℤ) : ∀ j,
    eta D (unitOrbit D u v p j) = eta D p * eps D u v ^ j
  | 0 => by simp [unitOrbit]
  | j + 1 => by rw [orbit_succ, eta_unitAct hD, eta_orbit hD p j, pow_succ, mul_assoc]

lemma etaBar_orbit (hD : 0 ≤ D) (p : ℤ × ℤ) : ∀ j,
    etaBar D (unitOrbit D u v p j) = etaBar D p * eps' D u v ^ j
  | 0 => by simp [unitOrbit]
  | j + 1 => by rw [orbit_succ, etaBar_unitAct hD, etaBar_orbit hD p j, pow_succ, mul_assoc]

lemma fst_eq_half (p : ℤ × ℤ) : (p.1 : ℝ) = (eta D p + etaBar D p) / 2 := by
  simp only [eta, etaBar]; ring

lemma eps_mul_eps' (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) : eps D u v * eps' D u v = 1 := by
  simp only [eps, eps']
  have := sqrt_sq_D hD
  have hu' : (u : ℝ) ^ 2 - D * v ^ 2 = 1 := by exact_mod_cast hu
  linear_combination hu' - (v : ℝ) ^ 2 * this

lemma one_lt_eps (hu1 : 1 < u) (hv : 0 ≤ v) : 1 < eps D u v := by
  simp only [eps]
  have : (1 : ℝ) < u := by exact_mod_cast hu1
  have : (0 : ℝ) ≤ v * Real.sqrt D := mul_nonneg (by exact_mod_cast hv) (Real.sqrt_nonneg _)
  linarith

lemma eps'_pos (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v) :
    0 < eps' D u v ∧ eps' D u v < 1 := by
  have h1 := one_lt_eps (D := D) hu1 hv
  have h2 := eps_mul_eps' hD hu
  constructor
  · by_contra h; push_neg at h; nlinarith
  · by_contra h; push_neg at h; nlinarith

lemma eta_pos {p : ℤ × ℤ} (hp : Sol D Δ p) : 0 < eta D p := by
  simp only [eta]
  have h1 : (0 : ℝ) < p.1 := by exact_mod_cast hp.1
  have h2 : (0 : ℝ) ≤ p.2 := by exact_mod_cast hp.2.1
  positivity

/-- **Growth bracket.**  `|X_j - (η/2) ε^j| ≤ |η̄|/2` along every orbit. -/
theorem orbit_fst_bracket (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v)
    (p : ℤ × ℤ) (j : ℕ) :
    |((unitOrbit D u v p j).1 : ℝ) - eta D p / 2 * eps D u v ^ j| ≤ |etaBar D p| / 2 := by
  rw [fst_eq_half, eta_orbit hD, etaBar_orbit hD]
  obtain ⟨h0, h1⟩ := eps'_pos hD hu hu1 hv
  have hpow : eps' D u v ^ j ≤ 1 := pow_le_one₀ h0.le h1.le
  have hpow0 : 0 ≤ eps' D u v ^ j := pow_nonneg h0.le j
  have : (eta D p * eps D u v ^ j + etaBar D p * eps' D u v ^ j) / 2 - eta D p / 2 * eps D u v ^ j
      = etaBar D p * eps' D u v ^ j / 2 := by ring
  rw [this, abs_div, abs_mul, abs_of_nonneg hpow0, abs_two]
  have := abs_nonneg (etaBar D p)
  have : |etaBar D p| * eps' D u v ^ j ≤ |etaBar D p| := by nlinarith
  linarith

end Growth

/-! ### Part 3: counting a sequence within bounded distance of a geometric one -/

lemma exists_pos_lower (f : ℕ → ℝ) (hpos : ∀ h, 0 < f h) :
    ∀ n : ℕ, ∃ m : ℝ, 0 < m ∧ ∀ h < n, m ≤ f h
  | 0 => ⟨1, one_pos, fun h hh => absurd hh (Nat.not_lt_zero h)⟩
  | n + 1 => by
    obtain ⟨m, hm, hmn⟩ := exists_pos_lower f hpos n
    refine ⟨min m (f n), lt_min hm (hpos n), fun h hh => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with h1 | rfl
    · exact (min_le_left _ _).trans (hmn h h1)
    · exact min_le_right _ _

/-- A positive sequence within bounded distance of `a E^h` has a geometric lower bound. -/
lemma geometric_lower {f : ℕ → ℝ} {E a b : ℝ} (hE : 1 < E) (ha : 0 < a)
    (hf : ∀ h, |f h - a * E ^ h| ≤ b) (hpos : ∀ h, 0 < f h) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ h, c₁ * E ^ h ≤ f h := by
  obtain ⟨h₀, hh₀⟩ := pow_unbounded_of_one_lt (2 * b / a) hE
  obtain ⟨m, hm, hmf⟩ := exists_pos_lower f hpos h₀
  have hE0 : 0 < E := by linarith
  refine ⟨min (a / 2) (m / E ^ h₀), lt_min (by linarith) (div_pos hm (pow_pos hE0 _)), fun h => ?_⟩
  rcases Nat.lt_or_ge h h₀ with hlt | hge
  · have hpow : E ^ h ≤ E ^ h₀ := pow_le_pow_right₀ hE.le hlt.le
    calc min (a / 2) (m / E ^ h₀) * E ^ h ≤ m / E ^ h₀ * E ^ h :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hE0.le _)
      _ ≤ m / E ^ h₀ * E ^ h₀ := mul_le_mul_of_nonneg_left hpow (div_nonneg hm.le (pow_nonneg hE0.le _))
      _ = m := div_mul_cancel₀ m (pow_pos hE0 _).ne'
      _ ≤ f h := hmf h hlt
  · have hpow : E ^ h₀ ≤ E ^ h := pow_le_pow_right₀ hE.le hge
    have h2 : 2 * b ≤ a * E ^ h := by
      have := (div_lt_iff₀ ha).mp hh₀
      nlinarith
    have h3 := (abs_le.mp (hf h)).1
    calc min (a / 2) (m / E ^ h₀) * E ^ h ≤ a / 2 * E ^ h :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hE0.le _)
      _ ≤ f h := by linarith

/-- **Counting near a geometric sequence.**  If `|f h - a E^h| ≤ b` and `f > 0`, then the number
of `h` with `f h ≤ M` is `log M / log E + O(1)` for `M ≥ 1`. -/
theorem count_near_geometric {f : ℕ → ℝ} {E a b : ℝ} (hE : 1 < E) (ha : 0 < a) (hb : 0 ≤ b)
    (hf : ∀ h, |f h - a * E ^ h| ≤ b) (hpos : ∀ h, 0 < f h) :
    ∃ K : ℝ, ∀ (M : ℝ) (L : ℕ), 1 ≤ M → (∀ h, f h ≤ M → h < L) →
      |(((Finset.range L).filter (fun h => f h ≤ M)).card : ℝ) - Real.log M / Real.log E| ≤ K := by
  obtain ⟨c₁, hc₁, hlow⟩ := geometric_lower hE ha hf hpos
  have hlogE : 0 < Real.log E := Real.log_pos hE
  set c₂ := a + b
  have hc₂ : 0 < c₂ := by positivity
  have hup : ∀ h, f h ≤ c₂ * E ^ h := by
    intro h
    have h1 := (abs_le.mp (hf h)).2
    have hEh : 1 ≤ E ^ h := one_le_pow₀ hE.le
    have e : c₂ * E ^ h = a * E ^ h + b * E ^ h := by simp only [c₂]; ring
    have : b ≤ b * E ^ h := le_mul_of_one_le_right hb hEh
    linarith
  refine ⟨|Real.log c₁| / Real.log E + 1 + |Real.log c₂| / Real.log E, fun M L hM hL => ?_⟩
  have hM0 : 0 < M := by linarith
  set cnt := (((Finset.range L).filter (fun h => f h ≤ M)).card : ℝ)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hq0 : 0 ≤ Real.log M / Real.log E := div_nonneg hlogM hlogE.le
  -- upper bound
  have hupper : cnt ≤ Real.log M / Real.log E + |Real.log c₁| / Real.log E + 1 := by
    rcases le_or_lt c₁ M with h1 | h1
    · have := geometric_count_le hE hc₁ h1 hlow L
      rw [Real.log_div hM0.ne' hc₁.ne', sub_div] at this
      have : -(Real.log c₁ / Real.log E) ≤ |Real.log c₁| / Real.log E := by
        rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_le_abs _) hlogE.le
      linarith
    · have hzero : (Finset.range L).filter (fun h => f h ≤ M) = ∅ := by
        apply Finset.filter_false_of_mem
        intro h _ hh
        have := hlow h
        have : c₁ ≤ c₁ * E ^ h := le_mul_of_one_le_right hc₁.le (one_le_pow₀ hE.le)
        linarith
      have : cnt = 0 := by simp only [cnt, hzero, Finset.card_empty, Nat.cast_zero]
      have := div_nonneg (abs_nonneg (Real.log c₁)) hlogE.le
      linarith
  -- lower bound
  have hlower : Real.log M / Real.log E - |Real.log c₂| / Real.log E ≤ cnt := by
    have hLb : Real.log (M / c₂) / Real.log E < L := by
      set q := Real.log (M / c₂) / Real.log E
      rcases lt_or_le q 0 with hq | hq
      · exact hq.trans_le (Nat.cast_nonneg _)
      · have hfl := Nat.floor_le hq
        have hmem := le_of_index_le_geometric hE hc₂ hM0 hup hfl
        have := hL _ hmem
        have : (⌊q⌋₊ : ℝ) + 1 ≤ L := by exact_mod_cast this
        linarith [Nat.lt_floor_add_one q]
    have := le_geometric_count hE hc₂ hM0 hup L hLb
    rw [Real.log_div hM0.ne' hc₂.ne', sub_div] at this
    have : Real.log c₂ / Real.log E ≤ |Real.log c₂| / Real.log E :=
      div_le_div_of_nonneg_right (le_abs_self _) hlogE.le
    linarith
  rw [abs_le]
  constructor <;> linarith [div_nonneg (abs_nonneg (Real.log c₁)) hlogE.le,
    div_nonneg (abs_nonneg (Real.log c₂)) hlogE.le]

/-! ### Part 4: one residue class of one orbit -/

/-- **One class.**  For a solution `ρ`, a period `P > 0` and a residue `r`, the number of `h` with
`X_{r + P h}(ρ) ≤ M` is `log M / (P log ε) + O(1)`. -/
theorem class_count (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v)
    {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) {P : ℕ} (hP : 0 < P) (r : ℕ) :
    ∃ K : ℝ, ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ h, ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M → h < L) →
      |((((Finset.range L).filter
          (fun h => ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M)).card : ℕ) : ℝ) -
        Real.log M / (P * Real.log (eps D u v))| ≤ K := by
  have hε := one_lt_eps (D := D) hu1 hv
  have hE : 1 < eps D u v ^ P := one_lt_pow₀ hε hP.ne'
  have ha : 0 < eta D ρ / 2 * eps D u v ^ r := by
    have := eta_pos hρ; positivity
  obtain ⟨K, hK⟩ := count_near_geometric (f := fun h => ((unitOrbit D u v ρ (r + P * h)).1 : ℝ))
    hE ha (by positivity : (0 : ℝ) ≤ |etaBar D ρ| / 2)
    (fun h => by
      have := orbit_fst_bracket hD hu hu1 hv ρ (r + P * h)
      rwa [pow_add, pow_mul, ← mul_assoc] at this)
    (fun h => Int.cast_pos.mpr (orbit_sol hD hu hu1.le hv hρ (r + P * h)).1)
  refine ⟨K, fun M L hM hL => ?_⟩
  have := hK M L hM hL
  rwa [Real.log_pow] at this


/-! ### Part 5: the good indices of one orbit -/

open Finset in
/-- Splitting a finite set of indices by residue modulo `P`. -/
lemma card_split_residue (P L : ℕ) (hP : 0 < P) (good : ℕ → Prop) [DecidablePred good]
    (hgood : ∀ j, good (j + P) ↔ good j) (small : ℕ → Prop) [DecidablePred small]
    (hL : ∀ j, small j → j < L) :
    #{j ∈ range L | good j ∧ small j} =
      ∑ r ∈ (range P).filter good, #{h ∈ range L | small (r + P * h)} := by
  have hmod : ∀ j, good j ↔ good (j % P) := by
    intro j
    conv_lhs => rw [← Nat.mod_add_div j P]
    generalize j / P = k
    induction k with
    | zero => simp
    | succ k ih => rw [show j % P + P * (k + 1) = j % P + P * k + P by ring, hgood, ih]
  rw [card_eq_sum_card_fiberwise (f := fun j => j % P) (t := range P)
    (fun j _ => mem_range.mpr (Nat.mod_lt j hP)), sum_filter]
  refine sum_congr rfl fun r hr => ?_
  have hrP : r < P := mem_range.mp hr
  split_ifs with hg
  · refine card_nbij' (fun j => j / P) (fun h => r + P * h) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [mem_filter, mem_range] at hj ⊢
      obtain ⟨⟨hjL, -, hs⟩, hjr⟩ := hj
      have e : r + P * (j / P) = j := by rw [← hjr]; exact Nat.mod_add_div j P
      refine ⟨lt_of_le_of_lt (Nat.div_le_self j P) hjL, ?_⟩
      rw [e]; exact hs
    · intro h hh
      simp only [mem_filter, mem_range] at hh ⊢
      obtain ⟨-, hs⟩ := hh
      refine ⟨⟨hL _ hs, ?_, hs⟩, ?_⟩
      · rw [hmod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrP]; exact hg
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrP]
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      rw [← hj.2]; exact Nat.mod_add_div j P
    · intro h _
      simp only
      rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hrP, zero_add]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro j hj hjr
    simp only [mem_filter] at hj
    exact hg (hjr ▸ (hmod j).mp hj.2.1)

open Finset in
/-- **One orbit.**  With `g` good residues among `P` (a period of `X mod 2A`), the number of good
indices `j` with `X_j ≤ M` is `g log M / (P log ε) + O(1)`. -/
theorem orbit_count (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u) (hv : 0 ≤ v)
    {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) (m B : ℤ) {P : ℕ} (hP : 0 < P)
    (hper : ∀ j, m ∣ (unitOrbit D u v ρ (j + P)).1 - (unitOrbit D u v ρ j).1) :
    ∃ K : ℝ, ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ j, ((unitOrbit D u v ρ j).1 : ℝ) ≤ M → j < L) →
      |((#{j ∈ range L | m ∣ (unitOrbit D u v ρ j).1 - B ∧
            ((unitOrbit D u v ρ j).1 : ℝ) ≤ M} : ℕ) : ℝ) -
        (#((range P).filter fun r => m ∣ (unitOrbit D u v ρ r).1 - B) : ℕ) *
          (Real.log M / (P * Real.log (eps D u v)))| ≤ K := by
  classical
  have hK : ∀ r, ∃ K : ℝ, ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ h, ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M → h < L) →
      |((((range L).filter
          (fun h => ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M)).card : ℕ) : ℝ) -
        Real.log M / (P * Real.log (eps D u v))| ≤ K :=
    fun r => class_count hD hu hu1 hv hρ hP r
  choose Kf hKf using hK
  set G := (range P).filter fun r => m ∣ (unitOrbit D u v ρ r).1 - B
  refine ⟨∑ r ∈ G, Kf r, fun M L hM hL => ?_⟩
  have hgood : ∀ j, m ∣ (unitOrbit D u v ρ (j + P)).1 - B ↔ m ∣ (unitOrbit D u v ρ j).1 - B := by
    intro j
    have := hper j
    constructor
    · intro h; have := dvd_sub h this; simpa using this
    · intro h; have := dvd_add h this; simpa using this
  rw [card_split_residue P L hP _ hgood (fun j => ((unitOrbit D u v ρ j).1 : ℝ) ≤ M) hL]
  push_cast
  have hG : ((#G : ℕ) : ℝ) * (Real.log M / (P * Real.log (eps D u v))) =
      ∑ r ∈ G, Real.log M / (P * Real.log (eps D u v)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hG, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have hLr : ∀ h, ((unitOrbit D u v ρ (r + P * h)).1 : ℝ) ≤ M → h < L := by
    intro h hh
    have := hL _ hh
    have : h ≤ r + P * h := by nlinarith
    omega
  have := hKf r M L hM hLr
  simpa using this


/-! ### Part 6: assembly -/

lemma sol_eq_of_fst (hD : 0 < D) {p q : ℤ × ℤ} (hp : Sol D Δ p) (hq : Sol D Δ q) (h : p.1 = q.1) :
    p = q := by
  have h2 : D * p.2 ^ 2 = D * q.2 ^ 2 := by have := hp.2.2; have := hq.2.2; rw [h] at *; linarith
  have h3 : p.2 ^ 2 = q.2 ^ 2 := mul_left_cancel₀ hD.ne' h2
  have h4 : p.2 = q.2 := (sq_eq_sq₀ hp.2.1 hq.2.1).mp h3
  exact Prod.ext h h4

/-- Index bound: `j < X_j` along the orbit of a solution. -/
lemma index_lt_fst (hD : 0 ≤ D) (hu1 : 1 < u) (hv : 0 ≤ v) {ρ : ℤ × ℤ} (hρ : Sol D Δ ρ) (j : ℕ) :
    (j : ℤ) < (unitOrbit D u v ρ j).1 := by
  have hg := (unitOrbit_growth hD hu1.le hv hρ.1 hρ.2.1 j).1
  have hb : (1 : ℤ) + j * (u - 1) ≤ (1 + (u - 1)) ^ j :=
    one_add_mul_le_pow (by linarith) j
  simp only [add_sub_cancel] at hb
  have : (j : ℤ) ≤ j * (u - 1) := le_mul_of_one_le_right (by positivity) (by linarith)
  have hρ1 : (1 : ℤ) ≤ ρ.1 := hρ.1
  nlinarith [pow_pos (show (0 : ℤ) < u by linarith) j]

open Finset in
/-- Counting a filtered product by its first coordinate. -/
lemma card_filter_prod {α : Type*} [DecidableEq α] (R : Finset α) (L : ℕ) (q : α → ℕ → Prop)
    [∀ a, DecidablePred (q a)] :
    #((R ×ˢ range L).filter fun x => q x.1 x.2) = ∑ ρ ∈ R, #((range L).filter (q ρ)) := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := R) (fun x hx => (mem_product.mp (mem_filter.mp hx).1).1)]
  refine sum_congr rfl fun ρ _ => ?_
  refine card_nbij' Prod.snd (fun j => (ρ, j)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_product, mem_range] at hx ⊢
    obtain ⟨⟨⟨-, h1⟩, h2⟩, rfl⟩ := hx
    exact ⟨h1, h2⟩
  · intro j hj
    simp only [mem_filter, mem_product, mem_range] at hj ⊢
    tauto
  · intro x hx
    simp only [mem_filter] at hx
    exact Prod.ext hx.2.symm rfl
  · intro j _; rfl

set_option maxHeartbeats 2000000 in
open scoped Classical in
open Finset in
/-- **Exact Pell count.**  Let `A > 0`, `(u, v)` with `u > 1`, `v > 0`, `u^2 - 4A v^2 = 1`, and
`ε = u + v √(4A)`.  Let `R` be the finite set of canonical orbit roots of
`X^2 - 4A Y^2 = B^2 - 4AC`, `P ρ` a period of `X mod 2A` along the orbit of `ρ`, and `g ρ` the
number of residues `r < P ρ` with `X_r ≡ B (mod 2A)`.  Then the number `A(N)` of `n ∈ [1, N]` with
`A n^2 + B n + C` a square satisfies `|A(N) - κ log N| ≤ K` for `N ≥ N₀`, with
`κ = (∑_ρ g ρ / P ρ) / log ε`. -/
theorem pell_exact_count {A B C u v : ℤ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) :
    ∃ (R : Finset (ℤ × ℤ)) (P g : ℤ × ℤ → ℕ),
      (∀ ρ, ρ ∈ R ↔ IsRoot (4 * A) u v (B ^ 2 - 4 * A * C) ρ) ∧
      (∀ ρ ∈ R, 0 < P ρ ∧ ∀ j, 2 * A ∣
        (unitOrbit (4 * A) u v ρ (j + P ρ)).1 - (unitOrbit (4 * A) u v ρ j).1) ∧
      (∀ ρ, g ρ = #((range (P ρ)).filter fun r => 2 * A ∣ (unitOrbit (4 * A) u v ρ r).1 - B)) ∧
      ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        |((#((Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)) : ℕ) : ℝ) -
          (∑ ρ ∈ R, (g ρ : ℝ) / P ρ) / Real.log (eps (4 * A) u v) * Real.log N| ≤ K := by
  set D := 4 * A
  set Δ := B ^ 2 - 4 * A * C
  have hD : 0 < D := by positivity
  have hu' : u ^ 2 - D * v ^ 2 = 1 := hu
  -- roots
  have hfin := roots_finite (Δ := Δ) hD hu1 hv hu'
  set R := hfin.toFinset
  -- periods
  have hper : ∀ ρ : ℤ × ℤ, ∃ P, 0 < P ∧ ∀ j, 2 * A ∣
      (unitOrbit D u v ρ (j + P)).1 - (unitOrbit D u v ρ j).1 := by
    intro ρ
    haveI : NeZero (2 * A).toNat := ⟨by omega⟩
    obtain ⟨P, hP, hPj⟩ := unitOrbit_periodic (2 * A).toNat hu' ρ
    refine ⟨P, hP, fun j => ?_⟩
    have := (hPj j).1
    rwa [Int.toNat_of_nonneg (by omega)] at this
  choose P hP0 hPper using hper
  set g : ℤ × ℤ → ℕ := fun ρ =>
    #((range (P ρ)).filter fun r => 2 * A ∣ (unitOrbit D u v ρ r).1 - B)
  refine ⟨R, P, g, fun ρ => hfin.mem_toFinset, fun ρ _ => ⟨hP0 ρ, hPper ρ⟩, fun ρ => rfl, ?_⟩
  -- per-root constants
  have hroot : ∀ ρ ∈ R, Sol D Δ ρ := fun ρ hρ => (hfin.mem_toFinset.mp hρ).1
  have hK : ∀ ρ, ∃ K : ℝ, Sol D Δ ρ → ∀ (M : ℝ) (L : ℕ), 1 ≤ M →
      (∀ j, ((unitOrbit D u v ρ j).1 : ℝ) ≤ M → j < L) →
      |((#{j ∈ range L | 2 * A ∣ (unitOrbit D u v ρ j).1 - B ∧
            ((unitOrbit D u v ρ j).1 : ℝ) ≤ M} : ℕ) : ℝ) -
        (g ρ : ℝ) * (Real.log M / (P ρ * Real.log (eps D u v)))| ≤ K := by
    intro ρ
    by_cases hρ : Sol D Δ ρ
    · obtain ⟨K, hK⟩ := orbit_count hD.le hu' hu1 hv.le hρ (2 * A) B (hP0 ρ) (hPper ρ)
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hρ⟩
  choose Kf hKf using hK
  have hε := one_lt_eps (D := D) hu1 hv.le
  have hlogε : 0 < Real.log (eps D u v) := Real.log_pos hε
  set κ := (∑ ρ ∈ R, (g ρ : ℝ) / P ρ) / Real.log (eps D u v)
  have hκ : 0 ≤ κ := div_nonneg (sum_nonneg fun ρ _ => by positivity) hlogε.le
  refine ⟨|B| + 1 + ∑ ρ ∈ R, Kf ρ + κ * Real.log (2 * A + |B|), B.natAbs + 1, fun N hN => ?_⟩
  -- the parameter range
  set M : ℝ := 2 * A * N + B
  set L : ℕ := (2 * A * N + |B|).toNat + 1
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hBN : (|B| : ℝ) + 1 ≤ N := by
    have : ((B.natAbs : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hN
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hBr : -(|B| : ℝ) ≤ B := by exact_mod_cast neg_abs_le B
  have hBr' : (B : ℝ) ≤ |B| := by exact_mod_cast le_abs_self B
  have hMN : (N : ℝ) ≤ M := by simp only [M]; nlinarith
  have hM1 : (1 : ℝ) ≤ M := hNpos.trans hMN
  have hMup : M ≤ (2 * A + |B|) * N := by
    have : ((|B| : ℤ) : ℝ) ≤ ((|B| : ℤ) : ℝ) * N :=
      le_mul_of_one_le_right (by exact_mod_cast abs_nonneg B) hNpos
    simp only [M]; push_cast at this ⊢; nlinarith [le_abs_self (B : ℝ)]
  have hjL : ∀ ρ, Sol D Δ ρ → ∀ j, ((unitOrbit D u v ρ j).1 : ℝ) ≤ M → j < L := by
    intro ρ hρ j hj
    have h1 := index_lt_fst hD.le hu1 hv.le hρ j
    have h2 : (unitOrbit D u v ρ j).1 ≤ 2 * A * N + |B| := by
      have : ((unitOrbit D u v ρ j).1 : ℝ) ≤ 2 * A * N + |B| := by simp only [M] at hj; linarith
      exact_mod_cast this
    have : (j : ℤ) < ((2 * A * N + |B|).toNat : ℤ) + 1 := by
      rw [Int.toNat_of_nonneg (by positivity)]; linarith
    omega
  -- the index set T and its count
  set T := (R ×ˢ range L).filter fun x => 2 * A ∣ (unitOrbit D u v x.1 x.2).1 - B ∧
      ((unitOrbit D u v x.1 x.2).1 : ℝ) ≤ M
  have hTcard : #T = ∑ ρ ∈ R, #{j ∈ range L | 2 * A ∣ (unitOrbit D u v ρ j).1 - B ∧
      ((unitOrbit D u v ρ j).1 : ℝ) ≤ M} :=
    card_filter_prod R L (fun ρ j => 2 * A ∣ (unitOrbit D u v ρ j).1 - B ∧
      ((unitOrbit D u v ρ j).1 : ℝ) ≤ M)
  set hits := (Icc 1 N).filter fun n : ℕ => IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)
  set ψ : (ℤ × ℤ) × ℕ → ℕ := fun x => (((unitOrbit D u v x.1 x.2).1 - B) / (2 * A)).toNat
  -- (A1) hits ≤ #T + |B|
  have hA1 : (#hits : ℤ) ≤ #T + B.natAbs := by
    have hsmall : (hits.filter fun n : ℕ => 2 * A * n + B ≤ 0) ⊆ Icc 1 B.natAbs := by
      intro n hn
      simp only [hits, mem_filter, mem_Icc] at hn ⊢
      refine ⟨hn.1.1.1, ?_⟩
      have : (n : ℤ) ≤ |B| := by nlinarith [neg_abs_le B, (by exact_mod_cast hn.1.1.1 : (1 : ℤ) ≤ n)]
      have hB : (|B| : ℤ) = (B.natAbs : ℤ) := Int.abs_eq_natAbs B
      omega
    have hbig : (hits.filter fun n : ℕ => ¬ 2 * A * n + B ≤ 0) ⊆ T.image ψ := by
      intro n hn
      simp only [hits, mem_filter, mem_Icc, not_le] at hn
      obtain ⟨⟨⟨hn1, hnN⟩, hhit⟩, hX⟩ := hn
      obtain ⟨Y, hY⟩ := (quadratic_isHit_iff_norm hA.ne' B C n).mp hhit
      have hs : Sol D Δ (2 * A * n + B, |Y|) := ⟨hX, abs_nonneg Y, by simp only [sq_abs]; exact hY⟩
      obtain ⟨ρ, j, hρ, hj⟩ := exists_root hD hu1 hv hu' _ _ rfl hs
      have hρR : ρ ∈ R := hfin.mem_toFinset.mpr hρ
      have hXM : ((unitOrbit D u v ρ j).1 : ℝ) ≤ M := by
        rw [hj]; simp only [M]; push_cast
        have : (n : ℝ) ≤ N := by exact_mod_cast hnN
        nlinarith
      refine mem_image.mpr ⟨(ρ, j), mem_filter.mpr ⟨mem_product.mpr ⟨hρR,
        mem_range.mpr (hjL ρ hρ.1 j hXM)⟩, ?_, hXM⟩, ?_⟩
      · rw [hj]; exact ⟨n, by ring⟩
      · simp only [ψ, hj]
        rw [show 2 * A * (n : ℤ) + B - B = 2 * A * n by ring,
          Int.mul_ediv_cancel_left _ (by positivity)]
        simp
    have hsplit := filter_card_add_filter_neg_card_eq_card (s := hits)
      (fun n : ℕ => 2 * A * n + B ≤ 0)
    have c1 := card_le_card hsmall
    have c2 := (card_le_card hbig).trans card_image_le
    simp only [Nat.card_Icc, add_tsub_cancel_right] at c1
    omega
  -- (A2) #T ≤ hits + |B|
  have hA2 : (#T : ℤ) ≤ #hits + B.natAbs := by
    have hTsol : ∀ x ∈ T, Sol D Δ (unitOrbit D u v x.1 x.2) := by
      intro x hx
      have := (mem_product.mp (mem_filter.mp hx).1).1
      exact orbit_sol hD.le hu' hu1.le hv.le (hroot _ this) x.2
    have hinj : ∀ x ∈ T, ∀ y ∈ T, (unitOrbit D u v x.1 x.2).1 = (unitOrbit D u v y.1 y.2).1 → x = y := by
      intro x hx y hy hxy
      have e := sol_eq_of_fst hD (hTsol x hx) (hTsol y hy) hxy
      have hx' := hfin.mem_toFinset.mp (mem_product.mp (mem_filter.mp hx).1).1
      have hy' := hfin.mem_toFinset.mp (mem_product.mp (mem_filter.mp hy).1).1
      obtain ⟨e1, e2⟩ := root_unique hD.le hu1 hv.le hu' x.2 y.2 hx' hy' e
      exact Prod.ext e1 e2
    have h1 : (T.filter fun x => B < (unitOrbit D u v x.1 x.2).1).card ≤ #hits := by
      refine card_le_card_of_injOn ψ ?_ ?_
      · intro x hx
        rw [mem_filter] at hx
        obtain ⟨hxT, hxB⟩ := hx
        obtain ⟨-, ⟨k, hk⟩, hxM⟩ := mem_filter.mp hxT
        have hk1 : 1 ≤ k := by nlinarith
        simp only [hits, mem_filter, mem_Icc, ψ]
        rw [hk, Int.mul_ediv_cancel_left _ (by positivity)]
        have hkN : k ≤ N := by
          have : ((2 * A * k + B : ℤ) : ℝ) ≤ M := by rw [← hk]; push_cast; linarith
          simp only [M] at this; push_cast at this
          have : (k : ℝ) ≤ N := by nlinarith
          exact_mod_cast this
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [Int.toNat_of_nonneg (by omega)]
        refine (quadratic_isHit_iff_norm hA.ne' B C k).mpr ⟨(unitOrbit D u v x.1 x.2).2, ?_⟩
        rw [show 2 * A * k + B = (unitOrbit D u v x.1 x.2).1 by linarith]
        exact (hTsol x hxT).2.2
      · intro x hx y hy hxy
        rw [mem_coe, mem_filter] at hx hy
        obtain ⟨hxT, hxB⟩ := hx
        obtain ⟨hyT, hyB⟩ := hy
        obtain ⟨-, ⟨k, hk⟩, -⟩ := mem_filter.mp hxT
        obtain ⟨-, ⟨l, hl⟩, -⟩ := mem_filter.mp hyT
        simp only [ψ] at hxy
        rw [hk, hl, Int.mul_ediv_cancel_left _ (by positivity),
          Int.mul_ediv_cancel_left _ (by positivity)] at hxy
        have hk0 : 0 ≤ k := by nlinarith
        have hl0 : 0 ≤ l := by nlinarith
        have : k = l := by omega
        exact hinj x hxT y hyT (by rw [this] at hk; linarith)
    have h2 : (T.filter fun x => ¬ B < (unitOrbit D u v x.1 x.2).1).card ≤ B.natAbs := by
      calc _ ≤ (Icc 1 B.natAbs).card := by
            refine card_le_card_of_injOn (fun x => ((unitOrbit D u v x.1 x.2).1).toNat) ?_ ?_
            · intro x hx
              rw [mem_filter, not_lt] at hx
              obtain ⟨hxT, hxB⟩ := hx
              have hpos := (hTsol x hxT).1
              dsimp only
              rw [mem_Icc]
              have h1 := le_abs_self B
              have hB : (|B| : ℤ) = (B.natAbs : ℤ) := Int.abs_eq_natAbs B
              constructor <;> omega
            · intro x hx y hy hxy
              rw [mem_coe, mem_filter] at hx hy
              have := (hTsol x hx.1).1
              have := (hTsol y hy.1).1
              exact hinj x hx.1 y hy.1 (by simp only at hxy; omega)
        _ = B.natAbs := by simp
    have hsplit := filter_card_add_filter_neg_card_eq_card (s := T)
      (fun x => B < (unitOrbit D u v x.1 x.2).1)
    omega
  -- (B) the per-root estimates
  have hB' : |(#T : ℝ) - κ * Real.log M| ≤ ∑ ρ ∈ R, Kf ρ := by
    rw [hTcard]; push_cast
    have e : κ * Real.log M = ∑ ρ ∈ R, (g ρ : ℝ) * (Real.log M / (P ρ * Real.log (eps D u v))) := by
      simp only [κ]; rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
      refine sum_congr rfl fun ρ hρ => ?_
      have : (0 : ℝ) < P ρ := by exact_mod_cast hP0 ρ
      field_simp
    rw [e, ← sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ρ hρ =>
      hKf ρ (hroot ρ hρ) M L hM1 (hjL ρ (hroot ρ hρ)))
  -- (C) log M versus log N
  have hlog1 : Real.log N ≤ Real.log M := Real.log_le_log (by linarith) hMN
  have hlog2 : Real.log M ≤ Real.log (2 * A + |B|) + Real.log N := by
    rw [← Real.log_mul (by positivity) (by linarith)]
    exact Real.log_le_log (by linarith) hMup
  have hB : ((B.natAbs : ℕ) : ℝ) = |(B : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hAB1 : ((#hits : ℕ) : ℝ) ≤ (#T : ℕ) + (B.natAbs : ℕ) := by exact_mod_cast hA1
  have hAB2 : ((#T : ℕ) : ℝ) ≤ (#hits : ℕ) + (B.natAbs : ℕ) := by exact_mod_cast hA2
  rw [hB] at hAB1 hAB2
  have hcast : ((|B| : ℤ) : ℝ) = |(B : ℝ)| := Int.cast_abs
  rw [abs_le] at hB' ⊢
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlog1 hκ, mul_le_mul_of_nonneg_left hlog2 hκ]

end PerfectPower.PellExact
