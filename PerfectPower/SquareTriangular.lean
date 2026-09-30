import PerfectPower.Observation

/-!
# Six sequences, one orbit: square triangular numbers and `2n^2 + 1 = m^2`

Every positive solution of `X^2 - 8 Y^2 = 1` is `(X_j, Y_j) = (3 + √8)^j`, `j ≥ 0`
(`sol_iff`: the only orbit root is `(1, 0)`).  Six sequences, each defined here by its plain
arithmetic definition, are coordinates of that one orbit (index `j = h + 1`):

| set | definition | coordinate | growth | count of values `≤ N` |
|---|---|---|---|---|
| `PellIdx` | `n ≥ 1`, `2n^2 + 1` a square | `2 Y_j` | `ε^j` | `log N / log ε` |
| `PellRoot` | `m` with `m^2 = 2n^2 + 1`, `n ≥ 1` | `X_j` | `ε^j` | `log N / log ε` |
| `SqTriRoot` | `t ≥ 1`, `t^2` triangular | `Y_j` | `ε^j` | `log N / log ε` |
| `TriIdx` | `u ≥ 1`, `u(u+1)/2` a square | `(X_j - 1)/2` | `ε^j` | `log N / log ε` |
| `SqTri` | `v ≥ 1` both square and triangular | `Y_j^2` | `ε^{2j}` | `log N / (2 log ε)` |
| `OddSqTri` | odd square triangular numbers | `Y_j^2`, `j` odd | `ε^{2j}`, `g/P = 1/2` | `log N / (4 log ε)` |

with `ε = 3 + 2√2`.  The correspondences are proved (`*_iff`), and the counts follow from the
single theorem `Observation.observed_count`: the orbit is the same, the measured coordinate
changes the constant.  The substitution behind the table is `m = 2u + 1`, `n = 2t`: the Pell
equation forces `n` even (`even_of_pell`), which is why the correspondence is exact.
-/

namespace PerfectPower.SquareTriangular

open PerfectPower PellExact Finset Observation
open scoped Classical

/-- The orbit `X_j + Y_j √8 = (3 + √8)^j`. -/
def orb (j : ℕ) : ℤ × ℤ := unitOrbit 8 3 1 (1, 0) j

lemma unit_norm : (3 : ℤ) ^ 2 - 8 * 1 ^ 2 = 1 := by norm_num

lemma orb_succ (j : ℕ) :
    orb (j + 1) = (3 * (orb j).1 + 8 * (orb j).2, (orb j).1 + 3 * (orb j).2) := by
  rw [orb, orbit_succ, ← orb]
  simp only [unitAct]
  ext <;> ring

lemma orb_sol (j : ℕ) : Sol 8 1 (orb j) :=
  orbit_sol (by norm_num) unit_norm (by norm_num) (by norm_num)
    (show Sol 8 1 (1, 0) by refine ⟨by norm_num, le_refl _, by norm_num⟩) j

/-- **Every positive solution is on the orbit of `(1, 0)`.** -/
theorem sol_iff (p : ℤ × ℤ) : Sol 8 1 p ↔ ∃ j, orb j = p := by
  refine ⟨fun hp => ?_, fun ⟨j, hj⟩ => hj ▸ orb_sol j⟩
  obtain ⟨ρ, j, hρ, hj⟩ := exists_root (D := 8) (u := 3) (v := 1) (Δ := 1) (by norm_num)
    (by norm_num) (by norm_num) unit_norm p.1 p rfl hp
  have hbox := root_in_box (by norm_num) (by norm_num) (by norm_num) unit_norm hρ
  obtain ⟨⟨h1, h2, h3⟩, hpred⟩ := hρ
  norm_num at hbox
  have hY : ρ.2 = 0 ∨ ρ.2 = 1 := by
    have : ρ.2 ≤ 1 := by nlinarith
    omega
  rcases hY with hY | hY
  · have hX : ρ.1 = 1 := by rw [hY] at h3; nlinarith
    refine ⟨j, ?_⟩
    rw [orb, ← hj]
    congr 1
    exact (Prod.ext hX hY).symm
  · exfalso
    have hX : ρ.1 = 3 := by rw [hY] at h3; nlinarith
    apply hpred
    simp only [pred, hX, hY]
    exact ⟨by norm_num, by norm_num, by norm_num⟩

lemma X_odd (j : ℕ) : (orb j).1 % 2 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [orb_succ]; simp only; omega

lemma Y_parity (j : ℕ) : (orb j).2 % 2 = (j : ℤ) % 2 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [orb_succ]; simp only; have := X_odd j; push_cast; omega

lemma X_pos (j : ℕ) : 0 < (orb j).1 := (orb_sol j).1
lemma Y_nonneg (j : ℕ) : 0 ≤ (orb j).2 := (orb_sol j).2.1
lemma norm_eq (j : ℕ) : (orb j).1 ^ 2 - 8 * (orb j).2 ^ 2 = 1 := (orb_sol j).2.2

lemma Y_succ_pos (h : ℕ) : 1 ≤ (orb (h + 1)).2 := by
  rw [orb_succ]; simp only; have := X_pos h; have := Y_nonneg h; omega

lemma X_succ_ge (h : ℕ) : 3 ≤ (orb (h + 1)).1 := by
  rw [orb_succ]; simp only; have := X_pos h; have := Y_nonneg h; omega

lemma X_step (j : ℕ) : (orb j).1 + 2 ≤ (orb (j + 1)).1 := by
  rw [orb_succ]; simp only; have := X_pos j; have := Y_nonneg j; omega

lemma Y_step (j : ℕ) : (orb j).2 + 1 ≤ (orb (j + 1)).2 := by
  rw [orb_succ]; simp only; have := X_pos j; have := Y_nonneg j; omega

/-! ### The coordinates, as natural numbers (index `h ↦ j = h + 1`) -/

/-- `X_{h+1}`. -/
def X' (h : ℕ) : ℕ := (orb (h + 1)).1.toNat
/-- `Y_{h+1}`. -/
def Y' (h : ℕ) : ℕ := (orb (h + 1)).2.toNat

lemma X'_cast (h : ℕ) : ((X' h : ℕ) : ℤ) = (orb (h + 1)).1 := Int.toNat_of_nonneg (X_pos _).le
lemma Y'_cast (h : ℕ) : ((Y' h : ℕ) : ℤ) = (orb (h + 1)).2 := Int.toNat_of_nonneg (Y_nonneg _)

lemma norm' (h : ℕ) : X' h ^ 2 = 8 * Y' h ^ 2 + 1 := by
  have := norm_eq (h + 1)
  rw [← X'_cast, ← Y'_cast] at this
  have : ((X' h ^ 2 : ℕ) : ℤ) = ((8 * Y' h ^ 2 + 1 : ℕ) : ℤ) := by push_cast; linarith
  exact_mod_cast this

lemma X'_odd (h : ℕ) : X' h % 2 = 1 := by
  have := X_odd (h + 1); rw [← X'_cast] at this; omega

lemma Y'_pos (h : ℕ) : 1 ≤ Y' h := by
  have := Y_succ_pos h; rw [← Y'_cast] at this; omega

lemma X'_ge (h : ℕ) : 3 ≤ X' h := by
  have := X_succ_ge h; rw [← X'_cast] at this; omega

lemma X'_mono : StrictMono X' := by
  apply strictMono_nat_of_lt_succ
  intro h
  have := X_step (h + 1); rw [← X'_cast, ← X'_cast] at this; omega

lemma Y'_mono : StrictMono Y' := by
  apply strictMono_nat_of_lt_succ
  intro h
  have := Y_step (h + 1); rw [← Y'_cast, ← Y'_cast] at this; omega

/-- **Every solution of `X^2 = 8 Y^2 + 1` with `Y ≥ 1` is `(X' h, Y' h)`.** -/
lemma sol_nat {X Y : ℕ} (hXY : X ^ 2 = 8 * Y ^ 2 + 1) (hY : 1 ≤ Y) : ∃ h, X' h = X ∧ Y' h = Y := by
  have hX : 0 < X := by
    rcases Nat.eq_zero_or_pos X with h0 | h0
    · rw [h0] at hXY; omega
    · exact h0
  have hsol : Sol 8 1 ((X : ℤ), (Y : ℤ)) := by
    refine ⟨?_, ?_, ?_⟩
    · show (0 : ℤ) < X; exact_mod_cast hX
    · show (0 : ℤ) ≤ Y; positivity
    · show (X : ℤ) ^ 2 - 8 * (Y : ℤ) ^ 2 = 1
      linarith
  obtain ⟨j, hj⟩ := (sol_iff _).mp hsol
  cases j with
  | zero =>
    exfalso
    have h0 : (orb 0).2 = 0 := rfl
    rw [hj] at h0
    simp only at h0
    omega
  | succ h =>
    refine ⟨h, ?_, ?_⟩
    · have := X'_cast h; rw [hj] at this; simp only at this; exact_mod_cast this
    · have := Y'_cast h; rw [hj] at this; simp only at this; exact_mod_cast this

/-- In `m^2 = 2 n^2 + 1`, `n` is even. -/
lemma even_of_pell {m n : ℕ} (h : m ^ 2 = 2 * n ^ 2 + 1) : n % 2 = 0 := by
  have key : ∀ a b : ZMod 8, b ^ 2 = 2 * a ^ 2 + 1 → a.val % 2 = 0 := by decide
  have h8 : ((m : ZMod 8)) ^ 2 = 2 * (n : ZMod 8) ^ 2 + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 8) h
  have := key _ _ h8
  rw [ZMod.val_natCast] at this
  omega

/-! ### The six sequences -/

/-- `n ≥ 1` with `2n^2 + 1` a square. -/
def PellIdx : Set ℕ := {n | 1 ≤ n ∧ ∃ m : ℕ, m ^ 2 = 2 * n ^ 2 + 1}
/-- `m` with `m^2 = 2n^2 + 1` for some `n ≥ 1`. -/
def PellRoot : Set ℕ := {m | ∃ n : ℕ, 1 ≤ n ∧ m ^ 2 = 2 * n ^ 2 + 1}
/-- `t ≥ 1` whose square is triangular. -/
def SqTriRoot : Set ℕ := {t | 1 ≤ t ∧ ∃ u : ℕ, 2 * t ^ 2 = u * (u + 1)}
/-- `u ≥ 1` whose triangular number `u(u+1)/2` is a square. -/
def TriIdx : Set ℕ := {u | 1 ≤ u ∧ ∃ t : ℕ, u * (u + 1) = 2 * t ^ 2}
/-- Square triangular numbers `v ≥ 1`. -/
def SqTri : Set ℕ := {v | 1 ≤ v ∧ (∃ t : ℕ, v = t ^ 2) ∧ ∃ u : ℕ, 2 * v = u * (u + 1)}
/-- Odd square triangular numbers. -/
def OddSqTri : Set ℕ := {v | v ∈ SqTri ∧ v % 2 = 1}

lemma tri_iff {t u : ℕ} : 2 * t ^ 2 = u * (u + 1) ↔ (2 * u + 1) ^ 2 = 8 * t ^ 2 + 1 := by
  constructor <;> intro h <;> nlinarith

theorem sqTriRoot_iff (t : ℕ) : t ∈ SqTriRoot ↔ ∃ h, Y' h = t := by
  constructor
  · rintro ⟨ht, u, hu⟩
    obtain ⟨h, -, hY⟩ := sol_nat (tri_iff.mp hu) ht
    exact ⟨h, hY⟩
  · rintro ⟨h, rfl⟩
    refine ⟨Y'_pos h, (X' h - 1) / 2, tri_iff.mpr ?_⟩
    have := X'_odd h; have := X'_ge h
    have e : 2 * ((X' h - 1) / 2) + 1 = X' h := by omega
    rw [e, norm' h]

theorem triIdx_iff (u : ℕ) : u ∈ TriIdx ↔ ∃ h, (X' h - 1) / 2 = u := by
  constructor
  · rintro ⟨hu, t, ht⟩
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0] at ht; simp at ht; omega
      · exact h0
    obtain ⟨h, hX, -⟩ := sol_nat (tri_iff.mp ht.symm) ht1
    exact ⟨h, by omega⟩
  · rintro ⟨h, rfl⟩
    have := X'_odd h; have := X'_ge h
    refine ⟨by omega, Y' h, ?_⟩
    have e : 2 * ((X' h - 1) / 2) + 1 = X' h := by omega
    exact (tri_iff.mpr (by rw [e, norm' h])).symm

theorem sqTri_iff (v : ℕ) : v ∈ SqTri ↔ ∃ h, Y' h ^ 2 = v := by
  constructor
  · rintro ⟨hv, ⟨t, rfl⟩, u, hu⟩
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0] at hv; simp at hv
      · exact h0
    obtain ⟨h, hY⟩ := (sqTriRoot_iff t).mp ⟨ht, u, hu⟩
    exact ⟨h, by rw [hY]⟩
  · rintro ⟨h, rfl⟩
    obtain ⟨-, u, hu⟩ := (sqTriRoot_iff (Y' h)).mpr ⟨h, rfl⟩
    exact ⟨Nat.one_le_pow _ _ (Y'_pos h), ⟨Y' h, rfl⟩, u, hu⟩

theorem pellIdx_iff (n : ℕ) : n ∈ PellIdx ↔ ∃ h, 2 * Y' h = n := by
  constructor
  · rintro ⟨hn, m, hm⟩
    have he := even_of_pell hm
    obtain ⟨h, -, hY⟩ := sol_nat (X := m) (Y := n / 2) (by
      have e : n = 2 * (n / 2) := by omega
      rw [hm]; conv_lhs => rw [e]
      ring) (by omega)
    exact ⟨h, by omega⟩
  · rintro ⟨h, rfl⟩
    refine ⟨by have := Y'_pos h; omega, X' h, ?_⟩
    rw [norm' h]; ring

theorem pellRoot_iff (m : ℕ) : m ∈ PellRoot ↔ ∃ h, X' h = m := by
  constructor
  · rintro ⟨n, hn, hm⟩
    have he := even_of_pell hm
    obtain ⟨h, hX, -⟩ := sol_nat (X := m) (Y := n / 2) (by
      have e : n = 2 * (n / 2) := by omega
      rw [hm]; conv_lhs => rw [e]
      ring) (by omega)
    exact ⟨h, hX⟩
  · rintro ⟨h, rfl⟩
    refine ⟨2 * Y' h, by have := Y'_pos h; omega, ?_⟩
    rw [norm' h]; ring

theorem oddSqTri_iff (v : ℕ) : v ∈ OddSqTri ↔ ∃ h, h % 2 = 0 ∧ Y' h ^ 2 = v := by
  have hpar : ∀ h, Y' h % 2 = (h + 1) % 2 := by
    intro h
    have := Y_parity (h + 1)
    rw [← Y'_cast] at this
    push_cast at this
    omega
  constructor
  · rintro ⟨hv, hodd⟩
    obtain ⟨h, rfl⟩ := (sqTri_iff v).mp hv
    refine ⟨h, ?_, rfl⟩
    have := hpar h
    rcases Nat.even_or_odd (Y' h) with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk] at hodd; ring_nf at hodd; omega
    · omega
  · rintro ⟨h, hh, rfl⟩
    refine ⟨(sqTri_iff _).mpr ⟨h, rfl⟩, ?_⟩
    have := hpar h
    obtain ⟨k, hk⟩ : ∃ k, Y' h = 2 * k + 1 := ⟨Y' h / 2, by omega⟩
    rw [hk]; ring_nf; omega

/-! ### Growth -/

/-- `ε = 3 + √8 = 3 + 2√2`. -/
lemma eps_eq : eps 8 3 1 = 3 + 2 * Real.sqrt 2 := by
  have : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  simp only [eps]; push_cast; rw [this]; ring

lemma eps_ge : 5 ≤ eps 8 3 1 := by
  rw [eps_eq]
  have : 1 ≤ Real.sqrt 2 := by rw [Real.one_le_sqrt]; norm_num
  linarith

lemma X_bounds (h : ℕ) :
    eps 8 3 1 ^ h / 4 ≤ ((orb (h + 1)).1 : ℝ) ∧ ((orb (h + 1)).1 : ℝ) ≤ eps 8 3 1 * eps 8 3 1 ^ h := by
  have hb := orbit_fst_bracket (D := 8) (u := 3) (v := 1) (by norm_num) unit_norm (by norm_num)
    (by norm_num) (1, 0) (h + 1)
  have he : eta 8 (1, 0) = 1 := by simp [eta]
  have hb' : etaBar 8 (1, 0) = 1 := by simp [etaBar]
  rw [he, hb', abs_one] at hb
  have hε := eps_ge
  have hpow : 1 ≤ eps 8 3 1 ^ h := one_le_pow₀ (by linarith)
  rw [pow_succ] at hb
  change |((orb (h + 1)).1 : ℝ) - _| ≤ _ at hb
  have hab := abs_le.mp hb
  have hprod : 5 * eps 8 3 1 ^ h ≤ eps 8 3 1 ^ h * eps 8 3 1 := by nlinarith
  constructor <;> nlinarith [hab.1, hab.2]

lemma Y_bounds (h : ℕ) : ((orb (h + 1)).1 : ℝ) / 3 ≤ (orb (h + 1)).2 ∧
    ((orb (h + 1)).2 : ℝ) ≤ ((orb (h + 1)).1 : ℝ) / 2 := by
  have hn := norm_eq (h + 1)
  have hX := X_succ_ge h
  have hY := Y_nonneg (h + 1)
  have hn' : ((orb (h + 1)).1 : ℝ) ^ 2 - 8 * ((orb (h + 1)).2 : ℝ) ^ 2 = 1 := by exact_mod_cast hn
  have hX' : (3 : ℝ) ≤ (orb (h + 1)).1 := by exact_mod_cast hX
  have hY' : (0 : ℝ) ≤ (orb (h + 1)).2 := by exact_mod_cast hY
  constructor <;> nlinarith

/-! ### The counts -/

/-- One observed orbit, specialized from `observed_count`. -/
lemma single_count (obs : ℕ → ℕ) {E c₁ c₂ : ℝ} (hE : 1 < E) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlow : ∀ j, c₁ * E ^ j ≤ obs j) (hup : ∀ j, (obs j : ℝ) ≤ c₂ * E ^ j) (hmono : StrictMono obs)
    {P : ℕ} (hP : 0 < P) (q : ℕ → Prop) (hq : ∀ j, q (j + P) ↔ q j)
    (S : Set ℕ) (hS : ∀ v, v ∈ S ↔ ∃ j, q j ∧ obs j = v) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      |((#{v ∈ Icc 1 N | v ∈ S} : ℕ) : ℝ) -
        (#((range P).filter q) : ℝ) / (P * Real.log E) * Real.log N| ≤ K := by
  obtain ⟨K, hK⟩ := observed_count ({()} : Finset Unit) (fun _ => obs) (fun _ => E) (fun _ => c₁)
    (fun _ => c₂) (fun _ _ => hE) (fun _ _ => hc₁) (fun _ _ => hc₂) (fun _ _ => hlow)
    (fun _ _ => hup) (fun _ => P) (fun _ _ => hP) (fun _ => q) (fun _ _ => hq)
    (fun _ _ => hmono) 0 (fun _ _ _ _ _ _ _ _ _ _ => rfl) S
    (fun v => by rw [hS]; simp)
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  simpa using this

lemma pos_E : 1 < eps 8 3 1 := by linarith [eps_ge]

lemma cast_toNat {z : ℤ} (hz : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]

lemma X'_real (h : ℕ) : ((X' h : ℕ) : ℝ) = ((orb (h + 1)).1 : ℝ) := cast_toNat (X_pos _).le
lemma Y'_real (h : ℕ) : ((Y' h : ℕ) : ℝ) = ((orb (h + 1)).2 : ℝ) := cast_toNat (Y_nonneg _)

/-- **`#{t ≤ N : t^2 triangular} = log N / log ε + O(1)`.** -/
theorem sqTriRoot_count : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |((#{t ∈ Icc 1 N | t ∈ SqTriRoot} : ℕ) : ℝ) - Real.log N / Real.log (eps 8 3 1)| ≤ K := by
  obtain ⟨K, hK⟩ := single_count Y' pos_E (by norm_num : (0 : ℝ) < 1 / 12)
    (by linarith [eps_ge] : (0 : ℝ) < eps 8 3 1 / 2)
    (fun h => by rw [Y'_real]; have := X_bounds h; have := Y_bounds h; nlinarith)
    (fun h => by rw [Y'_real]; have := X_bounds h; have := Y_bounds h; nlinarith)
    Y'_mono one_pos (fun _ => True) (fun _ => Iff.rfl) SqTriRoot (fun v => by simp [sqTriRoot_iff])
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  rw [div_eq_inv_mul]; simpa using this

/-- **`#{u ≤ N : u(u+1)/2 a square} = log N / log ε + O(1)`.** -/
theorem triIdx_count : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |((#{u ∈ Icc 1 N | u ∈ TriIdx} : ℕ) : ℝ) - Real.log N / Real.log (eps 8 3 1)| ≤ K := by
  have hreal : ∀ h, (((X' h - 1) / 2 : ℕ) : ℝ) = (((orb (h + 1)).1 : ℝ) - 1) / 2 := by
    intro h
    have := X'_odd h; have := X'_ge h
    have e : 2 * ((X' h - 1) / 2) + 1 = X' h := by omega
    have : ((X' h : ℕ) : ℝ) = 2 * (((X' h - 1) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast e.symm
    rw [← X'_real]; linarith
  have hmono : StrictMono (fun h => (X' h - 1) / 2) := by
    apply strictMono_nat_of_lt_succ
    intro h
    have := X'_mono (show h < h + 1 by omega); have := X'_odd h; have := X'_odd (h + 1)
    have := X'_ge h
    omega
  obtain ⟨K, hK⟩ := single_count (fun h => (X' h - 1) / 2) pos_E (by norm_num : (0 : ℝ) < 1 / 12)
    (by linarith [eps_ge] : (0 : ℝ) < eps 8 3 1 / 2)
    (fun h => by
      rw [hreal]; have := X_bounds h; have := X_succ_ge h
      have : (3 : ℝ) ≤ (orb (h + 1)).1 := by exact_mod_cast this
      nlinarith)
    (fun h => by rw [hreal]; have := X_bounds h; nlinarith)
    hmono one_pos (fun _ => True) (fun _ => Iff.rfl) TriIdx (fun v => by simp [triIdx_iff])
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  rw [div_eq_inv_mul]; simpa using this

/-- **`#{n ≤ N : 2n^2 + 1 a square} = log N / log ε + O(1)`.** -/
theorem pellIdx_count : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |((#{n ∈ Icc 1 N | n ∈ PellIdx} : ℕ) : ℝ) - Real.log N / Real.log (eps 8 3 1)| ≤ K := by
  have hmono : StrictMono (fun h => 2 * Y' h) := fun a b hab => by
    have := Y'_mono hab; simp only; omega
  obtain ⟨K, hK⟩ := single_count (fun h => 2 * Y' h) pos_E (by norm_num : (0 : ℝ) < 1 / 6)
    (by linarith [eps_ge] : (0 : ℝ) < eps 8 3 1)
    (fun h => by push_cast; rw [Y'_real]; have := X_bounds h; have := Y_bounds h; nlinarith)
    (fun h => by push_cast; rw [Y'_real]; have := X_bounds h; have := Y_bounds h; nlinarith)
    hmono one_pos (fun _ => True) (fun _ => Iff.rfl) PellIdx (fun v => by simp [pellIdx_iff])
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  rw [div_eq_inv_mul]; simpa using this

/-- **`#{m ≤ N : m^2 = 2n^2 + 1, n ≥ 1} = log N / log ε + O(1)`.** -/
theorem pellRoot_count : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |((#{m ∈ Icc 1 N | m ∈ PellRoot} : ℕ) : ℝ) - Real.log N / Real.log (eps 8 3 1)| ≤ K := by
  obtain ⟨K, hK⟩ := single_count X' pos_E (by norm_num : (0 : ℝ) < 1 / 4)
    (by linarith [eps_ge] : (0 : ℝ) < eps 8 3 1)
    (fun h => by rw [X'_real]; have := X_bounds h; linarith)
    (fun h => by rw [X'_real]; exact (X_bounds h).2)
    X'_mono one_pos (fun _ => True) (fun _ => Iff.rfl) PellRoot (fun v => by simp [pellRoot_iff])
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  rw [div_eq_inv_mul]; simpa using this

lemma Y2_bounds (h : ℕ) : 1 / 144 * (eps 8 3 1 ^ 2) ^ h ≤ ((Y' h ^ 2 : ℕ) : ℝ) ∧
    ((Y' h ^ 2 : ℕ) : ℝ) ≤ eps 8 3 1 ^ 2 / 4 * (eps 8 3 1 ^ 2) ^ h := by
  push_cast
  rw [Y'_real, ← pow_mul, mul_comm 2 h, pow_mul]
  obtain ⟨hx1, hx2⟩ := X_bounds h
  obtain ⟨hy1, hy2⟩ := Y_bounds h
  have hε := eps_ge
  have hy0 : 0 ≤ ((orb (h + 1)).2 : ℝ) := by exact_mod_cast Y_nonneg (h + 1)
  constructor
  · have : eps 8 3 1 ^ h / 12 ≤ ((orb (h + 1)).2 : ℝ) := by linarith
    have := mul_le_mul this this (by positivity) hy0
    nlinarith
  · have : ((orb (h + 1)).2 : ℝ) ≤ eps 8 3 1 * eps 8 3 1 ^ h / 2 := by linarith
    have := mul_le_mul this this hy0 (by positivity)
    nlinarith

lemma sq_mono : StrictMono (fun h => Y' h ^ 2) := fun _ _ hab =>
  Nat.pow_lt_pow_left (Y'_mono hab) two_ne_zero

lemma E2 : 1 < eps 8 3 1 ^ 2 := one_lt_pow₀ pos_E two_ne_zero

/-- **Square triangular numbers: `#{v ≤ N} = log N / (2 log ε) + O(1)`**, half the rate of their
square roots, from the same orbit. -/
theorem sqTri_count : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |((#{v ∈ Icc 1 N | v ∈ SqTri} : ℕ) : ℝ) - Real.log N / (2 * Real.log (eps 8 3 1))| ≤ K := by
  obtain ⟨K, hK⟩ := single_count (fun h => Y' h ^ 2) E2 (by norm_num : (0 : ℝ) < 1 / 144)
    (by have := eps_ge; positivity : (0 : ℝ) < eps 8 3 1 ^ 2 / 4)
    (fun h => (Y2_bounds h).1) (fun h => (Y2_bounds h).2)
    sq_mono one_pos (fun _ => True) (fun _ => Iff.rfl) SqTri (fun v => by simp [sqTri_iff])
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  simp only [Real.log_pow] at this
  have e : Real.log N / (2 * Real.log (eps 8 3 1)) = (Real.log (eps 8 3 1))⁻¹ * 2⁻¹ * Real.log N := by
    ring
  rw [e]; simpa using this

/-- **Odd square triangular numbers: `#{v ≤ N} = log N / (4 log ε) + O(1)`**: the filter
`j` odd accepts `g = 1` of `P = 2` residues. -/
theorem oddSqTri_count : ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |((#{v ∈ Icc 1 N | v ∈ OddSqTri} : ℕ) : ℝ) - Real.log N / (4 * Real.log (eps 8 3 1))| ≤ K := by
  obtain ⟨K, hK⟩ := single_count (fun h => Y' h ^ 2) E2 (by norm_num : (0 : ℝ) < 1 / 144)
    (by have := eps_ge; positivity : (0 : ℝ) < eps 8 3 1 ^ 2 / 4)
    (fun h => (Y2_bounds h).1) (fun h => (Y2_bounds h).2)
    sq_mono two_pos (fun h => h % 2 = 0) (fun j => by omega) OddSqTri
    (fun v => oddSqTri_iff v)
  refine ⟨K, fun N hN => ?_⟩
  have := hK N hN
  have h0 : (@Finset.filter ℕ (fun h => h % 2 = 0) (fun h => Nat.decEq _ _) (range 2)).card = 1 := by
    decide
  have hc : ∀ inst : DecidablePred (fun h : ℕ => h % 2 = 0),
      (@Finset.filter ℕ (fun h => h % 2 = 0) inst (range 2)).card = 1 := by
    intro inst
    convert h0
  rw [hc, Real.log_pow] at this
  have e : Real.log N / (4 * Real.log (eps 8 3 1)) =
      (Real.log (eps 8 3 1))⁻¹ * 2⁻¹ * 2⁻¹ * Real.log N := by ring
  rw [e]; simpa using this

end PerfectPower.SquareTriangular
