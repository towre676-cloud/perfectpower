import PerfectPower.Continuation.KappaPositive

/-!
# When is the Pell constant positive?

For one branch `A n^2 + B n + C ∈ □` (`A > 0` not a square, `B^2 - 4AC ≠ 0`):

* `branch_point_infinite`: **one point suffices.**  A single integer `n₀` with `2A n₀ + B > 0`
  and a square value gives infinitely many hits.  `(X₀, |m|)` lies in the quadrant `X > 0`,
  and moving along the unit orbit in steps of a period modulo `2A` (`short_period`, at most
  `(2A)^2`) gives hits with strictly increasing `X` (`goodClass_hits`, `orbit_mono`).
* `branch_bounded_witness`: **a bounded search.**  Every quadrant solution lies on the orbit
  of a root in the box `4A Y^2 ≤ |Δ| u^2` (`PellExact.exists_root`, `root_in_box`).  The good
  orbit index can be taken below the period, and `X + Y` grows at most by
  `c = 2u + (4A + 1) v` per step (`orbit_growth`), so a witness exists with
  `n ≤ c^{(2A)^2} (2 |Δ| (1 + u^2) + 2) + |B|`.
* `branch_infinite_iff`: the branch is infinite iff `A > 0`, `A` is not a square, and one point
  with `2An + B > 0` exists; `branch_infinite_iff_bounded` gives the finite search, for any unit.

For a general `F` of Pell type, `Decomposition.pell_kappa_decide`: the constant `κ` is positive
iff some root `γ` of `γ^e = lc(F)` is positive and not a rational square, and `γ Q(n)` is a
rational square at one integer `n` past the vertex (`2n + b > 0`, `Q = X^2 + bX + c`).
-/

open Finset Polynomial
open scoped Classical

namespace PerfectPower.RationalYun

/-! ### Orbits: a short period, monotonicity and growth -/

/-- The orbit modulo `M` has a period `Q` with `0 < Q ≤ M^2` (pigeonhole). -/
theorem short_period (M : ℕ) [NeZero M] {D x₁ y₁ : ℤ} (hu : x₁ ^ 2 - D * y₁ ^ 2 = 1)
    (p₀ : ℤ × ℤ) :
    ∃ Q, 0 < Q ∧ Q ≤ M ^ 2 ∧ ∀ j, (M : ℤ) ∣
      (unitOrbit D x₁ y₁ p₀ (j + Q)).1 - (unitOrbit D x₁ y₁ p₀ j).1 := by
  set σ := unitPerm M D x₁ y₁ hu
  set x : ZMod M × ZMod M := ((p₀.1 : ZMod M), (p₀.2 : ZMod M))
  have hcard : (univ : Finset (ZMod M × ZMod M)).card < (range (M ^ 2 + 1)).card := by
    rw [card_univ, Fintype.card_prod, ZMod.card, card_range, sq]
    exact Nat.lt_succ_self _
  obtain ⟨a, ha, b, hb, hab, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun j => (σ ^ j) x) (fun _ _ => mem_univ _)
  have key : ∀ a b : ℕ, a < b → b ≤ M ^ 2 → (σ ^ a) x = (σ ^ b) x →
      ∃ Q, 0 < Q ∧ Q ≤ M ^ 2 ∧ ∀ j, (M : ℤ) ∣
        (unitOrbit D x₁ y₁ p₀ (j + Q)).1 - (unitOrbit D x₁ y₁ p₀ j).1 := by
    intro a b hlt hbM h
    refine ⟨b - a, by omega, by omega, fun j => ?_⟩
    have hQ : (σ ^ (b - a)) x = x := by
      apply (σ ^ a).injective
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
      exact h.symm
    have hj : (σ ^ (j + (b - a))) x = (σ ^ j) x := by rw [pow_add, Equiv.Perm.mul_apply, hQ]
    have h1 := cast_unitOrbit M hu p₀ (j + (b - a))
    have h2 := cast_unitOrbit M hu p₀ j
    rw [hj, ← h2] at h1
    simp only [Prod.mk.injEq] at h1
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1.1.symm
  simp only [mem_range] at ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h (by omega) heq
  · exact key b a h (by omega) heq.symm

lemma period_iter {D x₁ y₁ : ℤ} {p₀ : ℤ × ℤ} {M : ℤ} {Q : ℕ}
    (hper : ∀ j, M ∣ (unitOrbit D x₁ y₁ p₀ (j + Q)).1 - (unitOrbit D x₁ y₁ p₀ j).1) (r : ℕ) :
    ∀ k : ℕ, M ∣ (unitOrbit D x₁ y₁ p₀ (r + k * Q)).1 - (unitOrbit D x₁ y₁ p₀ r).1
  | 0 => by simp
  | k + 1 => by
    have := dvd_add (hper (r + k * Q)) (period_iter hper r k)
    rw [show r + (k + 1) * Q = r + k * Q + Q by ring]
    simpa using this

/-- Along the orbit of a quadrant solution, `X` increases by at least one per step. -/
lemma orbit_mono {D u v Δ : ℤ} (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u)
    (hv : 0 ≤ v) {p : ℤ × ℤ} (hp : PellExact.Sol D Δ p) :
    ∀ j : ℕ, p.1 + j ≤ (unitOrbit D u v p j).1
  | 0 => by simp [unitOrbit]
  | j + 1 => by
    have ih := orbit_mono hD hu hu1 hv hp j
    have hs := PellExact.orbit_sol hD hu hu1.le hv hp j
    have hgt := PellExact.unitAct_fst_gt hD hu1 hv hs
    rw [PellExact.orbit_succ]
    push_cast
    linarith

/-- Along the orbit of a quadrant solution, `X + Y` grows at most by `c = 2u + (D + 1) v`. -/
lemma orbit_growth {D u v Δ : ℤ} (hD : 0 ≤ D) (hu : u ^ 2 - D * v ^ 2 = 1) (hu1 : 1 < u)
    (hv : 0 ≤ v) {p : ℤ × ℤ} (hp : PellExact.Sol D Δ p) :
    ∀ j : ℕ, (unitOrbit D u v p j).1 + (unitOrbit D u v p j).2 ≤
      (2 * u + (D + 1) * v) ^ j * (p.1 + p.2)
  | 0 => by simp [unitOrbit]
  | j + 1 => by
    have ih := orbit_growth hD hu hu1 hv hp j
    obtain ⟨hX, hY, -⟩ := PellExact.orbit_sol hD hu hu1.le hv hp j
    rw [PellExact.orbit_succ, pow_succ]
    simp only [unitAct]
    set X := (unitOrbit D u v p j).1
    set Y := (unitOrbit D u v p j).2
    have hc : 0 ≤ 2 * u + (D + 1) * v := by nlinarith
    have hstep : X * u + D * Y * v + (X * v + Y * u) ≤ (2 * u + (D + 1) * v) * (X + Y) := by
      nlinarith [mul_nonneg (mul_nonneg hD hY) hv, mul_nonneg hX.le hv, mul_nonneg hY hv,
        mul_nonneg (mul_nonneg hD hX.le) hv]
    calc X * u + D * Y * v + (X * v + Y * u) ≤ (2 * u + (D + 1) * v) * (X + Y) := hstep
      _ ≤ (2 * u + (D + 1) * v) * ((2 * u + (D + 1) * v) ^ j * (p.1 + p.2)) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = _ := by ring

/-- Roots are small: `X + Y ≤ 2 |Δ| (1 + u^2) + 2`. -/
lemma root_small {D u v Δ : ℤ} (hD : 1 ≤ D) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - D * v ^ 2 = 1) {ρ : ℤ × ℤ} (hρ : PellExact.IsRoot D u v Δ ρ) :
    ρ.1 + ρ.2 ≤ 2 * (|Δ| * (1 + u ^ 2)) + 2 := by
  have hbox := PellExact.root_in_box (by omega) hu1 hv hu hρ
  obtain ⟨hX, hY, hN⟩ := hρ.1
  have hΔ := abs_nonneg Δ
  have hD2 : ρ.2 ^ 2 ≤ D * ρ.2 ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sq_nonneg ρ.2)]
  have hX2 : ρ.1 ^ 2 ≤ |Δ| * (1 + u ^ 2) := by nlinarith [le_abs_self Δ]
  have hXZ : ρ.1 ≤ |Δ| * (1 + u ^ 2) + 1 := by nlinarith [sq_nonneg (ρ.1 - 1)]
  have hYZ : ρ.2 ≤ |Δ| * (1 + u ^ 2) + 1 := by nlinarith [sq_nonneg (ρ.2 - 1)]
  linarith

/-! ### One branch -/

/-- Data of a branch with a unit: `A > 0`, `u^2 - 4A v^2 = 1`, `u > 1`, `v > 0`. -/
theorem branch_point_infinite {A B C u v : ℤ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) {n₀ : ℤ} (hX : 0 < 2 * A * n₀ + B)
    (hhit : IsHit 2 (A * n₀ ^ 2 + B * n₀ + C)) :
    {n : ℕ | 1 ≤ n ∧ IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)}.Infinite := by
  obtain ⟨m, hm⟩ := hhit
  set p₀ : ℤ × ℤ := (2 * A * n₀ + B, |m|)
  have h₀ : p₀.1 ^ 2 - 4 * A * p₀.2 ^ 2 = B ^ 2 - 4 * A * C := by
    simp only [p₀, sq_abs]; linear_combination (4 * A) * hm
  have hsol : PellExact.Sol (4 * A) (B ^ 2 - 4 * A * C) p₀ := ⟨hX, abs_nonneg m, h₀⟩
  set M := (2 * A).toNat
  have hM : (M : ℤ) = 2 * A := Int.toNat_of_nonneg (by omega)
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨Q, hQ, -, hper⟩ := short_period M hu p₀
  rw [hM] at hper
  intro hfin
  obtain ⟨T, hT⟩ := hfin.bddAbove
  set k := (2 * A * (T + 1) + |B|).toNat
  obtain ⟨n, hn, hhitn⟩ := goodClass_hits (ne_of_gt hA) hu h₀ hper (r := 0)
    ⟨n₀, by simp [p₀, unitOrbit]⟩ k
  have hmono := orbit_mono (by omega) hu hu1 hv.le hsol (0 + k * Q)
  have hk : (k : ℤ) = 2 * A * (T + 1) + |B| := Int.toNat_of_nonneg (by positivity)
  have hkQ : (k : ℤ) ≤ ((0 + k * Q : ℕ) : ℤ) := by
    push_cast; nlinarith [(by exact_mod_cast hQ : (1 : ℤ) ≤ Q)]
  have hn_big : (T : ℤ) + 1 < n := by
    have : 2 * A * n > 2 * A * (T + 1) := by
      simp only [p₀] at hmono
      nlinarith [neg_abs_le B, le_abs_self B]
    nlinarith
  have hnn : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
  have hmem : n.toNat ∈ {n : ℕ | 1 ≤ n ∧ IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)} :=
    ⟨by omega, by rw [hnn]; exact hhitn⟩
  have := hT hmem
  omega

/-- **The bounded search.**  An infinite branch has a witness with
`-|B| ≤ n ≤ c^{(2A)^2} (2|Δ|(1 + u^2) + 2) + |B|`, `c = 2u + (4A + 1) v`. -/
theorem branch_bounded_witness {A B C u v : ℤ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1)
    (hinf : {n : ℕ | 1 ≤ n ∧ IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)}.Infinite) :
    ∃ n : ℤ, -|B| ≤ n ∧
      n ≤ (2 * u + (4 * A + 1) * v) ^ ((2 * A).toNat ^ 2) *
        (2 * (|B ^ 2 - 4 * A * C| * (1 + u ^ 2)) + 2) + |B| ∧
      0 < 2 * A * n + B ∧ IsHit 2 (A * n ^ 2 + B * n + C) := by
  set Δ := B ^ 2 - 4 * A * C
  obtain ⟨n₁, ⟨-, ⟨m, hm⟩⟩, hn₁⟩ := hinf.exists_gt B.natAbs
  have hX : 0 < 2 * A * (n₁ : ℤ) + B := by
    have : (B.natAbs : ℤ) < n₁ := by exact_mod_cast hn₁
    have : -(B.natAbs : ℤ) ≤ B := by rw [← Int.abs_eq_natAbs]; exact neg_abs_le B
    nlinarith
  set p : ℤ × ℤ := (2 * A * n₁ + B, |m|)
  have hsol : PellExact.Sol (4 * A) Δ p :=
    ⟨hX, abs_nonneg m, by simp only [p, sq_abs, Δ]; linear_combination (4 * A) * hm⟩
  obtain ⟨ρ, j, hρ, hj⟩ := PellExact.exists_root (by omega) hu1 hv hu _ p rfl hsol
  set M := (2 * A).toNat
  have hM : (M : ℤ) = 2 * A := Int.toNat_of_nonneg (by omega)
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨Q, hQ, hQM, hper⟩ := short_period M hu ρ
  rw [hM] at hper
  set r := j % Q
  have hjr : j = r + (j / Q) * Q := by rw [Nat.mod_add_div' j Q]
  have hrQ : r < Q := Nat.mod_lt j hQ
  -- `X_r ≡ X_j ≡ B (mod 2A)`
  have hjB : 2 * A ∣ (unitOrbit (4 * A) u v ρ j).1 - B := ⟨n₁, by rw [hj]; simp [p]⟩
  have hrB : 2 * A ∣ (unitOrbit (4 * A) u v ρ r).1 - B := by
    have := period_iter hper r (j / Q)
    rw [← hjr] at this
    have h2 := dvd_sub hjB this
    simpa using h2
  obtain ⟨n, hn⟩ := hrB
  have hsolr := PellExact.orbit_sol (by omega) hu hu1.le hv.le hρ.1 r
  have hXr : 0 < 2 * A * n + B := by linarith [hsolr.1]
  refine ⟨n, ?_, ?_, hXr, ?_⟩
  · nlinarith [neg_abs_le B, le_abs_self B]
  · -- `X_r + Y_r ≤ c^r (X_ρ + Y_ρ) ≤ c^{M^2} (2 |Δ| (1 + u^2) + 2)`
    have hgrow := orbit_growth (by omega) hu hu1 hv.le hρ.1 r
    have hsmall := root_small (by omega) hu1 hv hu hρ
    set c := 2 * u + (4 * A + 1) * v
    have hc1 : 1 ≤ c := by
      have : 0 < (4 * A + 1) * v := mul_pos (by omega) hv
      simp only [c]; linarith
    have hpow : c ^ r ≤ c ^ (M ^ 2) := pow_le_pow_right₀ hc1 (by omega)
    have hρ0 : 0 ≤ ρ.1 + ρ.2 := by linarith [hρ.1.1, hρ.1.2.1]
    have h1 : c ^ r * (ρ.1 + ρ.2) ≤ c ^ (M ^ 2) * (2 * (|Δ| * (1 + u ^ 2)) + 2) :=
      mul_le_mul hpow hsmall hρ0 (by positivity)
    have hYr := hsolr.2.1
    nlinarith [neg_abs_le B, le_abs_self B, pow_nonneg (by omega : (0 : ℤ) ≤ c) (M ^ 2),
      abs_nonneg Δ]
  · refine (quadratic_isHit_iff_norm hA.ne' B C n).mpr ⟨(unitOrbit (4 * A) u v ρ r).2, ?_⟩
    rw [show 2 * A * n + B = (unitOrbit (4 * A) u v ρ r).1 by linarith, unitOrbit_norm hu,
      hρ.1.2.2]

/-- **One branch, decided.**  With `A ≠ 0` and nonzero discriminant, the branch is infinite iff
`A > 0`, `A` is not a square, and one integer point with `2An + B > 0` exists. -/
theorem branch_infinite_iff {A B C : ℤ} (hA : A ≠ 0) (hdisc : B ^ 2 - 4 * A * C ≠ 0) :
    {n : ℕ | 1 ≤ n ∧ IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)}.Infinite ↔
      0 < A ∧ ¬ IsSquare A ∧ ∃ n : ℤ, 0 < 2 * A * n + B ∧ IsHit 2 (A * n ^ 2 + B * n + C) := by
  have finite_of_bound : ∀ M : ℕ, (∀ n : ℕ, 1 ≤ n → IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C) →
      n ≤ M) → ¬ {n : ℕ | 1 ≤ n ∧ IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)}.Infinite := by
    intro M hM hinf
    obtain ⟨n, ⟨hn1, hn⟩, hnM⟩ := hinf.exists_gt M
    have := hM n hn1 hn
    omega
  constructor
  · intro hinf
    rcases lt_or_gt_of_ne hA with hneg | hpos
    · exact absurd hinf (finite_of_bound _ (hit_le_of_neg hneg))
    by_cases hsq : IsSquare A
    · exact absurd hinf (finite_of_bound _ (hit_le_of_square hpos hsq hdisc))
    refine ⟨hpos, hsq, ?_⟩
    obtain ⟨n, ⟨-, hn⟩, hnB⟩ := hinf.exists_gt B.natAbs
    refine ⟨n, ?_, hn⟩
    have : (B.natAbs : ℤ) < n := by exact_mod_cast hnB
    have : -(B.natAbs : ℤ) ≤ B := by rw [← Int.abs_eq_natAbs]; exact neg_abs_le B
    nlinarith
  · rintro ⟨hpos, hsq, n₀, hX, hhit⟩
    have h4 : ¬ IsSquare (4 * A) := fun h => hsq (isSquare_of_isSquare_four_mul h)
    obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare (by omega : 0 < 4 * A) h4
    have hv : 0 < |y| := abs_pos.mpr hy
    have hu : |x| ^ 2 - 4 * A * |y| ^ 2 = 1 := by rw [sq_abs, sq_abs]; exact hxy
    have hu1 : 1 < |x| := by
      have hy2 : 1 ≤ |y| ^ 2 := by nlinarith
      nlinarith [abs_nonneg x]
    exact branch_point_infinite hpos hu1 hv hu hX hhit

/-- **One branch, decided by a finite search**, for any unit `(u, v)`. -/
theorem branch_infinite_iff_bounded {A B C u v : ℤ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) :
    {n : ℕ | 1 ≤ n ∧ IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)}.Infinite ↔
      ∃ n : ℤ, -|B| ≤ n ∧
        n ≤ (2 * u + (4 * A + 1) * v) ^ ((2 * A).toNat ^ 2) *
          (2 * (|B ^ 2 - 4 * A * C| * (1 + u ^ 2)) + 2) + |B| ∧
        0 < 2 * A * n + B ∧ IsHit 2 (A * n ^ 2 + B * n + C) := by
  constructor
  · exact branch_bounded_witness hA hu1 hv hu
  · rintro ⟨n, -, -, hX, hhit⟩
    exact branch_point_infinite hA hu1 hv hu hX hhit

/-! ### A general `F` of Pell type -/

/-- **Theorem C, positivity decided.**  For `F` of Pell type, the constant `κ` of
`A(N) = κ log N + O(1)` is positive iff some root `γ` of `γ^e = lc(F)` is positive and not a
rational square, and `γ Q(n)` is a rational square at one integer `n` with `2n + b > 0`, where
`Q = X^2 + b X + c` is the Pell quadratic. -/
theorem Decomposition.pell_kappa_decide {F : ℤ[X]}
    (Y : Decomposition (F.map (Int.castRingHom ℚ))) {e : ℕ} (he : e ≠ 0)
    (hres : ∀ j ∈ Finset.range Y.m,
      (j + 1) % (2 * e) = 0 ∨ (j + 1) % (2 * e) = e ∨ Y.part (j + 1) = 1)
    (hdegree : (∑ j ∈ (Finset.range Y.m).filter (fun j => (j + 1) % (2 * e) = e),
      (Y.part (j + 1)).natDegree) = 2) :
    ∃ κ K : ℝ, 0 ≤ κ ∧ (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(#((Icc 1 N).filter fun n : ℕ => IsHit (2 * e) (F.eval (n : ℤ))) : ℝ) -
        κ * Real.log N| ≤ K) ∧
      (0 < κ ↔ ∃ γ : ℚ, γ ^ e = F.leadingCoeff ∧ 0 < γ ∧ ¬ IsSquare γ ∧
        ∃ n : ℤ, 0 < 2 * (n : ℚ) + (Y.pellPart e).coeff 1 ∧
          RatPower (γ * (Y.pellPart e).eval (n : ℚ)) 2) := by
  obtain ⟨κ, K, hκ, hK, hpos⟩ := Y.pell_count_pos he hres hdegree
  refine ⟨κ, K, hκ, hK, ?_⟩
  rw [hpos]
  obtain ⟨hmon, hdeg, hiff⟩ := Y.integer_pell_reduction he hres hdegree
  have hFq : F.map (Int.castRingHom ℚ) ≠ 0 := Y.ne_zero
  have hF : F ≠ 0 := by rintro rfl; exact hFq (Polynomial.map_zero _)
  set Q := Y.pellPart e
  have hdisc := disc_ne_zero (pellPart_squarefree Y e) hmon hdeg
  have hlc : (F.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hF
  set P : ℚ → ℕ → Prop := fun γ n => RatPower (γ * Q.eval (n : ℚ)) 2 with hPdef
  -- the hit set, without the finitely many zeros, is a union over the roots `γ`
  have eset : {n : ℕ | 1 ≤ n ∧ IsHit (2 * e) (F.eval (n : ℤ))} =
      {n : ℕ | 1 ≤ n ∧ (F.eval (n : ℤ) = 0 ∨ ∃ γ : ℚ, γ ^ e = F.leadingCoeff ∧ P γ n)} := by
    ext n; simp only [Set.mem_setOf_eq]; rw [hiff n]; simp only [hPdef, Int.cast_natCast]
  rw [eset, infinite_or_finite _ _ (zeros_finite F hF)]
  -- the roots `γ` form a finite set
  have hroots_fin : {γ : ℚ | γ ^ e = F.leadingCoeff}.Finite := by
    by_cases hγ : ∃ γ₀ : ℚ, γ₀ ^ e = F.leadingCoeff
    · obtain ⟨γ₀, hγ₀⟩ := hγ
      apply (Set.toFinite ({γ₀, -γ₀} : Set ℚ)).subset
      intro γ hγ
      simp only [Set.mem_setOf_eq] at hγ
      rw [← hγ₀] at hγ
      rcases (pow_eq_pow_iff_of_ne_zero he).mp hγ with h | ⟨h, -⟩
      · simp [h]
      · simp [h]
    · push_neg at hγ
      convert Set.finite_empty
      ext γ; simp [hγ γ]
  -- each branch, decided
  have hbranch : ∀ γ : ℚ, γ ^ e = F.leadingCoeff →
      ({n : ℕ | 1 ≤ n ∧ P γ n}.Infinite ↔ 0 < γ ∧ ¬ IsSquare γ ∧
        ∃ n : ℤ, 0 < 2 * (n : ℚ) + Q.coeff 1 ∧ RatPower (γ * Q.eval (n : ℚ)) 2) := by
    intro γ hγe
    have hγ : γ ≠ 0 := by rintro rfl; rw [zero_pow he] at hγe; exact hlc hγe.symm
    obtain ⟨A, B, C, hA, hD, ⟨s, hs, hAs, hBs⟩, hPA⟩ :=
      clear_denoms γ (Q.coeff 1) (Q.coeff 0) hγ hdisc
    have hPn : ∀ n : ℤ, RatPower (γ * Q.eval (n : ℚ)) 2 ↔ IsHit 2 (A * n ^ 2 + B * n + C) := by
      intro n; rw [monic_quadratic_eval hmon hdeg, hPA n]
    have eP : {n : ℕ | 1 ≤ n ∧ P γ n} =
        {n : ℕ | 1 ≤ n ∧ IsHit 2 (A * (n : ℤ) ^ 2 + B * n + C)} := by
      ext n; simp only [Set.mem_setOf_eq, hPdef]
      rw [show ((n : ℕ) : ℚ) = (((n : ℕ) : ℤ) : ℚ) by push_cast; rfl, hPn]
    rw [eP, branch_infinite_iff hA hD]
    have hs2 : 0 < s ^ 2 := by positivity
    have hApos : 0 < A ↔ 0 < γ := by
      rw [← Int.cast_pos (R := ℚ), hAs]
      constructor
      · intro h; exact (pos_iff_pos_of_mul_pos h).mpr hs2
      · intro h; exact mul_pos h hs2
    have hAsq : IsSquare A ↔ IsSquare γ := by
      rw [← Rat.isSquare_intCast_iff, hAs]
      constructor
      · rintro ⟨y, hy⟩; exact ⟨y / s, by field_simp; linear_combination hy⟩
      · rintro ⟨y, hy⟩; exact ⟨y * s, by rw [hy]; ring⟩
    rw [hApos, hAsq]
    constructor
    · rintro ⟨hg, hns, n, hX, hhit⟩
      refine ⟨hg, hns, n, ?_, (hPn n).mpr hhit⟩
      have : ((2 * A * n + B : ℤ) : ℚ) = γ * s ^ 2 * (2 * n + Q.coeff 1) := by
        push_cast; rw [hAs, hBs]; ring
      have h0 : (0 : ℚ) < ((2 * A * n + B : ℤ) : ℚ) := by exact_mod_cast hX
      rw [this] at h0
      exact (pos_iff_pos_of_mul_pos h0).mp (mul_pos hg hs2)
    · rintro ⟨hg, hns, n, hX, hhit⟩
      refine ⟨hg, hns, n, ?_, (hPn n).mp hhit⟩
      have : ((2 * A * n + B : ℤ) : ℚ) = γ * s ^ 2 * (2 * n + Q.coeff 1) := by
        push_cast; rw [hAs, hBs]; ring
      have h0 : (0 : ℚ) < ((2 * A * n + B : ℤ) : ℚ) := by rw [this]; positivity
      exact_mod_cast h0
  -- a finite union is infinite iff one member is
  have eunion : {n : ℕ | 1 ≤ n ∧ ∃ γ : ℚ, γ ^ e = F.leadingCoeff ∧ P γ n} =
      ⋃ γ ∈ {γ : ℚ | γ ^ e = F.leadingCoeff}, {n : ℕ | 1 ≤ n ∧ P γ n} := by
    ext n; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]; tauto
  rw [eunion]
  constructor
  · intro hinf
    have hex : ∃ γ ∈ {γ : ℚ | γ ^ e = F.leadingCoeff}, {n : ℕ | 1 ≤ n ∧ P γ n}.Infinite := by
      refine Classical.byContradiction fun hno => hinf ?_
      apply hroots_fin.biUnion
      intro γ hγ
      exact Set.not_infinite.mp fun h => hno ⟨γ, hγ, h⟩
    obtain ⟨γ, hγ, hγinf⟩ := hex
    exact ⟨γ, hγ, (hbranch γ hγ).mp hγinf⟩
  · rintro ⟨γ, hγe, hrest⟩
    exact ((hbranch γ hγe).mpr hrest).mono (Set.subset_biUnion_of_mem (u := fun γ =>
      {n : ℕ | 1 ≤ n ∧ P γ n}) hγe)

end PerfectPower.RationalYun
