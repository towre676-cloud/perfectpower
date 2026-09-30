import PerfectPower.Reduction
import PerfectPower.Continuation.PellPositive

/-!
# Filtered Pell orbits: when does a divisibility filter leave infinitely many solutions?

A Pell family `m^2 = A n^2 + B n + C` (`A > 0` not a square) becomes, through `X = 2An + B` and
`Y = |m|`, the quadrant solutions of `X^2 - 4A Y^2 = Δ`, which are the forward orbits of finitely
many roots under the unit `u + v √(4A)`.  A constraint reduced to this family (for example a
quadratic integer root, `Reduction.quadratic`) keeps only the solutions that pass the way back:
a filter `good (X, Y)`.

Such filters are **stable**: once `Y ≥ T` they depend only on `(X, Y) mod M` (`StableFilter`).
The unit acts on `(ZMod M)^2` as a permutation `σ` (`unitPerm`), so every orbit is purely
periodic modulo `M` with the common period `orderOf σ` (`orbit_period`).  Hence:

* `point_infinite`: **one admissible state suffices.**  A quadrant solution whose residue class
  is admissible gives infinitely many `n`, by moving along its orbit in steps of the period.
* `infinite_iff_state`: the filtered family is infinite **iff** some quadrant solution has an
  admissible residue class, **iff** some root orbit meets an admissible state within one
  period (`infinite_iff_root_state`) — a finite search over the roots and `orderOf σ` states.
* `finite_bound`: if no residue class `s` with `s.1^2 - 4A s.2^2 = Δ` in `ZMod M` is admissible,
  every solution has `Y < T`, so `(2An + B)^2 < Δ + 4A T^2`: a complete finite search.

Instance (`quadRoot_infinite_iff`, `quadRoot_bound`): `a y^2 + b y + c = A₀ n^2 + B₀ n + C₀`
with `y ∈ ℤ` or `y ≥ L`.  The reduction `m = 2ay + b` gives `m^2 = A n^2 + B n + C` with
`A = 4aA₀`, `B = 4aB₀`, `C = 4aC₀ + b^2 - 4ac`; the filter is `2A ∣ X - B` (integral `n`) and
`2a ∣ s Y - b` for a sign `s` (integral `y`), and, for `y ≥ L`, the sign `s = sign a` once
`Y ≥ |b| + 2|a|(|L| + 1)` (the domain condition is eventually a sign condition).
-/

namespace PerfectPower.FilteredPell

open PerfectPower PellExact RationalYun

/-- Residues of a pair. -/
def castPair (M : ℕ) (p : ℤ × ℤ) : ZMod M × ZMod M := ((p.1 : ZMod M), (p.2 : ZMod M))

/-- A filter on quadrant points that depends only on residues modulo `M` once `Y ≥ T`. -/
structure StableFilter (M : ℕ) where
  /-- The admissibility of a reduced solution `(X, Y)`. -/
  good : ℤ × ℤ → Prop
  /-- Its residue form. -/
  goodMod : ZMod M × ZMod M → Prop
  /-- The threshold beyond which `good` is a residue condition. -/
  T : ℤ
  stable : ∀ p : ℤ × ℤ, T ≤ p.2 → (good p ↔ goodMod (castPair M p))

variable {D u v Δ : ℤ}

/-- **Pure periodicity with a common period**: `orderOf σ` for the unit permutation `σ`. -/
theorem orbit_period (M : ℕ) (hu : u ^ 2 - D * v ^ 2 = 1) (p : ℤ × ℤ) (j k : ℕ) :
    castPair M (unitOrbit D u v p (j + k * orderOf (unitPerm M D u v hu))) =
      castPair M (unitOrbit D u v p j) := by
  have h1 := cast_unitOrbit M hu p (j + k * orderOf (unitPerm M D u v hu))
  have h2 := cast_unitOrbit M hu p j
  simp only [castPair] at *
  rw [h1, h2, pow_add, pow_mul', pow_orderOf_eq_one, one_pow, mul_one]

lemma orderOf_pos' (M : ℕ) [NeZero M] (hu : u ^ 2 - D * v ^ 2 = 1) :
    0 < orderOf (unitPerm M D u v hu) :=
  orderOf_pos _

/-- A quadrant solution with large `X` has `Y ≥ T`. -/
lemma snd_ge_of_fst {T : ℤ} (hD : 0 ≤ D) {p : ℤ × ℤ} (hp : Sol D Δ p)
    (hX : |Δ| + D * T ^ 2 + 1 ≤ p.1) : T ≤ p.2 := by
  obtain ⟨h1, h2, h3⟩ := hp
  by_contra hlt
  push_neg at hlt
  have hY2 : p.2 ^ 2 ≤ T ^ 2 := by nlinarith
  have hDY : D * p.2 ^ 2 ≤ D * T ^ 2 := mul_le_mul_of_nonneg_left hY2 hD
  have hΔ := le_abs_self Δ
  nlinarith

variable {A B C : ℤ}

/-- The filtered reduced family: `n ≥ 1` with `X = 2An + B`, a quadrant solution `(X, Y)` of
`X^2 - 4A Y^2 = B^2 - 4AC`, admissible. -/
def Hits (A B C : ℤ) {M : ℕ} (F : StableFilter M) : Set ℕ :=
  {n | 1 ≤ n ∧ ∃ Y : ℤ, Sol (4 * A) (B ^ 2 - 4 * A * C) (2 * A * n + B, Y) ∧
    F.good (2 * A * n + B, Y)}

/-- **One admissible state suffices.** -/
theorem point_infinite {M : ℕ} [NeZero M] (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) (F : StableFilter M)
    (hdiv : ∀ p, F.good p → 2 * A ∣ p.1 - B)
    {p₀ : ℤ × ℤ} (hp₀ : Sol (4 * A) (B ^ 2 - 4 * A * C) p₀)
    (hg : F.goodMod (castPair M p₀)) : (Hits A B C F).Infinite := by
  set Q := orderOf (unitPerm M (4 * A) u v hu)
  have hQ : 0 < Q := orderOf_pos' M hu
  intro hfin
  obtain ⟨Tn, hTn⟩ := hfin.bddAbove
  set big : ℤ := |B ^ 2 - 4 * A * C| + 4 * A * F.T ^ 2 + 1 + 2 * A * (Tn + 1) + |B|
  have hbig0 : 0 ≤ big := by positivity
  have hbigdef : big = |B ^ 2 - 4 * A * C| + 4 * A * F.T ^ 2 + 1 + 2 * A * (Tn + 1) + |B| := rfl
  have hB0 := abs_nonneg B
  have hΔ0 := abs_nonneg (B ^ 2 - 4 * A * C)
  have hT0 : 0 ≤ 4 * A * F.T ^ 2 := by positivity
  have hTn0 : 0 ≤ 2 * A * ((Tn : ℤ) + 1) := by positivity
  set k := big.toNat
  set q := unitOrbit (4 * A) u v p₀ (0 + k * Q)
  have hq : Sol (4 * A) (B ^ 2 - 4 * A * C) q :=
    orbit_sol (by omega) hu hu1.le hv.le hp₀ _
  have hmono := orbit_mono (by omega) hu hu1 hv.le hp₀ (0 + k * Q)
  have hk : (k : ℤ) = big := Int.toNat_of_nonneg hbig0
  have hkQ : (k : ℤ) ≤ ((0 + k * Q : ℕ) : ℤ) := by
    push_cast; nlinarith [(by exact_mod_cast hQ : (1 : ℤ) ≤ Q), (by positivity : (0 : ℤ) ≤ k)]
  have hqX : big ≤ q.1 := by have := hp₀.1; linarith
  have hqY : F.T ≤ q.2 := snd_ge_of_fst (by omega) hq (by linarith)
  have hgood : F.good q := by
    rw [F.stable q hqY]
    have := orbit_period (D := 4 * A) M hu p₀ 0 k
    simp only [zero_add] at this
    simpa [q] using this ▸ hg
  obtain ⟨w, hw⟩ := hdiv q hgood
  have hw' : q.1 = 2 * A * w + B := by linarith
  have hwbig : (Tn : ℤ) + 1 < w := by
    have h1 : 0 < 2 * A * (w - (Tn + 1)) := by nlinarith [le_abs_self B]
    by_contra hle
    push_neg at hle
    have := mul_le_mul_of_nonneg_left (show w - (Tn + 1) ≤ 0 by linarith)
      (show (0 : ℤ) ≤ 2 * A by omega)
    linarith
  have hwn : ((w.toNat : ℕ) : ℤ) = w := Int.toNat_of_nonneg (by omega)
  have hmem : w.toNat ∈ Hits A B C F := by
    refine ⟨by omega, q.2, ?_, ?_⟩
    · rw [hwn, ← hw']; exact hq
    · rw [hwn, ← hw']; exact hgood
  have := hTn hmem
  omega

/-- Infinitely many `n` give a solution in an admissible residue class. -/
theorem state_of_infinite {M : ℕ} (hA : 0 < A) (F : StableFilter M)
    (hinf : (Hits A B C F).Infinite) :
    ∃ p, Sol (4 * A) (B ^ 2 - 4 * A * C) p ∧ F.goodMod (castPair M p) := by
  set big : ℤ := |B ^ 2 - 4 * A * C| + 4 * A * F.T ^ 2 + 1 + |B|
  obtain ⟨n, ⟨hn1, Y, hsol, hgood⟩, hnbig⟩ := hinf.exists_gt big.toNat
  have hbig0 : 0 ≤ big := by positivity
  have hbigdef : big = |B ^ 2 - 4 * A * C| + 4 * A * F.T ^ 2 + 1 + |B| := rfl
  have hnb : big < n := by
    have := Int.toNat_of_nonneg hbig0; omega
  have hX : |B ^ 2 - 4 * A * C| + 4 * A * F.T ^ 2 + 1 ≤ 2 * A * n + B := by
    have hB := neg_abs_le B
    have : (n : ℤ) ≤ 2 * A * n := by nlinarith
    linarith
  have hY := snd_ge_of_fst (by omega) hsol hX
  exact ⟨_, hsol, (F.stable _ hY).mp hgood⟩

/-- **The criterion.**  The filtered family is infinite iff some quadrant solution lies in an
admissible residue class. -/
theorem infinite_iff_state {M : ℕ} [NeZero M] (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) (F : StableFilter M)
    (hdiv : ∀ p, F.good p → 2 * A ∣ p.1 - B) :
    (Hits A B C F).Infinite ↔
      ∃ p, Sol (4 * A) (B ^ 2 - 4 * A * C) p ∧ F.goodMod (castPair M p) :=
  ⟨state_of_infinite hA F, fun ⟨_, hp, hg⟩ => point_infinite hA hu1 hv hu F hdiv hp hg⟩

/-- **The finite search**: the criterion over the roots and one period. -/
theorem infinite_iff_root_state {M : ℕ} [NeZero M] (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) (F : StableFilter M)
    (hdiv : ∀ p, F.good p → 2 * A ∣ p.1 - B) :
    (Hits A B C F).Infinite ↔
      ∃ ρ, IsRoot (4 * A) u v (B ^ 2 - 4 * A * C) ρ ∧
        ∃ j < orderOf (unitPerm M (4 * A) u v hu),
          F.goodMod (castPair M (unitOrbit (4 * A) u v ρ j)) := by
  rw [infinite_iff_state hA hu1 hv hu F hdiv]
  constructor
  · rintro ⟨p, hp, hg⟩
    obtain ⟨ρ, j, hρ, hj⟩ := exists_root (by omega) hu1 hv hu p.1 p rfl hp
    set Q := orderOf (unitPerm M (4 * A) u v hu)
    have hQ : 0 < Q := orderOf_pos' M hu
    refine ⟨ρ, hρ, j % Q, Nat.mod_lt _ hQ, ?_⟩
    have := orbit_period (D := 4 * A) M hu ρ (j % Q) (j / Q)
    rw [show j % Q + j / Q * Q = j by rw [mul_comm]; exact Nat.mod_add_div j Q, hj] at this
    rw [← this]; exact hg
  · rintro ⟨ρ, hρ, j, -, hg⟩
    exact ⟨_, orbit_sol (by omega) hu hu1.le hv.le hρ.1 j, hg⟩

/-- **The finite case, with a complete search range.**  If no admissible residue class solves
the norm equation modulo `M`, every filtered solution has `Y < T`, so `(2An + B)^2 <
Δ + 4A T^2`. -/
theorem finite_bound {M : ℕ} (hA : 0 < A) (F : StableFilter M)
    (hno : ∀ s : ZMod M × ZMod M,
      s.1 ^ 2 - ((4 * A : ℤ) : ZMod M) * s.2 ^ 2 = ((B ^ 2 - 4 * A * C : ℤ) : ZMod M) →
        ¬ F.goodMod s) :
    ∀ n ∈ Hits A B C F, (2 * A * n + B) ^ 2 < B ^ 2 - 4 * A * C + 4 * A * F.T ^ 2 := by
  rintro n ⟨-, Y, hsol, hgood⟩
  have hY : Y < F.T := by
    by_contra h
    push_neg at h
    apply hno (castPair M (2 * A * n + B, Y)) _ ((F.stable _ h).mp hgood)
    have := congrArg (Int.cast : ℤ → ZMod M) hsol.2.2
    push_cast at this ⊢
    simpa [castPair] using this
  have hY0 := hsol.2.1
  have h2 : Y ^ 2 < F.T ^ 2 := by nlinarith
  have := hsol.2.2
  simp only at this
  nlinarith

/-! ### The quadratic-root constraint -/

/-- Divisibility read in a quotient: for `d ∣ M`, `d ∣ z` iff the image of `z` in `ZMod d` is
zero. -/
def dvdMod {M : ℕ} (d : ℕ) (h : d ∣ M) (z : ZMod M) : Prop := ZMod.castHom h (ZMod d) z = 0

instance {M : ℕ} (d : ℕ) (h : d ∣ M) : DecidablePred (dvdMod d h) :=
  fun z => inferInstanceAs (Decidable (ZMod.castHom h (ZMod d) z = 0))

lemma dvdMod_iff {M : ℕ} {d : ℕ} (h : d ∣ M) (z : ℤ) : dvdMod d h (z : ZMod M) ↔ (d : ℤ) ∣ z := by
  simp only [dvdMod, map_intCast]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd z d

/-- The admissible signs of the root `m = ± Y`: both for `y ∈ ℤ`, only `sign a` for `y ≥ L`. -/
def signs (a : ℤ) : Option ℤ → Finset ℤ
  | none => {1, -1}
  | some _ => {if 0 < a then 1 else -1}

/-- The domain of `y`. -/
def Dom : Option ℤ → ℤ → Prop
  | none, _ => True
  | some L, y => L ≤ y

/-- The threshold after which the domain is a sign condition. -/
def thr (a b : ℤ) : Option ℤ → ℤ
  | none => 0
  | some L => |b| + 2 * |a| * (|L| + 1) + 1

/-- For `Y` past the threshold, the root `y = (sY - b)/(2a)` lies in the domain iff the sign is
admissible. -/
lemma dom_iff_sign {a b : ℤ} (ha : a ≠ 0) (L : Option ℤ) {Y s : ℤ} (hs : s = 1 ∨ s = -1)
    (hY : thr a b L ≤ Y) (hdvd : 2 * a ∣ s * Y - b) :
    Dom L ((s * Y - b) / (2 * a)) ↔ s ∈ signs a L := by
  cases L with
  | none => simp only [Dom, signs, Finset.mem_insert, Finset.mem_singleton]; tauto
  | some L =>
    obtain ⟨k, hk⟩ := hdvd
    have hq : (s * Y - b) / (2 * a) = k := by rw [hk]; exact Int.mul_ediv_cancel_left _ (by positivity)
    rw [hq]
    simp only [Dom, signs, Finset.mem_singleton, thr] at hY ⊢
    have hLle := neg_abs_le L
    have hLle' := le_abs_self L
    have hbb := neg_abs_le b
    have hbb' := le_abs_self b
    have ha' : 0 < |a| := abs_pos.mpr ha
    rcases lt_or_gt_of_ne ha with han | hap
    · rw [if_neg (by omega), abs_of_neg han] at *
      rcases hs with rfl | rfl
      · -- s = 1: 2ak = Y - b > 0 with a < 0, so k < 0 and |k| is large
        constructor
        · intro h; exfalso
          nlinarith
        · intro h; omega
      · constructor
        · intro _; rfl
        · intro _
          nlinarith
    · rw [if_pos hap, abs_of_pos hap] at *
      rcases hs with rfl | rfl
      · constructor
        · intro _; rfl
        · intro _
          nlinarith
      · constructor
        · intro h; exfalso
          nlinarith
        · intro h; omega

/-- The filter of the quadratic-root constraint, with `A = 4aA₀`, `B = 4aB₀`. -/
def quadFilter (a b A B : ℤ) (L : Option ℤ) (ha : a ≠ 0) :
    StableFilter (4 * A * a).natAbs where
  good p := 2 * A ∣ p.1 - B ∧ ∃ s ∈ ({1, -1} : Finset ℤ), 2 * a ∣ s * p.2 - b ∧
    Dom L ((s * p.2 - b) / (2 * a))
  goodMod q := dvdMod (2 * A).natAbs (by
      exact Int.natAbs_dvd_natAbs.mpr ⟨2 * a, by ring⟩)
      (q.1 - (B : ZMod (4 * A * a).natAbs)) ∧
    ∃ s ∈ signs a L, dvdMod (2 * a).natAbs (by
      exact Int.natAbs_dvd_natAbs.mpr ⟨2 * A, by ring⟩)
      ((s : ZMod (4 * A * a).natAbs) * q.2 - (b : ZMod (4 * A * a).natAbs))
  T := thr a b L
  stable p hp := by
    have e1 : ∀ z : ℤ, (((2 * A).natAbs : ℕ) : ℤ) ∣ z ↔ 2 * A ∣ z := fun z => Int.natAbs_dvd
    have e2 : ∀ z : ℤ, (((2 * a).natAbs : ℕ) : ℤ) ∣ z ↔ 2 * a ∣ z := fun z => Int.natAbs_dvd
    simp only [castPair]
    rw [show ((p.1 : ZMod (4 * A * a).natAbs) - (B : ZMod (4 * A * a).natAbs)) =
      ((p.1 - B : ℤ) : ZMod (4 * A * a).natAbs) by push_cast; ring, dvdMod_iff, e1]
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨s, hs, hd, hdom⟩
      have hs' : s = 1 ∨ s = -1 := by simpa using hs
      refine ⟨s, (dom_iff_sign ha L hs' hp hd).mp hdom, ?_⟩
      rw [show (s : ZMod (4 * A * a).natAbs) * (p.2 : ZMod _) - (b : ZMod _) =
        ((s * p.2 - b : ℤ) : ZMod (4 * A * a).natAbs) by push_cast; ring, dvdMod_iff, e2]
      exact hd
    · rintro ⟨s, hs, hd⟩
      rw [show (s : ZMod (4 * A * a).natAbs) * (p.2 : ZMod _) - (b : ZMod _) =
        ((s * p.2 - b : ℤ) : ZMod (4 * A * a).natAbs) by push_cast; ring, dvdMod_iff, e2] at hd
      have hs' : s = 1 ∨ s = -1 := by
        cases L <;> simp only [signs, Finset.mem_insert, Finset.mem_singleton] at hs <;>
          [exact hs; (split_ifs at hs <;> simp [hs])]
      refine ⟨s, by rcases hs' with rfl | rfl <;> simp, hd, ?_⟩
      exact (dom_iff_sign ha L hs' hp hd).mpr hs

/-- The original constraint `a y^2 + b y + c = A₀ n^2 + B₀ n + C₀`, `y` in its domain. -/
def QuadHits (a b c A₀ B₀ C₀ : ℤ) (L : Option ℤ) : Set ℕ :=
  {n | 1 ≤ n ∧ ∃ y, Dom L y ∧ a * y ^ 2 + b * y + c = A₀ * n ^ 2 + B₀ * n + C₀}

/-- Past the vertex, the original constraint **is** the filtered family: the forward map is
`m = 2ay + b`, `Y = |m|`, and the way back is the filter. -/
lemma quadHits_iff {a b c A₀ B₀ C₀ : ℤ} (L : Option ℤ) (ha : a ≠ 0) (hA : 0 < 4 * a * A₀)
    (n : ℕ) (hX : 0 < 2 * (4 * a * A₀) * n + 4 * a * B₀) :
    n ∈ QuadHits a b c A₀ B₀ C₀ L ↔
      n ∈ Hits (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c)
        (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha) := by
  set A := 4 * a * A₀
  set B := 4 * a * B₀
  have hnorm : ∀ m : ℤ, m ^ 2 = A * n ^ 2 + B * n + (4 * a * C₀ + b ^ 2 - 4 * a * c) →
      (2 * A * n + B) ^ 2 - 4 * A * m ^ 2 = B ^ 2 - 4 * A * (4 * a * C₀ + b ^ 2 - 4 * a * c) := by
    intro m hm; rw [hm]; ring
  constructor
  · rintro ⟨hn, y, hdom, hy⟩
    set m := 2 * a * y + b
    have hm : m ^ 2 = A * n ^ 2 + B * n + (4 * a * C₀ + b ^ 2 - 4 * a * c) := by
      simp only [m, A, B]; linear_combination (4 * a) * hy
    refine ⟨hn, |m|, ⟨hX, abs_nonneg m, by rw [sq_abs]; exact hnorm m hm⟩, ⟨n, by ring⟩, ?_⟩
    have hs : ∃ s ∈ ({1, -1} : Finset ℤ), s * |m| = m := by
      rcases abs_choice m with h | h
      · exact ⟨1, by simp, by rw [h, one_mul]⟩
      · exact ⟨-1, by simp, by rw [h]; ring⟩
    obtain ⟨s, hs, hsm⟩ := hs
    refine ⟨s, hs, ⟨y, by rw [hsm]; ring⟩, ?_⟩
    rw [hsm, show m - b = 2 * a * y by ring, Int.mul_ediv_cancel_left _ (by positivity)]
    exact hdom
  · rintro ⟨hn, Y, hsol, -, s, hs, ⟨k, hk⟩, hdom⟩
    refine ⟨hn, k, ?_, ?_⟩
    · rwa [hk, Int.mul_ediv_cancel_left _ (by positivity)] at hdom
    · have hN := hsol.2.2
      have hs2 : s ^ 2 = 1 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl <;> norm_num
      have hm : (s * Y) ^ 2 = A * n ^ 2 + B * n + (4 * a * C₀ + b ^ 2 - 4 * a * c) := by
        have : (s * Y) ^ 2 = Y ^ 2 := by rw [mul_pow, hs2, one_mul]
        rw [this]
        have key : 4 * A * (Y ^ 2 - (A * n ^ 2 + B * n + (4 * a * C₀ + b ^ 2 - 4 * a * c))) = 0 := by
          simp only [A] at hN ⊢; linear_combination (-1 : ℤ) * hN
        rcases mul_eq_zero.mp key with h | h
        · exact absurd h (by positivity)
        · linarith
      rw [show s * Y = 2 * a * k + b by linarith] at hm
      have : 4 * a * (a * k ^ 2 + b * k + c - (A₀ * n ^ 2 + B₀ * n + C₀)) = 0 := by
        simp only [A, B] at hm; linear_combination hm
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · linarith

/-- The two sets differ only below the vertex. -/
lemma quadHits_infinite_iff {a b c A₀ B₀ C₀ : ℤ} (L : Option ℤ) (ha : a ≠ 0)
    (hA : 0 < 4 * a * A₀) :
    (QuadHits a b c A₀ B₀ C₀ L).Infinite ↔
      (Hits (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c)
        (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha)).Infinite := by
  set K := (4 * a * B₀).natAbs
  have hbig : ∀ n : ℕ, K < n → 0 < 2 * (4 * a * A₀) * n + 4 * a * B₀ := by
    intro n hn
    have hK : -(K : ℤ) ≤ 4 * a * B₀ := by rw [Int.natCast_natAbs]; exact neg_abs_le _
    nlinarith
  have e : QuadHits a b c A₀ B₀ C₀ L \ Set.Iic K = Hits (4 * a * A₀) (4 * a * B₀)
      (4 * a * C₀ + b ^ 2 - 4 * a * c) (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha) \
        Set.Iic K := by
    ext n
    simp only [Set.mem_diff, Set.mem_Iic, not_le]
    constructor
    · rintro ⟨h, hn⟩; exact ⟨(quadHits_iff L ha hA n (hbig n hn)).mp h, hn⟩
    · rintro ⟨h, hn⟩; exact ⟨(quadHits_iff L ha hA n (hbig n hn)).mpr h, hn⟩
  constructor
  · intro h
    have := h.diff (Set.finite_Iic K)
    rw [e] at this
    exact this.mono Set.diff_subset
  · intro h
    have := h.diff (Set.finite_Iic K)
    rw [← e] at this
    exact this.mono Set.diff_subset

/-- **The quadratic-root constraint, decided.**  `a y^2 + b y + c = A₀ n^2 + B₀ n + C₀` (with
`A = 4aA₀ > 0`, a unit `(u, v)` of `X^2 - 4A Y^2 = 1`, `y ∈ ℤ` or `y ≥ L`) has infinitely many
`n` iff some quadrant solution of `X^2 - 4A Y^2 = B^2 - 4AC` lies in an admissible residue class
modulo `|4Aa|`. -/
theorem quadRoot_infinite_iff {a b c A₀ B₀ C₀ u v : ℤ} (L : Option ℤ) (ha : a ≠ 0)
    (hA : 0 < 4 * a * A₀) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * (4 * a * A₀) * v ^ 2 = 1) :
    (QuadHits a b c A₀ B₀ C₀ L).Infinite ↔
      ∃ p, Sol (4 * (4 * a * A₀)) ((4 * a * B₀) ^ 2 - 4 * (4 * a * A₀) *
          (4 * a * C₀ + b ^ 2 - 4 * a * c)) p ∧
        (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha).goodMod
          (castPair (4 * (4 * a * A₀) * a).natAbs p) := by
  haveI : NeZero (4 * (4 * a * A₀) * a).natAbs := ⟨by
    rw [Int.natAbs_ne_zero]; exact mul_ne_zero (by positivity) ha⟩
  rw [quadHits_infinite_iff L ha hA]
  exact infinite_iff_state hA hu1 hv hu _ (fun p hp => hp.1)

/-- **The quadratic-root constraint, finite case.**  If no admissible residue class solves the
norm equation modulo `|4Aa|`, every solution past the vertex has
`(2An + B)^2 < Δ + 4A·thr^2`. -/
theorem quadRoot_bound {a b c A₀ B₀ C₀ : ℤ} (L : Option ℤ) (ha : a ≠ 0) (hA : 0 < 4 * a * A₀)
    (hno : ∀ s : ZMod (4 * (4 * a * A₀) * a).natAbs × ZMod (4 * (4 * a * A₀) * a).natAbs,
      s.1 ^ 2 - ((4 * (4 * a * A₀) : ℤ) : ZMod _) * s.2 ^ 2 =
        (((4 * a * B₀) ^ 2 - 4 * (4 * a * A₀) * (4 * a * C₀ + b ^ 2 - 4 * a * c) : ℤ) : ZMod _) →
      ¬ (quadFilter a b (4 * a * A₀) (4 * a * B₀) L ha).goodMod s)
    (n : ℕ) (hn : n ∈ QuadHits a b c A₀ B₀ C₀ L)
    (hX : 0 < 2 * (4 * a * A₀) * n + 4 * a * B₀) :
    (2 * (4 * a * A₀) * n + 4 * a * B₀) ^ 2 <
      (4 * a * B₀) ^ 2 - 4 * (4 * a * A₀) * (4 * a * C₀ + b ^ 2 - 4 * a * c) +
        4 * (4 * a * A₀) * thr a b L ^ 2 :=
  finite_bound hA _ hno n ((quadHits_iff L ha hA n hX).mp hn)

/-! ### Kernel-checked certificates -/

/-- The unit step on residues. -/
def stepMod (M : ℕ) (D u v : ℤ) (s : ZMod M × ZMod M) : ZMod M × ZMod M :=
  (s.1 * u + D * s.2 * v, s.1 * v + s.2 * u)

lemma castPair_orbit (M : ℕ) (D u v : ℤ) (p : ℤ × ℤ) :
    ∀ j, castPair M (unitOrbit D u v p j) = (stepMod M D u v)^[j] (castPair M p)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', ← castPair_orbit M D u v p j, orbit_succ]
    simp [castPair, stepMod, unitAct]

/-- The unit step on integer residues (what the kernel evaluates). -/
def stepInt (M D u v : ℤ) (s : ℤ × ℤ) : ℤ × ℤ :=
  ((s.1 * u + D * s.2 * v) % M, (s.1 * v + s.2 * u) % M)

lemma castPair_mod (M : ℕ) (p : ℤ × ℤ) :
    castPair M (p.1 % (M : ℤ), p.2 % (M : ℤ)) = castPair M p := by
  simp [castPair, ZMod.intCast_mod]

lemma castPair_stepInt_iter (M : ℕ) (D u v : ℤ) (s : ℤ × ℤ) :
    ∀ j, castPair M ((stepInt M D u v)^[j] s) = (stepMod M D u v)^[j] (castPair M s)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← castPair_stepInt_iter M D u v s j]
    set t := (stepInt M D u v)^[j] s
    simp only [stepInt]
    rw [castPair_mod M (t.1 * u + D * t.2 * v, t.1 * v + t.2 * u)]
    simp [castPair, stepMod]

/-- A finiteness certificate: a bound `Ymax` on the `Y` of roots, the integer square roots
`⌊√(Δ + 4A Y^2)⌋` for `Y ≤ Ymax`, the quadrant solutions with `Y ≤ Ymax` (which include the
roots), and for each of these the length of its cycle modulo `M`. -/
structure FinCert where
  /-- Every root has `Y ≤ Ymax`. -/
  Ymax : ℕ
  /-- `isqrts[Y] = ⌊√(Δ + 4A Y^2)⌋` (checked, not trusted). -/
  isqrts : List ℤ
  /-- The quadrant solutions `(X, Y)` with `Y ≤ Ymax`, with their cycle lengths. -/
  roots : List ((ℤ × ℤ) × ℕ)

/-- The check, on integers only: the box `4A (Ymax+1)^2 > |Δ| u^2` contains every root
(`root_in_box`); for each `Y ≤ Ymax` the supplied `q` is the integer square root of
`t = Δ + 4A Y^2` (or `t ≤ 0`), and if `q^2 = t` then `(q, Y)` is listed; and each listed cycle
modulo `M` returns to its start without meeting a state accepted by `goodB`. -/
def FinCert.check (M : ℕ) (goodB : ℤ × ℤ → Bool) (A B C u v : ℤ) (c : FinCert) : Bool :=
  decide (|B ^ 2 - 4 * A * C| * u ^ 2 < 4 * A * ((c.Ymax : ℤ) + 1) ^ 2) &&
  (List.range (c.Ymax + 1)).all (fun Y =>
    let t := B ^ 2 - 4 * A * C + 4 * A * (Y : ℤ) ^ 2
    let q := c.isqrts.getD Y 0
    decide (t ≤ 0) ||
      (decide (0 ≤ q ∧ q * q ≤ t ∧ t < (q + 1) * (q + 1)) &&
        (!decide (q * q = t) || c.roots.any (fun r => decide (r.1 = (q, (Y : ℤ))))))) &&
  c.roots.all (fun r =>
    decide (0 < r.2) &&
    decide ((stepInt M (4 * A) u v)^[r.2] (r.1.1 % M, r.1.2 % M) = (r.1.1 % M, r.1.2 % M)) &&
    (List.range r.2).all (fun j => !goodB ((stepInt M (4 * A) u v)^[j] (r.1.1 % M, r.1.2 % M))))

/-- **Soundness of the finiteness certificate**: if `goodB` accepts every state whose residues
are admissible, every filtered solution has `Y < T`, hence `(2An + B)^2 < Δ + 4A T^2`. -/
theorem FinCert.sound {M : ℕ} (hA : 0 < A) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * A * v ^ 2 = 1) (F : StableFilter M) (goodB : ℤ × ℤ → Bool)
    (hgoodB : ∀ p, F.goodMod (castPair M p) → goodB p = true)
    (c : FinCert) (hc : c.check M goodB A B C u v = true) :
    ∀ n ∈ Hits A B C F, (2 * A * n + B) ^ 2 < B ^ 2 - 4 * A * C + 4 * A * F.T ^ 2 := by
  simp only [FinCert.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.any_eq_true] at hc
  obtain ⟨⟨hbox, hlist⟩, hcyc⟩ := hc
  rintro n ⟨-, Y, hsol, hgood⟩
  have hY : Y < F.T := by
    by_contra h
    push_neg at h
    have hg := (F.stable _ h).mp hgood
    obtain ⟨ρ, j, hρ, hj⟩ := exists_root (by omega) hu1 hv hu _ _ rfl hsol
    have hρbox := root_in_box (by omega) hu1 hv hu hρ
    obtain ⟨hρX, hρY, hρN⟩ := hρ.1
    have hρY' : ρ.2 < (c.Ymax : ℤ) + 1 := by
      by_contra h'
      push_neg at h'
      have : 4 * A * ((c.Ymax : ℤ) + 1) ^ 2 ≤ 4 * A * ρ.2 ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by omega)
        exact pow_le_pow_left₀ (by positivity) h' 2
      linarith [le_abs_self (B ^ 2 - 4 * A * C)]
    have hYn : ρ.2.toNat < c.Ymax + 1 := by omega
    have hYc : ((ρ.2.toNat : ℕ) : ℤ) = ρ.2 := Int.toNat_of_nonneg hρY
    have ht : B ^ 2 - 4 * A * C + 4 * A * ((ρ.2.toNat : ℕ) : ℤ) ^ 2 = ρ.1 * ρ.1 := by
      rw [hYc]; linarith
    rcases hlist _ hYn with hneg | ⟨⟨hq0, hq1, hq2⟩, hsq⟩
    · rw [ht] at hneg; nlinarith
    rw [ht] at hq1 hq2 hsq
    set q := c.isqrts.getD ρ.2.toNat 0
    have hqX : q = ρ.1 := by
      have h1 : q ≤ ρ.1 := by nlinarith
      have h2 : ρ.1 < q + 1 := by nlinarith
      omega
    rcases hsq with hnot | ⟨r, hr, hre⟩
    · exact hnot (by rw [hqX])
    · rw [hqX, hYc] at hre
      have hre' : r.1 = ρ := hre
      obtain ⟨⟨hP, hper⟩, hnone⟩ := hcyc r hr
      set s₀ : ℤ × ℤ := (r.1.1 % M, r.1.2 % M)
      have hiter : (stepInt M (4 * A) u v)^[j] s₀ = (stepInt M (4 * A) u v)^[j % r.2] s₀ := by
        conv_lhs => rw [← Nat.mod_add_div j r.2]
        rw [Function.iterate_add_apply]
        congr 1
        induction j / r.2 with
        | zero => rfl
        | succ k ih => rw [Nat.mul_succ, Function.iterate_add_apply, hper, ih]
      have hstate : castPair M (unitOrbit (4 * A) u v ρ j) =
          castPair M ((stepInt M (4 * A) u v)^[j % r.2] s₀) := by
        rw [← hiter, castPair_stepInt_iter, castPair_orbit, castPair_mod, hre']
      rw [hj] at hstate
      have := hgoodB _ (hstate ▸ hg)
      rw [hnone _ (Nat.mod_lt _ hP)] at this
      exact absurd this (by decide)
  have hY0 := hsol.2.1
  have h2 : Y ^ 2 < F.T ^ 2 := by nlinarith
  have := hsol.2.2
  simp only at this
  nlinarith

/-- The admissible signs as a list. -/
def signsList (a : ℤ) : Option ℤ → List ℤ
  | none => [1, -1]
  | some _ => [if 0 < a then 1 else -1]

lemma mem_signsList (a : ℤ) (L : Option ℤ) (s : ℤ) : s ∈ signsList a L ↔ s ∈ signs a L := by
  cases L <;> simp [signsList, signs]

/-- The integer form of the quadratic-root filter. -/
def quadGoodB (a b A B : ℤ) (L : Option ℤ) (q : ℤ × ℤ) : Bool :=
  decide ((q.1 - B) % (2 * A) = 0) &&
    (signsList a L).any (fun s => decide ((s * q.2 - b) % (2 * a) = 0))

lemma quadGoodB_iff {a b A B : ℤ} (L : Option ℤ) (ha : a ≠ 0) (p : ℤ × ℤ) :
    (quadFilter a b A B L ha).goodMod (castPair (4 * A * a).natAbs p) ↔
      quadGoodB a b A B L p = true := by
  simp only [quadFilter, quadGoodB, castPair, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true]
  rw [show ((p.1 : ZMod (4 * A * a).natAbs) - (B : ZMod (4 * A * a).natAbs)) =
      ((p.1 - B : ℤ) : ZMod (4 * A * a).natAbs) by push_cast; ring, dvdMod_iff,
    Int.natAbs_dvd, ← Int.dvd_iff_emod_eq_zero]
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨s, hs, hd⟩
    refine ⟨s, (mem_signsList a L s).mpr hs, ?_⟩
    rw [show (s : ZMod (4 * A * a).natAbs) * (p.2 : ZMod _) - (b : ZMod _) =
      ((s * p.2 - b : ℤ) : ZMod (4 * A * a).natAbs) by push_cast; ring, dvdMod_iff,
      Int.natAbs_dvd] at hd
    exact Int.emod_eq_zero_of_dvd hd
  · rintro ⟨s, hs, hd⟩
    refine ⟨s, (mem_signsList a L s).mp hs, ?_⟩
    rw [show (s : ZMod (4 * A * a).natAbs) * (p.2 : ZMod _) - (b : ZMod _) =
      ((s * p.2 - b : ℤ) : ZMod (4 * A * a).natAbs) by push_cast; ring, dvdMod_iff,
      Int.natAbs_dvd]
    exact Int.dvd_of_emod_eq_zero hd

/-- A finiteness certificate for the quadratic-root constraint: past the vertex, every solution
satisfies `(2An + B)^2 < Δ + 4A·thr^2`. -/
theorem quadRoot_bound_of_cert {a b c A₀ B₀ C₀ u v : ℤ} (L : Option ℤ) (ha : a ≠ 0)
    (hA : 0 < 4 * a * A₀) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * (4 * a * A₀) * v ^ 2 = 1) (cert : FinCert)
    (hc : cert.check (4 * (4 * a * A₀) * a).natAbs (quadGoodB a b (4 * a * A₀) (4 * a * B₀) L)
      (4 * a * A₀) (4 * a * B₀) (4 * a * C₀ + b ^ 2 - 4 * a * c) u v = true)
    (n : ℕ) (hn : n ∈ QuadHits a b c A₀ B₀ C₀ L) (hX : 0 < 2 * (4 * a * A₀) * n + 4 * a * B₀) :
    (2 * (4 * a * A₀) * n + 4 * a * B₀) ^ 2 <
      (4 * a * B₀) ^ 2 - 4 * (4 * a * A₀) * (4 * a * C₀ + b ^ 2 - 4 * a * c) +
        4 * (4 * a * A₀) * thr a b L ^ 2 :=
  FinCert.sound hA hu1 hv hu _ _ (fun p hp => (quadGoodB_iff L ha p).mp hp) cert hc n
    ((quadHits_iff L ha hA n hX).mp hn)

/-- An infiniteness certificate for the quadratic-root constraint: one quadrant solution whose
residues pass the integer filter. -/
theorem quadRoot_infinite_of_witness {a b c A₀ B₀ C₀ u v : ℤ} (L : Option ℤ) (ha : a ≠ 0)
    (hA : 0 < 4 * a * A₀) (hu1 : 1 < u) (hv : 0 < v)
    (hu : u ^ 2 - 4 * (4 * a * A₀) * v ^ 2 = 1) (p : ℤ × ℤ)
    (hp : Sol (4 * (4 * a * A₀)) ((4 * a * B₀) ^ 2 - 4 * (4 * a * A₀) *
      (4 * a * C₀ + b ^ 2 - 4 * a * c)) p)
    (hg : quadGoodB a b (4 * a * A₀) (4 * a * B₀) L p = true) :
    (QuadHits a b c A₀ B₀ C₀ L).Infinite := by
  exact (quadRoot_infinite_iff L ha hA hu1 hv hu).mpr ⟨p, hp, (quadGoodB_iff L ha p).mpr hg⟩

end PerfectPower.FilteredPell
