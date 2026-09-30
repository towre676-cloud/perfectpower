import PerfectPower.Transport

/-!
# Exact constraint reductions, and how they compose

A program meets a constraint such as "`y(y+1)/2 = F(n)` for some integer `y`" and wants a complete
answer.  PerfectPower answers constraints of the form `F(n) = m^d`.  The bridge is an **exact
reduction**: a map of solutions forward, and a *partial* map back that is defined exactly on the
admissible reduced solutions (integrality, divisibility, sign and domain conditions).

* `Exact P Q`: `fwd` sends solutions of `P` to solutions of `Q`; `bwd` sends a solution of `Q`,
  when admissible, to a solution of `P`; and `bwd (fwd a) = some a` on solutions.
* `Exact.iff`: `P a ↔ ∃ b, Q b ∧ bwd b = some a`.  So a reduced solution set determines the
  original one, and nothing is lost or invented.
* `Exact.comp`: reductions compose (admissibility conditions compose with `Option.bind`).
* `Exact.pull_complete`: a *complete finite* list `T` of reduced solutions pulls back to a complete
  finite list of original solutions.  Completeness is transported, not re-proved.
* `Exact.exists_iff`, `Exact.count_eq`: for index-preserving reductions on `ℕ × ℤ`, the
  hit counts agree once the admissibility filter is applied.

Instances:

* `affine`: `Q (r n + s, m)` with `n ≥ 1`, pulled back along `t ↦ (t - s) / r` when `r ∣ t - s`
  and the quotient is `≥ 1`.
* `quadratic`: `a y^2 + b y + c = F(n)` with `y` in a decidable domain `Y`, reduced to
  `m^2 = 4a F(n) + b^2 - 4ac` by `m = 2ay + b`.  **Both signs of `m` are kept**, and the way back
  requires `2a ∣ m - b` and `(m - b)/(2a) ∈ Y`: a square discriminant alone is not enough.
* `triangular`: `y (y+1) = 2 F(n)` reduces to `m^2 = 8F(n) + 1`, and here the divisibility is
  automatic (the root is odd), so `triangular_count`: the number of `n ≤ N` with a triangular
  value equals `A (8F + 1) 2 0 N`, for `y ∈ ℤ` and for `y ≥ 0` alike.

Worked example (`tri_cube_complete`): `y(y+1)/2 = 64n^3 - 120n^2 + 75n - 16` with `n ≥ 1` has
exactly the solutions `(n, y) = (1, 2), (1, -3)`.  It is the composite
triangular → affine (`t = 8n - 5`) → `m^2 = t^3 - 2`, closed by `MordellMinus2.points`.
-/

namespace PerfectPower.Reduction

open PerfectPower

/-- An exact reduction of the constraint `P` to the constraint `Q`. -/
structure Exact {α β : Type*} (P : α → Prop) (Q : β → Prop) where
  /-- Solutions forward. -/
  fwd : α → β
  /-- Admissible reduced solutions back (`none` = inadmissible). -/
  bwd : β → Option α
  fwd_sol : ∀ a, P a → Q (fwd a)
  bwd_sol : ∀ b a, Q b → bwd b = some a → P a
  bwd_fwd : ∀ a, P a → bwd (fwd a) = some a

namespace Exact

variable {α β γ : Type*} {P : α → Prop} {Q : β → Prop} {R : γ → Prop}

/-- The original solutions are exactly the admissible images of reduced solutions. -/
theorem iff (e : Exact P Q) (a : α) : P a ↔ ∃ b, Q b ∧ e.bwd b = some a :=
  ⟨fun h => ⟨e.fwd a, e.fwd_sol a h, e.bwd_fwd a h⟩, fun ⟨b, hb, he⟩ => e.bwd_sol b a hb he⟩

/-- The identity reduction. -/
def refl (P : α → Prop) : Exact P P where
  fwd := id
  bwd := some
  fwd_sol _ h := h
  bwd_sol _ _ h he := by cases he; exact h
  bwd_fwd _ _ := rfl

/-- **Composition.**  The admissibility conditions compose. -/
def comp (e : Exact P Q) (f : Exact Q R) : Exact P R where
  fwd := f.fwd ∘ e.fwd
  bwd c := (f.bwd c).bind e.bwd
  fwd_sol a h := f.fwd_sol _ (e.fwd_sol a h)
  bwd_sol c a hc he := by
    obtain ⟨b, hb, hab⟩ := Option.bind_eq_some_iff.mp he
    exact e.bwd_sol b a (f.bwd_sol c b hc hb) hab
  bwd_fwd a h := by
    show (f.bwd (f.fwd (e.fwd a))).bind e.bwd = some a
    rw [f.bwd_fwd _ (e.fwd_sol a h)]
    exact e.bwd_fwd a h

/-- Restating the source constraint. -/
def congr {P' : α → Prop} (e : Exact P Q) (h : ∀ a, P' a ↔ P a) : Exact P' Q where
  fwd := e.fwd
  bwd := e.bwd
  fwd_sol a ha := e.fwd_sol a ((h a).mp ha)
  bwd_sol b a hb he := (h a).mpr (e.bwd_sol b a hb he)
  bwd_fwd a ha := e.bwd_fwd a ((h a).mp ha)

/-- Restating the target constraint. -/
def congrRight {Q' : β → Prop} (e : Exact P Q) (h : ∀ b, Q' b ↔ Q b) : Exact P Q' where
  fwd := e.fwd
  bwd := e.bwd
  fwd_sol a ha := (h _).mpr (e.fwd_sol a ha)
  bwd_sol b a hb he := e.bwd_sol b a ((h b).mp hb) he
  bwd_fwd := e.bwd_fwd

/-- Pull a finite list of reduced solutions back. -/
def pull [DecidableEq α] (e : Exact P Q) (T : Finset β) : Finset α :=
  T.biUnion fun b => (e.bwd b).toFinset

/-- **Completeness is transported**: a complete list of reduced solutions gives a complete list
of original solutions. -/
theorem pull_complete [DecidableEq α] (e : Exact P Q) {T : Finset β} (hT : ∀ b, Q b ↔ b ∈ T)
    (a : α) : P a ↔ a ∈ e.pull T := by
  simp only [pull, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
  rw [e.iff]
  exact ⟨fun ⟨b, hb, he⟩ => ⟨b, (hT b).mp hb, he⟩, fun ⟨b, hb, he⟩ => ⟨b, (hT b).mpr hb, he⟩⟩

/-- For a reduction between constraints indexed by `n`, which keeps `n` both ways: `n` has an
original solution iff it has an admissible reduced solution. -/
theorem exists_iff {P : ℕ × ℤ → Prop} {Q : ℕ × ℤ → Prop} (e : Exact P Q)
    (hf : ∀ a, (e.fwd a).1 = a.1) (hb : ∀ b a, e.bwd b = some a → a.1 = b.1) (n : ℕ) :
    (∃ y, P (n, y)) ↔ ∃ m, Q (n, m) ∧ (e.bwd (n, m)).isSome := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(e.fwd (n, y)).2, ?_, ?_⟩
    · have := e.fwd_sol _ hy
      rwa [show e.fwd (n, y) = (n, (e.fwd (n, y)).2) from Prod.ext (hf _) rfl] at this
    · rw [show ((n, (e.fwd (n, y)).2) : ℕ × ℤ) = e.fwd (n, y) from Prod.ext (hf (n, y)).symm rfl,
        e.bwd_fwd _ hy]
      rfl
  · rintro ⟨m, hm, hs⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hs
    have h1 := hb _ _ ha
    refine ⟨a.2, ?_⟩
    rw [show ((n, a.2) : ℕ × ℤ) = a from Prod.ext h1.symm rfl]
    exact e.bwd_sol _ a hm ha

/-- **Counts agree** through an index-preserving reduction, after the admissibility filter. -/
theorem count_eq {P : ℕ × ℤ → Prop} {Q : ℕ × ℤ → Prop} (e : Exact P Q)
    (hf : ∀ a, (e.fwd a).1 = a.1) (hb : ∀ b a, e.bwd b = some a → a.1 = b.1)
    [DecidablePred fun n : ℕ => ∃ y, P (n, y)]
    [DecidablePred fun n : ℕ => ∃ m, Q (n, m) ∧ (e.bwd (n, m)).isSome] (N : ℕ) :
    ((Finset.Icc 1 N).filter fun n => ∃ y, P (n, y)).card =
      ((Finset.Icc 1 N).filter fun n => ∃ m, Q (n, m) ∧ (e.bwd (n, m)).isSome).card := by
  congr 1
  exact Finset.filter_congr fun n _ => e.exists_iff hf hb n

end Exact

/-! ### Affine substitution -/

/-- `n ↦ t = r n + s` (with `n ≥ 1`), pulled back when `r ∣ t - s` and `(t - s)/r ≥ 1`. -/
def affine (Q : ℤ × ℤ → Prop) {r : ℤ} (hr : r ≠ 0) (s : ℤ) :
    Exact (fun p : ℕ × ℤ => 1 ≤ p.1 ∧ Q (r * p.1 + s, p.2)) Q where
  fwd p := (r * p.1 + s, p.2)
  bwd q := if r ∣ q.1 - s ∧ 1 ≤ (q.1 - s) / r then some (((q.1 - s) / r).toNat, q.2) else none
  fwd_sol _ h := h.2
  bwd_sol q p hq he := by
    split_ifs at he with h
    · cases he
      obtain ⟨⟨k, hk⟩, h1⟩ := h
      have hk' : (q.1 - s) / r = k := by rw [hk]; exact Int.mul_ediv_cancel_left _ hr
      rw [hk'] at h1 ⊢
      refine ⟨by omega, ?_⟩
      have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
      simp only [this]
      rw [show r * k + s = q.1 by linarith]
      exact hq
  bwd_fwd p h := by
    have hq : (r * (p.1 : ℤ) + s - s) / r = p.1 := by
      rw [add_sub_cancel_right]; exact Int.mul_ediv_cancel_left _ hr
    simp only [hq]
    rw [if_pos ⟨⟨p.1, by ring⟩, by exact_mod_cast h.1⟩]
    simp

/-! ### Quadratic integer roots through the discriminant -/

/-- `a y^2 + b y + c = F n` with `y ∈ Y` reduces to `m^2 = 4a F n + b^2 - 4ac` by `m = 2ay + b`;
the way back needs `2a ∣ m - b` and `(m - b) / (2a) ∈ Y`. -/
def quadratic {a : ℤ} (ha : a ≠ 0) (b c : ℤ) (F : ℕ → ℤ) (Y : ℤ → Prop) [DecidablePred Y] :
    Exact (fun p : ℕ × ℤ => 1 ≤ p.1 ∧ Y p.2 ∧ a * p.2 ^ 2 + b * p.2 + c = F p.1)
      (fun q : ℕ × ℤ => 1 ≤ q.1 ∧ q.2 ^ 2 = 4 * a * F q.1 + b ^ 2 - 4 * a * c) where
  fwd p := (p.1, 2 * a * p.2 + b)
  bwd q := if 2 * a ∣ q.2 - b ∧ Y ((q.2 - b) / (2 * a)) then some (q.1, (q.2 - b) / (2 * a))
    else none
  fwd_sol p h := ⟨h.1, by rw [← h.2.2]; ring⟩
  bwd_sol q p hq he := by
    split_ifs at he with h
    · cases he
      obtain ⟨⟨k, hk⟩, hY⟩ := h
      have hk' : (q.2 - b) / (2 * a) = k := by
        rw [hk]; exact Int.mul_ediv_cancel_left _ (by positivity)
      rw [hk'] at hY ⊢
      refine ⟨hq.1, hY, ?_⟩
      have hm : q.2 = 2 * a * k + b := by linarith
      have h2 := hq.2
      rw [hm] at h2
      have : 4 * a * (a * k ^ 2 + b * k + c - F q.1) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (by positivity)
      · linarith
  bwd_fwd p h := by
    have hq : (2 * a * p.2 + b - b) / (2 * a) = p.2 := by
      rw [add_sub_cancel_right]; exact Int.mul_ediv_cancel_left _ (by positivity)
    simp only [hq]
    rw [if_pos ⟨⟨p.2, by ring⟩, h.2.1⟩]

theorem quadratic_fwd_fst {a : ℤ} (ha : a ≠ 0) (b c : ℤ) (F : ℕ → ℤ) (Y : ℤ → Prop)
    [DecidablePred Y] (p : ℕ × ℤ) : ((quadratic ha b c F Y).fwd p).1 = p.1 := rfl

theorem quadratic_bwd_fst {a : ℤ} (ha : a ≠ 0) (b c : ℤ) (F : ℕ → ℤ) (Y : ℤ → Prop)
    [DecidablePred Y] (q p : ℕ × ℤ) (h : (quadratic ha b c F Y).bwd q = some p) : p.1 = q.1 := by
  simp only [quadratic] at h
  split_ifs at h
  cases h; rfl

/-! ### Triangular numbers -/

/-- `y (y + 1) = 2 F n` (that is, `F n` is the triangular number `y(y+1)/2`) reduces to
`m^2 = 8 F n + 1`. -/
def triangular (F : ℕ → ℤ) (Y : ℤ → Prop) [DecidablePred Y] :
    Exact (fun p : ℕ × ℤ => 1 ≤ p.1 ∧ Y p.2 ∧ p.2 * (p.2 + 1) = 2 * F p.1)
      (fun q : ℕ × ℤ => 1 ≤ q.1 ∧ q.2 ^ 2 = 8 * F q.1 + 1) :=
  ((quadratic one_ne_zero 1 0 (fun n => 2 * F n) Y).congr fun p => by
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, h2, by linarith⟩).congrRight
    fun q => by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

/-- An odd square root: `m^2 = 8 v + 1` forces `2 ∣ m - 1`. -/
lemma two_dvd_of_sq {m v : ℤ} (h : m ^ 2 = 8 * v + 1) : 2 ∣ m - 1 := by
  rcases Int.emod_two_eq_zero_or_one m with h0 | h0
  · exfalso
    obtain ⟨k, rfl⟩ := Int.dvd_of_emod_eq_zero h0
    have h' : 4 * (k * k) = 8 * v + 1 := by rw [← h]; ring
    omega
  · exact ⟨m / 2, by omega⟩

open Classical in
/-- **Triangular values, counted.**  For `Y = ℤ` or `Y = {y ≥ 0}`, the number of `n ∈ [1, N]`
at which `F n` is a triangular number equals the number at which `8 F n + 1` is a square: the
integrality condition of the way back always holds. -/
theorem triangular_count (F : ℕ → ℤ) (Y : ℤ → Prop) [DecidablePred Y]
    (hY : ∀ m : ℤ, Odd m → Y ((m - 1) / 2) ∨ Y ((-m - 1) / 2)) (N : ℕ) :
    ((Finset.Icc 1 N).filter fun n => ∃ y, Y y ∧ y * (y + 1) = 2 * F n).card =
      A (fun n => 8 * F n) 2 1 N := by
  classical
  unfold A
  congr 1
  apply Finset.filter_congr
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have key := (triangular F Y).exists_iff (fun _ => rfl)
    (fun q p h => quadratic_bwd_fst one_ne_zero 1 0 (fun n => 2 * F n) Y q p h) n
  have e1 : (∃ y, Y y ∧ y * (y + 1) = 2 * F n) ↔
      ∃ y, 1 ≤ (n, y).1 ∧ Y (n, y).2 ∧ (n, y).2 * ((n, y).2 + 1) = 2 * F (n, y).1 := by
    simp only; exact ⟨fun ⟨y, h⟩ => ⟨y, hn1, h⟩, fun ⟨y, _, h⟩ => ⟨y, h⟩⟩
  rw [e1, key]
  constructor
  · rintro ⟨m, hm, -⟩; exact ⟨m, hm.2.symm⟩
  · rintro ⟨m, hm⟩
    have hm2 : m ^ 2 = 8 * F n + 1 := hm.symm
    have hodd : Odd m := by
      obtain ⟨k, hk⟩ := two_dvd_of_sq hm2
      exact ⟨k, by linarith⟩
    have hsome : ∀ m' : ℤ, m' ^ 2 = 8 * F n + 1 → Y ((m' - 1) / 2) →
        ∃ m'', (1 ≤ (n, m'').1 ∧ (n, m'').2 ^ 2 = 8 * F (n, m'').1 + 1) ∧
          ((triangular F Y).bwd (n, m'')).isSome := by
      intro m' hm' hY'
      refine ⟨m', ⟨hn1, hm'⟩, ?_⟩
      simp only [triangular, Exact.congrRight, Exact.congr, quadratic, mul_one]
      rw [if_pos ⟨two_dvd_of_sq hm', hY'⟩]
      rfl
    rcases hY m hodd with h | h
    · exact hsome m hm2 h
    · exact hsome (-m) (by rw [neg_sq]; exact hm2) (by simpa using h)

open Classical in
/-- `triangular_count` for `y ∈ ℤ`. -/
theorem triangular_count_int (F : ℕ → ℤ) (N : ℕ) :
    ((Finset.Icc 1 N).filter fun n => ∃ y : ℤ, y * (y + 1) = 2 * F n).card =
      A (fun n => 8 * F n) 2 1 N := by
  rw [← triangular_count F (fun _ => True) (fun _ _ => Or.inl trivial) N]
  simp only [true_and]

open Classical in
/-- `triangular_count` for `y ≥ 0`: the nonnegative root `(|m| - 1)/2` is always available. -/
theorem triangular_count_nonneg (F : ℕ → ℤ) (N : ℕ) :
    ((Finset.Icc 1 N).filter fun n => ∃ y : ℤ, 0 ≤ y ∧ y * (y + 1) = 2 * F n).card =
      A (fun n => 8 * F n) 2 1 N := by
  refine triangular_count F (fun y => 0 ≤ y) (fun m ⟨k, hk⟩ => ?_) N
  subst hk
  rcases le_or_lt 0 k with h | h
  · left
    show 0 ≤ (2 * k + 1 - 1) / 2
    rw [show 2 * k + 1 - 1 = 2 * k by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
    exact h
  · right
    show 0 ≤ (-(2 * k + 1) - 1) / 2
    rw [show -(2 * k + 1) - 1 = 2 * (-k - 1) by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
    omega

/-! ### A composite worked example -/

/-- `F(n) = 64 n^3 - 120 n^2 + 75 n - 16`, so that `8 F(n) + 1 = (8n - 5)^3 - 2`. -/
def triF (n : ℕ) : ℤ := 64 * (n : ℤ) ^ 3 - 120 * (n : ℤ) ^ 2 + 75 * n - 16

/-- The chain triangular → affine `t = 8n - 5` → `m^2 = t^3 - 2`. -/
def triChain :
    Exact (fun p : ℕ × ℤ => 1 ≤ p.1 ∧ True ∧ p.2 * (p.2 + 1) = 2 * triF p.1)
      (fun q : ℤ × ℤ => q.2 ^ 2 = q.1 ^ 3 - 2) :=
  (triangular triF fun _ => True).comp
    ((affine (fun q : ℤ × ℤ => q.2 ^ 2 = q.1 ^ 3 - 2) (by norm_num : (8 : ℤ) ≠ 0) (-5)).congr
      fun p => by
        simp only [triF]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linear_combination h2⟩)

/-- The complete reduced list, from `MordellMinus2.points`. -/
theorem cube_sub_two_pairs (q : ℤ × ℤ) : q.2 ^ 2 = q.1 ^ 3 - 2 ↔ q ∈ ({(3, 5), (3, -5)} : Finset (ℤ × ℤ)) := by
  obtain ⟨x, y⟩ := q
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rw [MordellMinus2.points]
  tauto

/-- **Worked example, complete.**  `y (y+1)/2 = 64n^3 - 120n^2 + 75n - 16` with `n ≥ 1` and
`y ∈ ℤ` holds exactly for `(n, y) = (1, 2)` and `(1, -3)`. -/
theorem tri_cube_complete (n : ℕ) (y : ℤ) :
    (1 ≤ n ∧ y * (y + 1) = 2 * triF n) ↔ (n = 1 ∧ (y = 2 ∨ y = -3)) := by
  have h := triChain.pull_complete cube_sub_two_pairs (n, y)
  have hpull : triChain.pull ({(3, 5), (3, -5)} : Finset (ℤ × ℤ)) = {(1, 2), (1, -3)} := by
    decide
  rw [hpull] at h
  simp only [true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rw [h]
  tauto

end PerfectPower.Reduction
