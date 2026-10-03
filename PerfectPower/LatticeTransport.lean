import Mathlib.Tactic

/-!
# Complete solution sets through integer matrices of any nonzero determinant

`ThueLocal` transports complete solution sets through `GL₂(ℤ)`.  This module allows any integer
matrix `T` with `Δ = det T ≠ 0`, a translation `c` and a scale `s ≠ 0`.  Let `A = adj T`.

* **Affine lattice transport** (`complete_of_complete`).  If `F(Tz + c) = s · G(z)` for all `z`, and
  `L` is a complete list for `F = sM`, then the complete list for `G = M` is `L` filtered by the
  congruence `A(x − c) ≡ 0 (mod Δ)` and mapped by `x ↦ A(x − c)/Δ`.  The congruence is exactly the
  integrality condition: `A(Tz) = Δz` gives it for transported points, and conversely `z = A(x − c)/Δ`
  is integral with `Tz + c = x`.  No new search is needed.
* **Restricted emptiness** (`empty_of_filter`): if no point of `L` passes the congruence, `G = M` has
  no solution, even though `F = sM` may have some.
* **Unimodular case** (`complete_of_unimodular`): for `Δ = ±1` the congruence is vacuous.
* **Monic reduction** (`monic_identity`, `monic_complete`, `disc_monic`).  For
  `F = au³ + bu²v + cuv² + dv³`, `a ≠ 0`, put `H = X³ + bX²Y + acXY² + a²dY³`.  Then
  `H(au, v) = a² F(u, v)`, so `F = M` is `H = a²M` restricted to `a ∣ X`, with `(u, v) = (X/a, Y)`;
  and `Disc H = a² Disc F`.  The restriction matters: `(X, Y) = (1, 3)` solves
  `X³ + X²Y − 4Y³ = 4 · (−26)` but does not pull back to `2u³ + u²v − v³ = −26` (`monic_filter_needed`).

The statements are classical; the module makes them a checked interface for the compiler's edges
(`python/lattice_transport.py` mirrors the filter).
-/

namespace PerfectPower.LatticeTransport

/-- An integer `2 × 2` matrix `(p q; r s)`. -/
structure Mat where
  /-- Row 1. -/
  p : ℤ
  /-- Row 1. -/
  q : ℤ
  /-- Row 2. -/
  r : ℤ
  /-- Row 2. -/
  s : ℤ

/-- `det T`. -/
def Mat.det (T : Mat) : ℤ := T.p * T.s - T.q * T.r

/-- `T z`. -/
def Mat.ap (T : Mat) (z : ℤ × ℤ) : ℤ × ℤ := (T.p * z.1 + T.q * z.2, T.r * z.1 + T.s * z.2)

/-- The adjugate `adj T = (s −q; −r p)`. -/
def Mat.adj (T : Mat) : Mat := ⟨T.s, -T.q, -T.r, T.p⟩

lemma adj_ap (T : Mat) (z : ℤ × ℤ) : T.adj.ap (T.ap z) = (T.det * z.1, T.det * z.2) := by
  simp only [Mat.adj, Mat.ap, Mat.det, Prod.mk.injEq]; constructor <;> ring

lemma ap_adj (T : Mat) (x : ℤ × ℤ) : T.ap (T.adj.ap x) = (T.det * x.1, T.det * x.2) := by
  simp only [Mat.adj, Mat.ap, Mat.det, Prod.mk.injEq]; constructor <;> ring

/-- The lattice condition `A(x − c) ≡ 0 (mod Δ)`, as a decidable test. -/
def latB (T : Mat) (c x : ℤ × ℤ) : Bool :=
  decide (T.det ∣ (T.adj.ap (x - c)).1) && decide (T.det ∣ (T.adj.ap (x - c)).2)

/-- The pull-back `x ↦ A(x − c)/Δ`. -/
def pull (T : Mat) (c x : ℤ × ℤ) : ℤ × ℤ :=
  ((T.adj.ap (x - c)).1 / T.det, (T.adj.ap (x - c)).2 / T.det)

lemma pull_ap {T : Mat} (hΔ : T.det ≠ 0) (c z : ℤ × ℤ) : pull T c (T.ap z + c) = z := by
  simp only [pull, add_sub_cancel_right, adj_ap]
  rw [Int.mul_ediv_cancel_left _ hΔ, Int.mul_ediv_cancel_left _ hΔ]

lemma latB_ap (T : Mat) (c z : ℤ × ℤ) : latB T c (T.ap z + c) = true := by
  simp only [latB, add_sub_cancel_right, adj_ap, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩

lemma ap_pull {T : Mat} {c x : ℤ × ℤ} (hΔ : T.det ≠ 0) (h : latB T c x = true) :
    T.ap (pull T c x) + c = x := by
  simp only [latB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  have e : pull T c x = (k1, k2) := by
    simp only [pull, hk1, hk2, Int.mul_ediv_cancel_left _ hΔ]
  have hv : T.adj.ap (x - c) = (T.det * k1, T.det * k2) := Prod.ext hk1 hk2
  have h2 := ap_adj T (x - c)
  rw [hv] at h2
  have h2a := congrArg Prod.fst h2
  have h2b := congrArg Prod.snd h2
  simp only [Mat.ap, Prod.fst_sub, Prod.snd_sub] at h2a h2b
  rw [e]
  refine Prod.ext ?_ ?_ <;> simp only [Mat.ap, Prod.fst_add, Prod.snd_add]
  · have := mul_left_cancel₀ hΔ
      (show T.det * (T.p * k1 + T.q * k2) = T.det * (x.1 - c.1) by linear_combination h2a)
    linarith
  · have := mul_left_cancel₀ hΔ
      (show T.det * (T.r * k1 + T.s * k2) = T.det * (x.2 - c.2) by linear_combination h2b)
    linarith

/-- **Affine lattice transport of a complete list.** -/
theorem complete_of_complete {F G : ℤ × ℤ → ℤ} {T : Mat} {c : ℤ × ℤ} {s M : ℤ}
    (hΔ : T.det ≠ 0) (hs : s ≠ 0) (hFG : ∀ z, F (T.ap z + c) = s * G z)
    {L : List (ℤ × ℤ)} (hL : ∀ x, F x = s * M ↔ x ∈ L) (z : ℤ × ℤ) :
    G z = M ↔ z ∈ (L.filter (latB T c)).map (pull T c) := by
  constructor
  · intro h
    refine List.mem_map.mpr ⟨T.ap z + c, List.mem_filter.mpr ⟨(hL _).mp ?_, latB_ap T c z⟩, pull_ap hΔ c z⟩
    rw [hFG, h]
  · intro h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    obtain ⟨hxL, hlat⟩ := List.mem_filter.mp hx
    have hF := (hL x).mpr hxL
    rw [← ap_pull hΔ hlat, hFG] at hF
    exact mul_left_cancel₀ hs hF

/-- **Restricted emptiness**: no point of the source list lies on the required affine sublattice. -/
theorem empty_of_filter {F G : ℤ × ℤ → ℤ} {T : Mat} {c : ℤ × ℤ} {s M : ℤ}
    (hΔ : T.det ≠ 0) (hs : s ≠ 0) (hFG : ∀ z, F (T.ap z + c) = s * G z)
    {L : List (ℤ × ℤ)} (hL : ∀ x, F x = s * M ↔ x ∈ L) (h0 : L.filter (latB T c) = []) (z : ℤ × ℤ) :
    G z ≠ M := by
  intro h
  have := (complete_of_complete hΔ hs hFG hL z).mp h
  rw [h0] at this
  simp at this

/-- **The unimodular case**: for `Δ = ±1` every point of the list pulls back. -/
theorem complete_of_unimodular {F G : ℤ × ℤ → ℤ} {T : Mat} {c : ℤ × ℤ} {s M : ℤ}
    (hΔ : T.det = 1 ∨ T.det = -1) (hs : s ≠ 0) (hFG : ∀ z, F (T.ap z + c) = s * G z)
    {L : List (ℤ × ℤ)} (hL : ∀ x, F x = s * M ↔ x ∈ L) (z : ℤ × ℤ) :
    G z = M ↔ z ∈ L.map (pull T c) := by
  have hne : T.det ≠ 0 := by rcases hΔ with h | h <;> rw [h] <;> norm_num
  have hall : L.filter (latB T c) = L := by
    apply List.filter_eq_self.mpr
    intro x _
    simp only [latB, Bool.and_eq_true, decide_eq_true_eq]
    rcases hΔ with h | h <;> rw [h] <;> simp
  rw [complete_of_complete hne hs hFG hL z, hall]

/-! ### Monic reduction of a binary cubic -/

/-- `F(u, v) = au³ + bu²v + cuv² + dv³`. -/
def cubic (a b c d : ℤ) (z : ℤ × ℤ) : ℤ := a * z.1 ^ 3 + b * z.1 ^ 2 * z.2 + c * z.1 * z.2 ^ 2 + d * z.2 ^ 3

/-- The monic companion `H(X, Y) = X³ + bX²Y + acXY² + a²dY³`. -/
def monicH (a b c d : ℤ) (z : ℤ × ℤ) : ℤ := cubic 1 b (a * c) (a ^ 2 * d) z

theorem monic_identity (a b c d u v : ℤ) : monicH a b c d (a * u, v) = a ^ 2 * cubic a b c d (u, v) := by
  simp only [monicH, cubic]; ring

/-- **Monic reduction**: a complete list for `H = a²M` gives one for `F = M` (filter `a ∣ X`, divide). -/
theorem monic_complete {a b c d M : ℤ} (ha : a ≠ 0) {L : List (ℤ × ℤ)}
    (hL : ∀ x, monicH a b c d x = a ^ 2 * M ↔ x ∈ L) (z : ℤ × ℤ) :
    cubic a b c d z = M ↔ z ∈ (L.filter (latB ⟨a, 0, 0, 1⟩ (0, 0))).map (pull ⟨a, 0, 0, 1⟩ (0, 0)) := by
  refine complete_of_complete (T := ⟨a, 0, 0, 1⟩) (c := (0, 0)) (s := a ^ 2)
    (by simp [Mat.det, ha]) (pow_ne_zero 2 ha) (fun z => ?_) hL z
  simp only [Mat.ap, zero_mul, add_zero, one_mul, zero_add, Prod.mk_add_mk]
  rw [← monic_identity]

/-- The binary-cubic discriminant. -/
def disc (a b c d : ℤ) : ℤ := b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d - 27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- **`Disc H = a² Disc F`.** -/
theorem disc_monic (a b c d : ℤ) : disc 1 b (a * c) (a ^ 2 * d) = a ^ 2 * disc a b c d := by
  simp only [disc]; ring

/-- **The filter is needed**: `(1, 3)` solves `X³ + X²Y − 4Y³ = 4 · (−26)`, but `2 ∤ 1`, so it does not
pull back to `2u³ + u²v − v³ = −26`. -/
theorem monic_filter_needed :
    monicH 2 1 0 (-1) (1, 3) = 2 ^ 2 * (-26) ∧ latB ⟨2, 0, 0, 1⟩ (0, 0) (1, 3) = false := by
  decide

end PerfectPower.LatticeTransport
