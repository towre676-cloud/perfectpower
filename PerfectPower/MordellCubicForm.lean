import Mathlib.Tactic

/-!
# Mordell's cubic forms for `y² = x³ + k`

A route to the curves `y² = x³ + k` that needs no quadratic field (for `k > 0` the factorization of
`y² − k` is real quadratic, with infinitely many units).  Write binary cubic forms as
`F = a X³ + 3b X²Y + 3c XY² + d Y³`, stored as `(a, b, c, d)`, with the invariant

`Δ(F) = (ad − bc)² − 4(ac − b²)(bd − c²)`   (the discriminant is `−27 Δ`).

* `form_of_point`: a point `(x, y)` gives `F = (1, 0, −x, −2y)` with `F(1, 0) = 1` and `Δ = 4k`.
* `delta_act`, `ev_act`: `F ∘ T` for `T = (p q; r s)` has `Δ(F ∘ T) = (ps − qr)⁶ Δ(F)`, and its
  values are those of `F` at `T (u, v)`.
* `ClassList k Gs`: every form with `Δ = 4k` is `G ∘ T` for some `G ∈ Gs`, `T ∈ GL₂(ℤ)`.  This is
  the finiteness of the classes, a **premise** here: the reduction bound that proves it is not
  formalized (`python/positive_k.py` enumerates the classes inside a stated reduction bound and
  checks the list exactly; the bound itself is a paper argument).
* `no_point_of_classes`: under `ClassList k Gs`, if no `G ∈ Gs` represents `1`, the curve has no
  integral point.  `locImpB_sound` gives "no representation" from a finite residue check.
-/

namespace PerfectPower.MordellCubicForm

/-- The value `a u³ + 3b u²v + 3c uv² + d v³`. -/
def ev (F : ℤ × ℤ × ℤ × ℤ) (u v : ℤ) : ℤ :=
  F.1 * u ^ 3 + 3 * F.2.1 * u ^ 2 * v + 3 * F.2.2.1 * u * v ^ 2 + F.2.2.2 * v ^ 3

/-- The invariant `Δ = (ad − bc)² − 4(ac − b²)(bd − c²)`. -/
def delta (F : ℤ × ℤ × ℤ × ℤ) : ℤ :=
  (F.1 * F.2.2.2 - F.2.1 * F.2.2.1) ^ 2 - 4 * (F.1 * F.2.2.1 - F.2.1 ^ 2) * (F.2.1 * F.2.2.2 - F.2.2.1 ^ 2)

/-- `F ∘ T` for `T = (p q; r s)`: `F(pX + qY, rX + sY)`, again in the shape `(a, 3b, 3c, d)`. -/
def act (F : ℤ × ℤ × ℤ × ℤ) (p q r s : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  let (a, b, c, d) := F
  (a * p ^ 3 + 3 * b * p ^ 2 * r + 3 * c * p * r ^ 2 + d * r ^ 3,
   a * p ^ 2 * q + b * (p ^ 2 * s + 2 * p * q * r) + c * (q * r ^ 2 + 2 * p * r * s) + d * r ^ 2 * s,
   a * p * q ^ 2 + b * (2 * p * q * s + q ^ 2 * r) + c * (p * s ^ 2 + 2 * q * r * s) + d * r * s ^ 2,
   a * q ^ 3 + 3 * b * q ^ 2 * s + 3 * c * q * s ^ 2 + d * s ^ 3)

theorem ev_act (F : ℤ × ℤ × ℤ × ℤ) (p q r s u v : ℤ) :
    ev (act F p q r s) u v = ev F (p * u + q * v) (r * u + s * v) := by
  obtain ⟨a, b, c, d⟩ := F
  simp only [ev, act]
  ring

theorem delta_act (F : ℤ × ℤ × ℤ × ℤ) (p q r s : ℤ) :
    delta (act F p q r s) = (p * s - q * r) ^ 6 * delta F := by
  obtain ⟨a, b, c, d⟩ := F
  simp only [delta, act]
  ring

/-- **The forward map.**  A point gives the form `X³ − 3x XY² − 2y Y³`, with `Δ = 4k` and value `1`
at `(1, 0)`. -/
theorem form_of_point {k x y : ℤ} (h : y ^ 2 = x ^ 3 + k) :
    delta (1, 0, -x, -2 * y) = 4 * k ∧ ev (1, 0, -x, -2 * y) 1 0 = 1 := by
  refine ⟨?_, by simp [ev]⟩
  simp only [delta]
  linear_combination 4 * h

/-- **The way back.**  A form `(1, 0, c, d)` with `Δ = 4k` is the form of the point `(−c, −d/2)`. -/
theorem point_of_monic {k c d : ℤ} (h : delta (1, 0, c, d) = 4 * k) :
    ∃ y, d = -2 * y ∧ y ^ 2 = (-c) ^ 3 + k := by
  simp only [delta] at h
  have h2 : (2 : ℤ) ∣ d := by
    have : (2 : ℤ) ∣ d ^ 2 := ⟨2 * (k - c ^ 3), by linear_combination h⟩
    exact Int.prime_two.dvd_of_dvd_pow this
  obtain ⟨e, he⟩ := h2
  refine ⟨-e, by rw [he]; ring, ?_⟩
  subst he
  nlinarith [h]

/-- **The class-list premise**: every form with `Δ = 4k` is `G ∘ T` for some listed `G` and some
`T ∈ GL₂(ℤ)`. -/
def ClassList (k : ℤ) (Gs : List (ℤ × ℤ × ℤ × ℤ)) : Prop :=
  ∀ F : ℤ × ℤ × ℤ × ℤ, delta F = 4 * k →
    ∃ G ∈ Gs, ∃ p q r s : ℤ, (p * s - q * r) ^ 2 = 1 ∧ act G p q r s = F

/-- **No point** when no listed class represents `1` (under the class-list premise). -/
theorem no_point_of_classes {k : ℤ} {Gs : List (ℤ × ℤ × ℤ × ℤ)} (hcls : ClassList k Gs)
    (hrep : ∀ G ∈ Gs, ∀ u v : ℤ, ev G u v ≠ 1) (x y : ℤ) : y ^ 2 ≠ x ^ 3 + k := by
  intro h
  obtain ⟨hd, hv⟩ := form_of_point h
  obtain ⟨G, hG, p, q, r, s, -, hT⟩ := hcls _ hd
  apply hrep G hG p r
  have := ev_act G p q r s 1 0
  rw [hT, hv] at this
  simpa using this.symm

/-- The residue check: `G(u, v) ≢ 1 (mod m)` for all `0 ≤ u, v < m`. -/
def locImpB (G : ℤ × ℤ × ℤ × ℤ) (m : ℕ) : Bool :=
  (List.range m).all fun u => (List.range m).all fun v => (ev G u v - 1) % (m : ℤ) != 0

theorem ev_emod (G : ℤ × ℤ × ℤ × ℤ) (m u v : ℤ) : ev G (u % m) (v % m) % m = ev G u v % m := by
  obtain ⟨a, b, c, d⟩ := G
  simp only [ev]
  simp [Int.add_emod, Int.mul_emod, pow_succ, Int.emod_emod_of_dvd]

theorem locImpB_sound {G : ℤ × ℤ × ℤ × ℤ} {m : ℕ} (hm : 0 < m) (h : locImpB G m = true) (u v : ℤ) :
    ev G u v ≠ 1 := by
  intro hv
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hu0 := Int.emod_nonneg u hm'.ne'
  have hv0 := Int.emod_nonneg v hm'.ne'
  have hu1 := Int.emod_lt_of_pos u hm'
  have hv1 := Int.emod_lt_of_pos v hm'
  simp only [locImpB, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  have := h (u % m).toNat (by omega) (v % m).toNat (by omega)
  rw [Int.toNat_of_nonneg hu0, Int.toNat_of_nonneg hv0] at this
  apply this
  rw [Int.sub_emod, ev_emod, hv]
  simp

/-- A class list with one residue modulus per class: every `Δ` is `4k`, and every class is
locally impossible for the value `1`. -/
def emptyCertB (k : ℤ) (Cs : List ((ℤ × ℤ × ℤ × ℤ) × ℕ)) : Bool :=
  Cs.all fun c => delta c.1 == 4 * k && 0 < c.2 && locImpB c.1 c.2

/-- **Emptiness from a certificate**, under the class-list premise. -/
theorem no_point_of_cert {k : ℤ} {Cs : List ((ℤ × ℤ × ℤ × ℤ) × ℕ)}
    (hcls : ClassList k (Cs.map Prod.fst)) (h : emptyCertB k Cs = true) (x y : ℤ) :
    y ^ 2 ≠ x ^ 3 + k := by
  refine no_point_of_classes hcls (fun G hG u v => ?_) x y
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hG
  simp only [emptyCertB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hm⟩, hl⟩ := h c hc
  exact locImpB_sound hm hl u v

end PerfectPower.MordellCubicForm
