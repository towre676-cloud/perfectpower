import PerfectPower.Genus1
import PerfectPower.MordellMinus2
import PerfectPower.MordellFLT3
import PerfectPower.MordellDescent

/-!
# Transporting completeness through changes of variables, with exact counts

A completeness theorem about a curve is only useful for a polynomial hit count after it is carried
through the change of variables that relates the two, **keeping the integrality conditions**.

* `CompleteArgs G d T`: for every *integer* `t`, `G t` is a `d`-th power iff `t ∈ T`.
* `affine_isHit`, `affine_count`: for `r ≠ 0`, the family `n ↦ G (r n + s)` has hit criterion
  `r n + s ∈ T`, and its count `A(N)` equals the number of `t ∈ T` with `r ∣ t - s` and
  `1 ≤ (t - s) / r ≤ N`.  Both come from the same hypothesis.
* `IntegralPointsOnImage`: the premise of `Genus1.cubic_sound` restricted to the image of the
  change of variables `U = 9 a n + 3 b`, `V = 27 a m`.  Only points with `9a ∣ U - 3b` and
  `27a ∣ V` are required.  `IntegralPointsOn` implies it; the converse can fail, which is why a
  theorem about `m^2 = F(n)` discharges this premise but not the old one.  `n3m2_hits` does so for
  `n^3 - 2`, whose model `V^2 = U^3 - 1458` has integral points this file never classifies.

Completed inputs: `MordellMinus2` (rank one, `T = {3}`), `MordellFLT3` (`T = {12 u^2}`) and
`MordellDescent` (`T = ∅`).
-/

namespace PerfectPower.Transport

open PerfectPower

/-- A complete list of integer arguments. -/
def CompleteArgs (G : ℤ → ℤ) (d : ℕ) (T : Finset ℤ) : Prop :=
  ∀ t : ℤ, IsHit d (G t) ↔ t ∈ T

theorem affine_isHit {G : ℤ → ℤ} {d : ℕ} {T : Finset ℤ} (hT : CompleteArgs G d T) (r s : ℤ)
    (n : ℕ) : IsHit d (G (r * n + s)) ↔ r * n + s ∈ T :=
  hT _

/-- **Exact count through an affine substitution.** -/
theorem affine_count {G : ℤ → ℤ} {d : ℕ} {T : Finset ℤ} (hT : CompleteArgs G d T) {r : ℤ}
    (hr : r ≠ 0) (s : ℤ) (N : ℕ) :
    A (fun n => G (r * n + s)) d 0 N
      = (T.filter (fun t => r ∣ t - s ∧ 1 ≤ (t - s) / r ∧ (t - s) / r ≤ N)).card := by
  classical
  unfold A
  have e : (Finset.Icc 1 N).filter (fun n : ℕ => IsHit d (G (r * n + s) + 0))
      = (Finset.Icc 1 N).filter (fun n : ℕ => r * n + s ∈ T) :=
    Finset.filter_congr (fun n _ => by rw [add_zero]; exact hT _)
  rw [e]
  refine Finset.card_bij (fun n _ => r * (n : ℤ) + s) ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    have hq : (r * (n : ℤ) + s - s) / r = n := by
      rw [add_sub_cancel_right]; exact Int.mul_ediv_cancel_left _ hr
    refine ⟨hn.2, ⟨n, by ring⟩, ?_, ?_⟩ <;> rw [hq] <;> omega
  · intro n₁ _ n₂ _ h
    simp only at h
    have : (n₁ : ℤ) = n₂ := mul_left_cancel₀ hr (by linarith)
    exact_mod_cast this
  · intro t ht
    simp only [Finset.mem_filter] at ht
    obtain ⟨htT, ⟨q, hq⟩, h1, h2⟩ := ht
    have hqv : (t - s) / r = q := by rw [hq]; exact Int.mul_ediv_cancel_left _ hr
    rw [hqv] at h1 h2
    refine ⟨q.toNat, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      have : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg (by omega)
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [this]; convert htT using 1; linarith
    · have : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg (by omega)
      show r * ((q.toNat : ℕ) : ℤ) + s = t
      rw [this]; linarith

/-- The count is at most `#T`, whatever the substitution. -/
theorem affine_count_le {G : ℤ → ℤ} {d : ℕ} {T : Finset ℤ} (hT : CompleteArgs G d T) {r : ℤ}
    (hr : r ≠ 0) (s : ℤ) (N : ℕ) : A (fun n => G (r * n + s)) d 0 N ≤ T.card := by
  classical
  rw [affine_count hT hr]; exact Finset.card_filter_le _ _

/-! ### Completed inputs -/

theorem complete_cube_sub_two : CompleteArgs (fun t => t ^ 3 - 2) 2 {3} := by
  intro t
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨m, hm⟩; exact ((MordellMinus2.points t m).mp hm.symm).1
  · rintro rfl; exact ⟨5, by norm_num⟩

theorem complete_fermat (u : ℤ) (hu : u ≠ 0) :
    CompleteArgs (fun t => t ^ 3 - 432 * u ^ 6) 2 {12 * u ^ 2} := by
  intro t
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨m, hm⟩; exact ((MordellFLT3.points u hu t m).mp hm.symm).1
  · rintro rfl; exact ⟨36 * u ^ 3, by ring⟩

theorem complete_of_no_points {k : ℤ} (h : ∀ x y : ℤ, y ^ 2 ≠ x ^ 3 + k) :
    CompleteArgs (fun t => t ^ 3 + k) 2 ∅ := by
  intro t
  simp only [Finset.notMem_empty, iff_false]
  rintro ⟨m, hm⟩; exact h t m hm.symm

/-- **Worked example.**  For `r ≠ 0`, `(r n + s)^3 - 2` is a square iff `r n + s = 3`, and the
number of such `n ∈ [1, N]` is `1` when `r ∣ 3 - s` and `1 ≤ (3 - s)/r ≤ N`, else `0`. -/
theorem affine_cube_sub_two {r : ℤ} (hr : r ≠ 0) (s : ℤ) (N : ℕ) :
    (∀ n : ℕ, IsHit 2 ((r * n + s) ^ 3 - 2) ↔ r * n + s = 3) ∧
    A (fun n => (r * n + s) ^ 3 - 2) 2 0 N
      = if r ∣ 3 - s ∧ 1 ≤ (3 - s) / r ∧ (3 - s) / r ≤ N then 1 else 0 := by
  classical
  refine ⟨fun n => by simpa using complete_cube_sub_two (r * n + s), ?_⟩
  rw [affine_count complete_cube_sub_two hr, Finset.filter_singleton]
  split_ifs <;> simp

/-! ### The image-restricted Genus-one premise -/

/-- Every integral point of the model **in the image of `(n, m) ↦ (9 a n + 3 b, 27 a m)`** is
listed. -/
def IntegralPointsOnImage (a b : ℤ) (A B : ℤ) (L : List (ℤ × ℤ)) : Prop :=
  ∀ U V : ℤ, V ^ 2 = U ^ 3 + A * U + B → 9 * a ∣ U - 3 * b → 27 * a ∣ V → (U, V) ∈ L

theorem IntegralPointsOnImage.of_all {a b A B : ℤ} {L : List (ℤ × ℤ)}
    (h : Genus1.IntegralPointsOn A B L) : IntegralPointsOnImage a b A B L :=
  fun U V hUV _ _ => h U V hUV

/-- `Genus1.cubic_sound` from the weaker, image-restricted premise. -/
theorem cubic_sound_image {a b c e : ℤ} {L : List (ℤ × ℤ)} {hits : List (ℕ × ℤ)}
    (hpts : IntegralPointsOnImage a b (Genus1.cubicModel a b c e).1 (Genus1.cubicModel a b c e).2 L)
    (hok : Genus1.cubicOK a b c e L hits = true) (n : ℕ) (hn : 1 ≤ n) :
    IsHit 2 (Reflect.ev [e, c, b, a] n) ↔ n ∈ hits.map Prod.fst := by
  simp only [Genus1.cubicOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨ha, -⟩, hpull⟩, hwit⟩ := hok
  constructor
  · rintro ⟨m, hm⟩
    rw [Genus1.ev_cubic] at hm
    have hmem := hpts (9 * a * n + 3 * b) (27 * a * m) (by
      simp only [Genus1.cubicModel]; linear_combination (-(729 * a ^ 2)) * hm)
      ⟨n, by ring⟩ ⟨m, by ring⟩
    have := hpull _ hmem
    have hp : Genus1.cubicPull a b (9 * a * n + 3 * b, 27 * a * m) = some n := by
      have e1 : (9 * a * (n : ℤ) + 3 * b - 3 * b) / (9 * a) = n := by
        rw [show 9 * a * (n : ℤ) + 3 * b - 3 * b = 9 * a * n by ring]
        exact Int.mul_ediv_cancel_left _ (by positivity)
      simp only [Genus1.cubicPull, e1]
      rw [if_pos ⟨⟨n, by ring⟩, ⟨m, by ring⟩, by exact_mod_cast hn⟩]
      simp
    rw [hp] at this
    simpa using this
  · intro hmem
    obtain ⟨⟨k, m⟩, hkm, rfl⟩ := List.mem_map.mp hmem
    have := hwit _ hkm
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨m, this.2.symm⟩

/-- The model of `m^2 = n^3 - 2` is `V^2 = U^3 - 1458` (`U = 9n`, `V = 27m`).  Its image points
are exactly `(27, ± 135)`, by `MordellMinus2.points`; no statement about the other integral points
of `V^2 = U^3 - 1458` is needed. -/
theorem n3m2_image : IntegralPointsOnImage 1 0 (Genus1.cubicModel 1 0 0 (-2)).1
    (Genus1.cubicModel 1 0 0 (-2)).2 [(27, 135), (27, -135)] := by
  intro U V hUV ⟨n, hn⟩ ⟨m, hm⟩
  simp only [Genus1.cubicModel] at hUV
  have hU : U = 9 * n := by linarith
  have hV : V = 27 * m := by linarith
  subst hU hV
  have : m ^ 2 = n ^ 3 - 2 := by nlinarith
  obtain ⟨rfl, rfl | rfl⟩ := (MordellMinus2.points n m).mp this <;> simp

theorem n3m2_ok : Genus1.cubicOK 1 0 0 (-2) [(27, 135), (27, -135)] [(3, 5)] = true := by
  decide +kernel

/-- `n^3 - 2` through the generic genus-one checker, now **unconditional**. -/
theorem n3m2_hits (n : ℕ) (hn : 1 ≤ n) : IsHit 2 ((n : ℤ) ^ 3 - 2) ↔ n = 3 := by
  have h := cubic_sound_image n3m2_image n3m2_ok n hn
  have e : Reflect.ev [-2, 0, 0, 1] n = (n : ℤ) ^ 3 - 2 := by simp [Reflect.ev]; ring
  rw [e] at h; rw [h]; simp

end PerfectPower.Transport
