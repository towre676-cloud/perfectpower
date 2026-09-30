import PerfectPower.ClassTwo
import PerfectPower.Transport
import PerfectPower.KernelArith

/-!
# Descent certificates: complete, nonempty point lists for `y^2 = x^3 - D`

`ClassTwo.cube_of_table` needs its table to show that `p^2 + D q^2 = k^3` (`k ≤ K`) happens
only for `(k, p) = (1, ± 1), (4, ± 8)`.  Minkowski's constant grows like `2√D`, so for
`D ≥ 20` the squares `k = 9, 16, …` enter the table and that template no longer applies.  This file
generalizes it and turns the whole argument into one Boolean certificate that the compiler can
discover and the kernel can check, for curves nobody wrote by hand.

**The generalization.**  The table may contain `(k, p, q) = (j^2, ± j^3, 0)`.  Each such entry
means `k^3 α = ± j^3 v^3` with `α = y + √-D`, so `j^3` divides `v^3`.  `DivOK D j` (checked on
residues mod `j^3` by `divB`) says that then `j` divides `v`, so `α = ± (v / j)^3` is still a
cube.  This is the integral closedness of `ℤ[√-D]` at the primes of `j`, and it is checked, not
assumed.

* `tableB D K Q`: for every `k ≤ K` and `|q| ≤ Q`, every solution of `p^2 + D q^2 = k^3` has
  `q = 0` and `k = j^2` with `divB D j`.  Square roots are computed by `isqrtZ` and verified.
* `cube_of_cert`: under the certificate, `y + √-D = (p + q √-D)^3`.
* `points_of_cert`: then `q = ± 1`, `3 p^2 - D = q`, `x = p^2 + D`, `y = p^3 - 3 D p`.
* `pointList D`, `complete_of_cert`: the complete list of integral points, **nonempty**
  whenever `3 p^2 - D = ± 1` has a solution.
* `image_of_complete`: a complete list for `m^2 = t^3 + k` gives
  `Transport.IntegralPointsOnImage` for every constraint `m^2 = (r n + s)^3 + k`, which is exactly
  the premise the compiler names for genus-one cubics; `hits_of_cert` composes it with
  `Transport.cubic_sound_image`.

The certificate fails (and nothing is claimed) when the class number is divisible by 3, when a
non-primitive representation appears, or when `ℤ[√-D]` is not integrally closed at a prime of `j`.
-/

namespace PerfectPower.Descent

open PerfectPower ClassTwo

/-! ### Cube roots of `j^3`-divisible cubes -/

/-- If `j^3` divides `(a - b√-D)^3` then `j` divides `a - b√-D`. -/
def DivOK (D j : ℤ) : Prop := ∀ a b : ℤ, j ^ 3 ∣ W1 D a b → j ^ 3 ∣ W2 D a b → j ∣ a ∧ j ∣ b

/-- `DivOK`, checked on residues mod `j^3`. -/
def divB (D : ℤ) (j : ℕ) : Bool :=
  (List.range (j ^ 3)).all fun A => (List.range (j ^ 3)).all fun B =>
    !(decide (W1 D A B % (j : ℤ) ^ 3 = 0) && decide (W2 D A B % (j : ℤ) ^ 3 = 0)) ||
      (decide ((A : ℤ) % j = 0) && decide ((B : ℤ) % j = 0))

lemma W1_modEq {D a b a' b' M : ℤ} (ha : a ≡ a' [ZMOD M]) (hb : b ≡ b' [ZMOD M]) :
    W1 D a b ≡ W1 D a' b' [ZMOD M] := by
  unfold W1
  exact (ha.pow 3).sub (((Int.ModEq.refl (3 * D)).mul ha).mul (hb.pow 2))

lemma W2_modEq {D a b a' b' M : ℤ} (ha : a ≡ a' [ZMOD M]) (hb : b ≡ b' [ZMOD M]) :
    W2 D a b ≡ W2 D a' b' [ZMOD M] := by
  unfold W2
  exact ((Int.ModEq.refl D).mul (hb.pow 3)).sub (((Int.ModEq.refl 3).mul (ha.pow 2)).mul hb)

lemma divOK_of_divB (D : ℤ) (j : ℕ) (hj : 0 < j) (h : divB D j = true) : DivOK D j := by
  intro a b h1 h2
  set M : ℤ := (j : ℤ) ^ 3 with hMdef
  have hM : 0 < M := by positivity
  have hMn : ((j ^ 3 : ℕ) : ℤ) = M := by push_cast; rfl
  have hA0 := Int.emod_nonneg a hM.ne'
  have hA1 := Int.emod_lt_of_pos a hM
  have hB0 := Int.emod_nonneg b hM.ne'
  have hB1 := Int.emod_lt_of_pos b hM
  have hAc : (((a % M).toNat : ℕ) : ℤ) = a % M := Int.toNat_of_nonneg hA0
  have hBc : (((b % M).toNat : ℕ) : ℤ) = b % M := Int.toNat_of_nonneg hB0
  unfold divB at h
  rw [List.all_eq_true] at h
  have hAr : (a % M).toNat ∈ List.range (j ^ 3) := by
    rw [List.mem_range, ← Nat.cast_lt (α := ℤ), hAc, hMn]; exact hA1
  have hBr : (b % M).toNat ∈ List.range (j ^ 3) := by
    rw [List.mem_range, ← Nat.cast_lt (α := ℤ), hBc, hMn]; exact hB1
  have h' := (List.all_eq_true.mp (h _ hAr)) _ hBr
  rw [hAc, hBc] at h'
  have e1 : W1 D (a % M) (b % M) % M = 0 := by
    have := W1_modEq (D := D) (Int.mod_modEq a M) (Int.mod_modEq b M)
    rw [this]; exact Int.emod_eq_zero_of_dvd h1
  have e2 : W2 D (a % M) (b % M) % M = 0 := by
    have := W2_modEq (D := D) (Int.mod_modEq a M) (Int.mod_modEq b M)
    rw [this]; exact Int.emod_eq_zero_of_dvd h2
  simp only [← hMdef, e1, e2, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, decide_eq_true_eq] at h'
  have hjM : (j : ℤ) ∣ M := ⟨(j : ℤ) ^ 2, by rw [hMdef]; ring⟩
  refine ⟨?_, ?_⟩
  · have := Int.emod_add_ediv a M
    rw [← this]
    exact dvd_add (Int.dvd_of_emod_eq_zero h'.1) (dvd_mul_of_dvd_left hjM _)
  · have := Int.emod_add_ediv b M
    rw [← this]
    exact dvd_add (Int.dvd_of_emod_eq_zero h'.2) (dvd_mul_of_dvd_left hjM _)

/-! ### The table -/

/-- The class-group certificate: every `p^2 + D q^2 = k^3` with `1 ≤ k ≤ K`, `|q| ≤ Q` has
`q = 0`, `k = j^2`, and `divB D j`. -/
def tableB (D : ℤ) (K Q : ℕ) : Bool :=
  (List.range K).all fun i => (List.range (2 * Q + 1)).all fun iq =>
    let k : ℤ := (i : ℤ) + 1
    let q : ℤ := (iq : ℤ) - Q
    let t := k ^ 3 - D * q ^ 2
    let s := isqrtZ t
    decide (t < 0) ||
      (decide (0 ≤ s ∧ s * s ≤ t ∧ t < (s + 1) * (s + 1)) &&
        (!decide (s * s = t) ||
          (decide (q = 0) && decide ((nsqrt (i + 1) : ℤ) * nsqrt (i + 1) = k) &&
            divB D (nsqrt (i + 1)))))

lemma table_sound {D : ℤ} {K Q : ℕ} (h : tableB D K Q = true) (k q p : ℤ) (hk1 : 1 ≤ k)
    (hkK : k ≤ K) (hq : |q| ≤ Q) (hp : p ^ 2 + D * q ^ 2 = k ^ 3) :
    q = 0 ∧ ∃ j : ℕ, 0 < j ∧ (j : ℤ) ^ 2 = k ∧ divB D j = true := by
  unfold tableB at h
  rw [List.all_eq_true] at h
  have hi : (k - 1).toNat ∈ List.range K := by rw [List.mem_range]; omega
  have hq' := abs_le.mp hq
  have hiq : (q + Q).toNat ∈ List.range (2 * Q + 1) := by rw [List.mem_range]; omega
  have h' := (List.all_eq_true.mp (h _ hi)) _ hiq
  have hkc : (((k - 1).toNat : ℕ) : ℤ) + 1 = k := by omega
  have hqc : (((q + Q).toNat : ℕ) : ℤ) - Q = q := by omega
  have hnat : (k - 1).toNat + 1 = k.toNat := by omega
  simp only [hkc, hqc, hnat] at h'
  have ht : k ^ 3 - D * q ^ 2 = p ^ 2 := by linarith
  rw [ht] at h'
  generalize isqrtZ (p ^ 2) = s at h'
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at h'
  rcases h' with hneg | ⟨⟨hs0, hs1, hs2⟩, hrest⟩
  · nlinarith [sq_nonneg p]
  have hsp : s * s = p ^ 2 := by
    have habs : |p| ^ 2 = p ^ 2 := sq_abs p
    have h1 : s ≤ |p| := by
      by_contra hc; push_neg at hc
      have : |p| * |p| < s * s := mul_self_lt_mul_self (abs_nonneg p) hc
      nlinarith
    have h2 : |p| < s + 1 := by
      by_contra hc; push_neg at hc
      have : (s + 1) * (s + 1) ≤ |p| * |p| := mul_self_le_mul_self (by linarith) hc
      nlinarith
    have : s = |p| := by omega
    rw [this, ← habs]; ring
  rcases hrest with hns | ⟨⟨hq0, hjk⟩, hdiv⟩
  · exact absurd hsp hns
  refine ⟨hq0, nsqrt k.toNat, ?_, ?_, hdiv⟩
  · rcases Nat.eq_zero_or_pos (nsqrt k.toNat) with h0 | h0
    · rw [h0] at hjk; push_cast at hjk; omega
    · exact h0
  · rw [sq]; exact hjk

/-! ### The descent -/

/-- **The generalized template.**  Under the certificate, `y + √-D` is a cube. -/
theorem cube_of_cert (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K Q : ℕ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < ((K : ℤ) + 1) * r * t)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (htab : tableB D K Q = true) (x y : ℤ)
    (h : y ^ 2 + D = x ^ 3) :
    ∃ p q : ℤ, y = p ^ 3 - 3 * D * p * q ^ 2 ∧ 1 = 3 * p ^ 2 * q - D * q ^ 3 := by
  have hx : 0 < x := by
    by_contra hc
    push_neg at hc
    have : x ^ 3 ≤ 0 := Odd.pow_nonpos (⟨1, rfl⟩ : Odd 3) hc
    nlinarith [sq_nonneg y]
  obtain ⟨a, b, k, e1, e2, hk1, hkK, hnorm, hre, him⟩ :=
    short_relation D hD r t hr ht K hK x y h hx
  have hk3 : k ^ 3 ≤ (K : ℤ) ^ 3 := pow_le_pow_left₀ (by linarith) hkK 3
  have hq : |e2| ≤ Q := by
    have h1 : D * e2 ^ 2 < D * ((Q : ℤ) + 1) ^ 2 := by nlinarith [sq_nonneg e1]
    have h2 : e2 ^ 2 < ((Q : ℤ) + 1) ^ 2 := lt_of_mul_lt_mul_left h1 hD.le
    have h3 := abs_lt_of_sq_lt_sq' h2 (by positivity)
    rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
  obtain ⟨rfl, j, hj0, hjk, hdiv⟩ := table_sound htab k e2 e1 hk1 hkK hq hnorm
  have hdivOK := divOK_of_divB D j hj0 hdiv
  set J : ℤ := (j : ℤ) with hJdef
  have hJ3 : J ^ 3 ≠ 0 := pow_ne_zero 3 (by rw [hJdef]; exact_mod_cast hj0.ne')
  rw [← hjk] at hnorm hre him
  have he : e1 = J ^ 3 ∨ e1 = -J ^ 3 := by
    have : e1 ^ 2 = (J ^ 3) ^ 2 := by linear_combination hnorm
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  rcases he with rfl | rfl
  · have hw1 : W1 D a b = J ^ 3 * y := mul_left_cancel₀ hJ3 (by linear_combination -hre)
    have hw2 : W2 D a b = J ^ 3 * (-1) := mul_left_cancel₀ hJ3 (by linear_combination him)
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hdivOK a b ⟨y, hw1⟩ ⟨-1, hw2⟩
    have w1 : W1 D (J * a') (J * b') = J ^ 3 * W1 D a' b' := by simp only [W1]; ring
    have w2 : W2 D (J * a') (J * b') = J ^ 3 * W2 D a' b' := by simp only [W2]; ring
    rw [w1] at hw1; rw [w2] at hw2
    have e1' := mul_left_cancel₀ hJ3 hw1
    have e2' := mul_left_cancel₀ hJ3 hw2
    simp only [W1, W2] at e1' e2'
    exact ⟨a', b', by linear_combination -e1', by linear_combination e2'⟩
  · have hw1 : W1 D a b = J ^ 3 * (-y) := mul_left_cancel₀ hJ3 (by linear_combination hre)
    have hw2 : W2 D a b = J ^ 3 * 1 := mul_left_cancel₀ hJ3 (by linear_combination -him)
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hdivOK a b ⟨-y, hw1⟩ ⟨1, hw2⟩
    have w1 : W1 D (J * a') (J * b') = J ^ 3 * W1 D a' b' := by simp only [W1]; ring
    have w2 : W2 D (J * a') (J * b') = J ^ 3 * W2 D a' b' := by simp only [W2]; ring
    rw [w1] at hw1; rw [w2] at hw2
    have e1' := mul_left_cancel₀ hJ3 hw1
    have e2' := mul_left_cancel₀ hJ3 hw2
    simp only [W1, W2] at e1' e2'
    exact ⟨-a', -b', by linear_combination e1', by linear_combination -e2'⟩

/-- **Every point comes from `3 p^2 - D = ± 1`**: `x = p^2 + D`, `y = p^3 - 3 D p`. -/
theorem points_of_cert (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K Q : ℕ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < ((K : ℤ) + 1) * r * t)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (htab : tableB D K Q = true) (x y : ℤ)
    (h : y ^ 2 = x ^ 3 - D) :
    ∃ p : ℤ, (3 * p ^ 2 - D = 1 ∨ 3 * p ^ 2 - D = -1) ∧ x = p ^ 2 + D ∧ y = p ^ 3 - 3 * D * p := by
  obtain ⟨p, q, hy, h1⟩ := cube_of_cert D hD r t hr ht K Q hK hQ htab x y (by linarith)
  have hq : q * (3 * p ^ 2 - D * q ^ 2) = 1 := by linear_combination -h1
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hq with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · refine ⟨p, Or.inl (by linear_combination h2), cube_inj ?_, by linear_combination hy⟩
    linear_combination (-1) * h + (y + (p ^ 3 - 3 * D * p)) * hy - D * (3 * p ^ 2 - D + 1) * h2
  · refine ⟨p, Or.inr (by linear_combination h2), cube_inj ?_, by linear_combination hy⟩
    linear_combination (-1) * h + (y + (p ^ 3 - 3 * D * p)) * hy - D * (3 * p ^ 2 - D - 1) * h2

/-- The candidate points: `(p^2 + D, p^3 - 3 D p)` for `|p| ≤ D + 1` with `3 p^2 - D = ± 1`. -/
def pointList (D : ℤ) : List (ℤ × ℤ) :=
  ((List.range (2 * D.toNat + 3)).map fun i : ℕ => (i : ℤ) - (D + 1)).filterMap fun p =>
    if 3 * p ^ 2 - D = 1 ∨ 3 * p ^ 2 - D = -1 then some (p ^ 2 + D, p ^ 3 - 3 * D * p) else none

/-- Every listed point is on the curve (no certificate needed). -/
lemma pointList_sound {D x y : ℤ} (h : (x, y) ∈ pointList D) : y ^ 2 = x ^ 3 - D := by
  obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp h
  split_ifs at hp with hc
  · simp only [Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rcases hc with hc | hc
    · linear_combination (-D * (3 * p ^ 2 - D + 1)) * hc
    · linear_combination (-D * (3 * p ^ 2 - D - 1)) * hc

/-- **The complete list of integral points** of `y^2 = x^3 - D`, from the certificate. -/
theorem complete_of_cert (D : ℤ) (hD : 0 < D) (r t : ℕ) (hr : 0 < r) (ht : 0 < t) (K Q : ℕ)
    (hK : (r : ℤ) ^ 2 + D * (t : ℤ) ^ 2 < ((K : ℤ) + 1) * r * t)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (htab : tableB D K Q = true) (x y : ℤ) :
    y ^ 2 = x ^ 3 - D ↔ (x, y) ∈ pointList D := by
  refine ⟨fun h => ?_, pointList_sound⟩
  obtain ⟨p, hc, rfl, rfl⟩ := points_of_cert D hD r t hr ht K Q hK hQ htab x y h
  have hp2 : 3 * p ^ 2 ≤ D + 1 := by rcases hc with hc | hc <;> linarith
  have hpb : -(D + 1) ≤ p ∧ p ≤ D + 1 := by constructor <;> nlinarith [sq_nonneg (p + 1), sq_nonneg (p - 1)]
  refine List.mem_filterMap.mpr ⟨p, List.mem_map.mpr ⟨(p + D + 1).toNat, ?_, ?_⟩, ?_⟩
  · rw [List.mem_range]; omega
  · omega
  · dsimp only; rw [if_pos hc]

/-! ### The bridge to the compiler's premise -/

/-- **A complete list for `m^2 = t^3 + k` discharges the image premise** of every constraint
`m^2 = (r n + s)^3 + k`, written as `a n^3 + b n^2 + c n + e`. -/
theorem image_of_complete {k : ℤ} {L : List (ℤ × ℤ)} (hL : ∀ t m : ℤ, m ^ 2 = t ^ 3 + k → (t, m) ∈ L)
    (r s : ℤ) (hr : r ≠ 0) (a b c e : ℤ) (ha : a = r ^ 3) (hb : b = 3 * r ^ 2 * s)
    (hc : c = 3 * r * s ^ 2) (he : e = s ^ 3 + k) :
    Transport.IntegralPointsOnImage a b (Genus1.cubicModel a b c e).1 (Genus1.cubicModel a b c e).2
      (L.map fun p => (9 * r ^ 2 * p.1, 27 * r ^ 3 * p.2)) := by
  intro U V hUV ⟨n, hn⟩ ⟨m, hm⟩
  subst ha hb hc he
  simp only [Genus1.cubicModel] at hUV
  have hU : U = 9 * r ^ 2 * (r * n + s) := by linear_combination hn
  have hV : V = 27 * r ^ 3 * m := by linear_combination hm
  rw [hU, hV] at hUV
  have h729 : (729 * r ^ 6) * m ^ 2 = (729 * r ^ 6) * ((r * n + s) ^ 3 + k) := by
    linear_combination hUV
  have hr6 : (729 * r ^ 6) ≠ 0 := by positivity
  have hpt := hL _ _ (mul_left_cancel₀ hr6 h729)
  exact List.mem_map.mpr ⟨_, hpt, by rw [hU, hV]⟩

/-- **End to end**: a descent certificate for `D` and a checked pull-back give the complete hit
set of `m^2 = (r n + s)^3 - D`. -/
theorem hits_of_cert (D : ℤ) (hD : 0 < D) (r₀ t₀ : ℕ) (hr₀ : 0 < r₀) (ht₀ : 0 < t₀) (K Q : ℕ)
    (hK : (r₀ : ℤ) ^ 2 + D * (t₀ : ℤ) ^ 2 < ((K : ℤ) + 1) * r₀ * t₀)
    (hQ : (K : ℤ) ^ 3 < D * ((Q : ℤ) + 1) ^ 2) (htab : tableB D K Q = true)
    (r s : ℤ) (hr : r ≠ 0) (a b c e : ℤ) (ha : a = r ^ 3) (hb : b = 3 * r ^ 2 * s)
    (hc : c = 3 * r * s ^ 2) (he : e = s ^ 3 - D) (hits : List (ℕ × ℤ))
    (hok : Genus1.cubicOK a b c e
      ((pointList D).map fun p => (9 * r ^ 2 * p.1, 27 * r ^ 3 * p.2)) hits = true)
    (n : ℕ) (hn : 1 ≤ n) :
    IsHit 2 (Reflect.ev [e, c, b, a] n) ↔ n ∈ hits.map Prod.fst :=
  Transport.cubic_sound_image
    (image_of_complete (k := -D)
      (fun t m h => (complete_of_cert D hD r₀ t₀ hr₀ ht₀ K Q hK hQ htab t m).mp (by linarith))
      r s hr a b c e ha hb hc (by rw [he]; ring)) hok n hn

end PerfectPower.Descent
