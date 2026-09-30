import Mathlib.Data.Int.GCD
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Count
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# A narrow, finished counting module (the first Bilu–Tichy-type sequel)

This does **not** encode the Bilu–Tichy classification.  It proves three finished counting
statements with executable constants, which a classification would feed:

1. **Positive monomial equations** `x^a = y^b` (`monomial_param`, `monomial_count`).  With
   `d = gcd(a, b)`, `a' = a/d`, `b' = b/d`, the positive solutions are exactly
   `(t^{b'}, t^{a'})`, `t ≥ 1`, and in the box `[1, N]^2` there are exactly
   `#{t ≥ 1 : t^{max(a', b')} ≤ N} = ⌊N^{1/max(a',b')}⌋` of them.
2. **Residue-filtered orbit counts** (`filtered_orbit_count`).  For a strictly increasing
   observation `v`, the number of accepted indices (`j mod p ∈ R`) with `v j ≤ N` is an explicit
   sum over the residues of `#{j < J : j ≡ r (mod p)}`, where `J` is the number of indices with
   `v j ≤ N`.  This is exact, not `O(1)`; `Observation.observed_count` gives its asymptotics.
3. **Collisions and a common outer polynomial**.
   - `card_union_collisions`: the values of two observations count with their explicit
     collision set subtracted.
   - `sq_branch_count`: for the outer polynomial `t ↦ t^2`, `F^2 = G^2` splits into the branches
     `F = G` and `F = -G`, which overlap exactly where `F = G = 0`.  The outer polynomial is never
     cancelled.
-/

namespace PerfectPower.MonomialCount

/-! ### Positive monomial equations -/

lemma nat_of_rat_pow {c : ℚ} {n : ℕ} (hn : 0 < n) {x : ℕ} (h : (x : ℚ) = c ^ n) :
    ∃ z : ℤ, c = z := by
  have hden : (c ^ n).den = 1 := by rw [← h]; simp
  rw [Rat.den_pow] at hden
  have : c.den = 1 := (pow_eq_one_iff hn.ne').mp hden
  exact ⟨c.num, (Rat.coe_int_num_of_den_eq_one this).symm⟩

/-- **The positive solutions of `x^a = y^b`.** -/
theorem monomial_param {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    x ^ a = y ^ b ↔
      ∃ t : ℕ, 0 < t ∧ x = t ^ (b / Nat.gcd a b) ∧ y = t ^ (a / Nat.gcd a b) := by
  have hd0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  obtain ⟨a', ha_eq⟩ := Nat.gcd_dvd_left a b
  obtain ⟨b', hb_eq⟩ := Nat.gcd_dvd_right a b
  have hcop : Nat.Coprime (a / Nat.gcd a b) (b / Nat.gcd a b) := Nat.coprime_div_gcd_div_gcd hd0
  have hda : a / Nat.gcd a b = a' := Nat.div_eq_of_eq_mul_left hd0 (by rw [mul_comm]; exact ha_eq)
  have hdb : b / Nat.gcd a b = b' := Nat.div_eq_of_eq_mul_left hd0 (by rw [mul_comm]; exact hb_eq)
  rw [hda, hdb] at hcop ⊢
  have hb'0 : 0 < b' := by rcases Nat.eq_zero_or_pos b' with h | h <;> [simp [h] at hb_eq; exact h]; omega
  set d := Nat.gcd a b
  have eqv : x ^ a = y ^ b ↔ (x ^ a') ^ d = (y ^ b') ^ d := by
    rw [← pow_mul, ← pow_mul, mul_comm a', mul_comm b', ← ha_eq, ← hb_eq]
  rw [eqv]
  constructor
  · intro h
    have h2 : x ^ a' = y ^ b' := Nat.pow_left_injective hd0.ne' h
    have h3 : (x : ℚ) ^ a' = (y : ℚ) ^ b' := by exact_mod_cast h2
    obtain ⟨c, hcx, hcy⟩ := (pow_eq_pow_iff_of_coprime hcop).mp h3
    obtain ⟨z, rfl⟩ := nat_of_rat_pow hb'0 hcx
    have hzx : (x : ℤ) = z ^ b' := by exact_mod_cast hcx
    have hzy : (y : ℤ) = z ^ a' := by exact_mod_cast hcy
    -- `z > 0`: otherwise both exponents are even, against coprimality
    have hz : 0 < z := by
      rcases lt_trichotomy z 0 with hn | h0 | hp
      · have ex : Even b' := by
          rcases Nat.even_or_odd b' with he | ho
          · exact he
          · exfalso
            have : z ^ b' < 0 := Odd.pow_neg ho hn
            omega
        have ey : Even a' := by
          rcases Nat.even_or_odd a' with he | ho
          · exact he
          · exfalso
            have : z ^ a' < 0 := Odd.pow_neg ho hn
            omega
        have h2d : 2 ∣ Nat.gcd a' b' := Nat.dvd_gcd (even_iff_two_dvd.mp ey) (even_iff_two_dvd.mp ex)
        rw [hcop] at h2d; omega
      · subst h0; rw [zero_pow hb'0.ne'] at hzx; omega
      · exact hp
    refine ⟨z.toNat, by omega, ?_, ?_⟩
    · have : ((z.toNat ^ b' : ℕ) : ℤ) = z ^ b' := by push_cast; rw [Int.toNat_of_nonneg hz.le]
      omega
    · have : ((z.toNat ^ a' : ℕ) : ℤ) = z ^ a' := by push_cast; rw [Int.toNat_of_nonneg hz.le]
      omega
  · rintro ⟨t, -, rfl, rfl⟩
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]; congr 1; ring

/-- **The exact count in the box `[1, N]^2`.** -/
theorem monomial_count {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N : ℕ) :
    ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p : ℕ × ℕ => p.1 ^ a = p.2 ^ b)).card =
      ((Finset.Icc 1 N).filter
        (fun t => t ^ max (a / Nat.gcd a b) (b / Nat.gcd a b) ≤ N)).card := by
  set a' := a / Nat.gcd a b
  set b' := b / Nat.gcd a b
  have hd0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have ha' : 0 < a' := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hd0
  have hb' : 0 < b' := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hd0
  have key : ∀ t : ℕ, 1 ≤ t → (t ^ b' ≤ N ∧ t ^ a' ≤ N ↔ t ^ max a' b' ≤ N) := by
    intro t ht
    have m1 : t ^ b' ≤ t ^ max a' b' := Nat.pow_le_pow_right ht (le_max_right _ _)
    have m2 : t ^ a' ≤ t ^ max a' b' := Nat.pow_le_pow_right ht (le_max_left _ _)
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_total a' b' with h | h
      · rwa [max_eq_right h]
      · rwa [max_eq_left h]
    · intro h; exact ⟨m1.trans h, m2.trans h⟩
  symm
  apply Finset.card_bij (fun t _ => (t ^ b', t ^ a'))
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht
    obtain ⟨⟨h1, -⟩, hN⟩ := ht
    obtain ⟨e1, e2⟩ := (key t h1).mpr hN
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨Nat.one_le_pow _ _ h1, e1⟩, ⟨Nat.one_le_pow _ _ h1, e2⟩⟩, ?_⟩
    exact (monomial_param ha hb (Nat.one_le_pow _ _ h1) (Nat.one_le_pow _ _ h1)).mpr ⟨t, h1, rfl, rfl⟩
  · intro t1 _ t2 _ h
    simp only [Prod.mk.injEq] at h
    exact Nat.pow_left_injective hb'.ne' h.1
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hx1, hxN⟩, ⟨hy1, hyN⟩⟩, h⟩ := hp
    obtain ⟨t, ht, hx, hy⟩ := (monomial_param ha hb hx1 hy1).mp h
    refine ⟨t, ?_, Prod.ext hx.symm hy.symm⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hN := (key t ht).mp ⟨hx ▸ hxN, hy ▸ hyN⟩
    refine ⟨⟨ht, ?_⟩, hN⟩
    calc t ≤ t ^ max a' b' := Nat.le_self_pow (by omega) t
      _ ≤ N := hN

/-! ### Residue-filtered orbit counts, exactly -/

/-- **Exact filtered count.**  If exactly the indices `j < J` have `v j ≤ N` (for a strictly
increasing `v`, `J = #{j : v j ≤ N}`), the accepted indices with `v j ≤ N` number
`∑_{r ∈ R} #{j < J : j % p = r}`; each term is `residue_class_count`. -/
theorem filtered_orbit_count (v : ℕ → ℤ) (N : ℤ) (J : ℕ) (hJ : ∀ j, v j ≤ N ↔ j < J) (p : ℕ)
    (R : Finset ℕ) :
    ((Finset.range J).filter (fun j => v j ≤ N ∧ j % p ∈ R)).card =
      ∑ r ∈ R, ((Finset.range J).filter (fun j => j % p = r)).card := by
  rw [← Finset.card_biUnion]
  · congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion]
    constructor
    · rintro ⟨hj, -, hr⟩; exact ⟨_, hr, hj, rfl⟩
    · rintro ⟨r, hr, hj, rfl⟩; exact ⟨hj, (hJ j).mpr hj, hr⟩
  · intro r1 _ r2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact hne (h1.2.symm.trans h2.2)

/-- One residue class below `J`: `#{j < J : j % p = r} = J / p + [r < J % p]` for `r < p`. -/
theorem residue_class_count (J p r : ℕ) (hp : 0 < p) (hr : r < p) :
    ((Finset.range J).filter (fun j => j % p = r)).card = J / p + if r < J % p then 1 else 0 := by
  have := Nat.count_modEq_card J hp r
  rw [Nat.count_eq_card_filter_range, Nat.mod_eq_of_lt hr] at this
  rw [← this]
  congr 1; ext j; simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt hr]

/-! ### Collisions and a common outer polynomial -/

/-- **Distinct values of two observations**: `|A ∪ B| = |A| + |B| - |A ∩ B|`, with the collision
set `A ∩ B` explicit. -/
theorem card_union_collisions {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∪ B).card = A.card + B.card - (A ∩ B).card := by
  rw [← Finset.card_union_add_card_inter A B]; omega

/-- **The outer polynomial `t^2` is not cancelled**: on any finite index set,
`#{F^2 = G^2} = #{F = G} + #{F = -G} - #{F = G = 0}`. -/
theorem sq_branch_count {ι : Type*} [DecidableEq ι] (S : Finset ι) (F G : ι → ℤ) :
    (S.filter fun n => F n ^ 2 = G n ^ 2).card =
      (S.filter fun n => F n = G n).card + (S.filter fun n => F n = -G n).card -
        (S.filter fun n => F n = 0 ∧ G n = 0).card := by
  have hU : (S.filter fun n => F n ^ 2 = G n ^ 2) =
      (S.filter fun n => F n = G n) ∪ (S.filter fun n => F n = -G n) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_union, sq_eq_sq_iff_eq_or_eq_neg]; tauto
  have hI : (S.filter fun n => F n = G n) ∩ (S.filter fun n => F n = -G n) =
      S.filter fun n => F n = 0 ∧ G n = 0 := by
    ext n; simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨⟨h, e1⟩, -, e2⟩; exact ⟨h, by omega, by omega⟩
    · rintro ⟨h, e1, e2⟩; exact ⟨⟨h, by omega⟩, h, by omega⟩
  rw [hU, card_union_collisions, hI]

/-- An executable instance: `x^4 = y^6` in `[1, 1000]^2` has `⌊1000^{1/3}⌋ = 10` solutions. -/
example : ((Finset.Icc 1 1000).filter (fun t => t ^ max (4 / Nat.gcd 4 6) (6 / Nat.gcd 4 6) ≤ 1000)).card
    = 10 := by decide +kernel

end PerfectPower.MonomialCount
