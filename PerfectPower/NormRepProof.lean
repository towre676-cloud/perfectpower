import PerfectPower.UnitPremises
import Mathlib.Data.ZMod.Basic

/-!
# Norm representatives by explicit division

`UnitPremises.NormRep P Q N [γ₀]` says every element of `ℤ[x]` (`x³ = Px + Q`) of norm `N` is `γ₀`
times a unit.  For the two fields in use it is proved here in integer coordinates, with no maximal
order or ideal factorization:

* **Adjugate** (`mul_adj`): `g · g# = N(g)`, so an element of norm `±1` is a unit with an explicit
  inverse (`unit_of_nrm`); the norm is multiplicative (`nrm_mul`).
* **Field 1944** (`x³ = 9x + 6`): if `9 ∣ N(g)` then `3 ∣ A` and `3 ∣ B` (a check over `ZMod 9`),
  and `g / α` with `α = x² − 3x − 3` is integral (`d72_div`).  So every `g` of norm `9` is `α u`,
  `N(u) = 1`: `normRep_d72`.
* **Field 756** (`x³ = 6x + 2`): `2 ∣ N(g)` gives `x ∣ g`, and `3 ∣ N(g)` gives `(1 + x) ∣ g`
  (checks over `ZMod 2`, `ZMod 3`).  Induction gives `g = x^r (1 + x)^s u` with `N(u) = ±1`
  whenever `N(g) = ±2^r 3^s` (`decomp756`), and comparing with `γ₀` gives `normRep756`.
-/

namespace PerfectPower.NormRepProof

open PerfectPower UnitBox UnitPremises

/-! ### Generic algebra in `ℤ[x]` -/

/-- The adjugate: `g · g# = N(g)`. -/
def adj (P Q : ℤ) (g : Z3) : Z3 :=
  let (A, B, C) := g
  ((A + P * C) ^ 2 - (P * B + Q * C) * B, Q * C ^ 2 - A * B, B ^ 2 - A * C - P * C ^ 2)

lemma mul_adj (P Q : ℤ) (g : Z3) : mul P Q g (adj P Q g) = (nrm P Q g, 0, 0) := by
  obtain ⟨A, B, C⟩ := g
  simp only [mul, adj, nrm, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

lemma nrm_mul (P Q : ℤ) (x y : Z3) : nrm P Q (mul P Q x y) = nrm P Q x * nrm P Q y := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  simp only [nrm, mul]
  ring

lemma mul_comm' (P Q : ℤ) (x y : Z3) : mul P Q x y = mul P Q y x := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨d, e, f⟩ := y
  simp only [mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

lemma one_mul' (P Q : ℤ) (x : Z3) : mul P Q (1, 0, 0) x = x := by
  obtain ⟨a, b, c⟩ := x
  simp [mul]

lemma nrm_one (P Q : ℤ) : nrm P Q (1, 0, 0) = 1 := by simp [nrm]

/-- **An element of norm `±1` is a unit**, with inverse `±g#`. -/
lemma unit_of_nrm {P Q : ℤ} {g : Z3} (h : nrm P Q g = 1 ∨ nrm P Q g = -1) :
    ∃ v, mul P Q g v = (1, 0, 0) := by
  rcases h with h | h
  · exact ⟨adj P Q g, by rw [mul_adj, h]⟩
  · refine ⟨neg (adj P Q g), ?_⟩
    rw [mul_neg', mul_adj, h]
    simp [neg]

/-- The norm over any commutative ring (for residue checks). -/
def nrmR {R : Type*} [CommRing R] (P Q a b c : R) : R :=
  a * ((a + P * c) * (a + P * c) - (P * b + Q * c) * b) - Q * c * (b * (a + P * c) - (P * b + Q * c) * c) +
    Q * b * (b * b - (a + P * c) * c)

lemma nrm_cast {n : ℕ} (P Q A B C : ℤ) :
    ((nrm P Q (A, B, C) : ℤ) : ZMod n) = nrmR (P : ZMod n) Q A B C := by
  simp only [nrm, nrmR]
  push_cast
  ring

lemma val_mod {n : ℕ} [NeZero n] (A : ℤ) : (((A : ZMod n).val : ℕ) : ℤ) = A % n := ZMod.val_intCast A

/-! ### Field 1944: `x³ = 9x + 6`, `α = x² − 3x − 3`, `N(α) = 9` -/

/-- `9 ∣ N(g)` forces `3 ∣ A` and `3 ∣ B` (all `729` residues modulo `9`). -/
lemma d72_res : ∀ x y z : ZMod 9, nrmR 9 6 x y z = 0 → x.val % 3 = 0 ∧ y.val % 3 = 0 := by
  decide

lemma d72_mod (A B C : ℤ) (h : (9 : ℤ) ∣ nrm 9 6 (A, B, C)) : (3 : ℤ) ∣ A ∧ (3 : ℤ) ∣ B := by
  have hc : ((nrm 9 6 (A, B, C) : ℤ) : ZMod 9) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr h
  rw [nrm_cast] at hc
  have := d72_res _ _ _ (by simpa using hc)
  have ha := val_mod (n := 9) A
  have hb := val_mod (n := 9) B
  omega

/-- **Division by `α`.** -/
lemma d72_div (g : Z3) (h : nrm 9 6 g = 9) :
    ∃ u, g = mul 9 6 (-3, -3, 1) u ∧ nrm 9 6 u = 1 := by
  obtain ⟨A, B, C⟩ := g
  obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := d72_mod A B C (by rw [h])
  refine ⟨(-9 * a + 6 * b - 2 * C, -a - C, a - b), ?_, ?_⟩
  · simp only [mul, Prod.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  · have e : (3 * a, 3 * b, C) = mul 9 6 (-3, -3, 1) (-9 * a + 6 * b - 2 * C, -a - C, a - b) := by
      simp only [mul, Prod.mk.injEq]
      refine ⟨by ring, by ring, by ring⟩
    rw [e, nrm_mul] at h
    have h9 : nrm 9 6 ((-3, -3, 1) : Z3) = 9 := by decide
    rw [h9] at h
    omega

/-- **`NormRep` for norm `9` in the field 1944.** -/
theorem normRep_d72 : NormRep 9 6 9 [(-3, -3, 1)] := by
  intro g hg
  obtain ⟨u, hu, hn⟩ := d72_div g hg
  obtain ⟨v, hv⟩ := unit_of_nrm (Or.inl hn)
  exact ⟨(-3, -3, 1), List.mem_singleton_self _, u, v, hv, hu⟩

/-! ### Field 756: `x³ = 6x + 2`, `π₂ = x` (norm `2`), `π₃ = 1 + x` (norm `−3`) -/

/-- `2 ∣ N(g)` forces `2 ∣ A`. -/
lemma f756_res2 : ∀ x y z : ZMod 2, nrmR 6 2 x y z = 0 → x.val % 2 = 0 := by decide

/-- `3 ∣ N(g)` forces `3 ∣ A − B + C`. -/
lemma f756_res3 : ∀ x y z : ZMod 3, nrmR 6 2 x y z = 0 → (x.val + 2 * y.val + z.val) % 3 = 0 := by
  decide

/-- **Division by `x`.** -/
lemma div2 (g : Z3) (h : (2 : ℤ) ∣ nrm 6 2 g) : ∃ u, g = mul 6 2 (0, 1, 0) u := by
  obtain ⟨A, B, C⟩ := g
  have hc : ((nrm 6 2 (A, B, C) : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h
  rw [nrm_cast] at hc
  have := f756_res2 _ _ _ (by simpa using hc)
  have ha := val_mod (n := 2) A
  obtain ⟨a, rfl⟩ : (2 : ℤ) ∣ A := by omega
  refine ⟨(B - 6 * a, C, a), ?_⟩
  simp only [mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- **Division by `1 + x`.** -/
lemma div3 (g : Z3) (h : (3 : ℤ) ∣ nrm 6 2 g) : ∃ u, g = mul 6 2 (1, 1, 0) u := by
  obtain ⟨A, B, C⟩ := g
  have hc : ((nrm 6 2 (A, B, C) : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h
  rw [nrm_cast] at hc
  have := f756_res3 _ _ _ (by simpa using hc)
  have ha := val_mod (n := 3) A
  have hb := val_mod (n := 3) B
  have hcc := val_mod (n := 3) C
  obtain ⟨k, hk⟩ : (3 : ℤ) ∣ A - B + C := by omega
  refine ⟨(A + 2 * k, C + k, -k), ?_⟩
  have hB : B = A + C - 3 * k := by linarith
  subst hB
  simp only [mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- `x^r (1 + x)^s`. -/
def beta (r s : ℕ) : Z3 := mul 6 2 (pow 6 2 (0, 1, 0) r) (pow 6 2 (1, 1, 0) s)

lemma beta_succ_r (r s : ℕ) : beta (r + 1) s = mul 6 2 (0, 1, 0) (beta r s) := by
  simp only [beta, pow]
  rw [mul_comm' 6 2 (pow 6 2 _ r) (0, 1, 0), mul_assoc']

lemma beta_succ_s (r s : ℕ) : beta r (s + 1) = mul 6 2 (1, 1, 0) (beta r s) := by
  simp only [beta, pow]
  rw [mul_comm' 6 2 (pow 6 2 _ s) (1, 1, 0), ← mul_assoc', mul_comm' 6 2 (pow 6 2 _ r) (1, 1, 0),
    mul_assoc']

/-- **Factorization**: `N(g) = ±2^r 3^s` gives `g = x^r (1 + x)^s u`, `N(u) = ±1`. -/
lemma decomp756 : ∀ (r s : ℕ) (g : Z3), (nrm 6 2 g = 2 ^ r * 3 ^ s ∨ nrm 6 2 g = -(2 ^ r * 3 ^ s)) →
    ∃ u, g = mul 6 2 (beta r s) u ∧ (nrm 6 2 u = 1 ∨ nrm 6 2 u = -1)
  | 0, 0, g, h => ⟨g, by simp [beta, pow, one_mul'], by simpa using h⟩
  | r + 1, s, g, h => by
    have e : (2 : ℤ) ^ (r + 1) * 3 ^ s = 2 * (2 ^ r * 3 ^ s) := by ring
    rw [e] at h
    obtain ⟨g', rfl⟩ := div2 g (by
      rcases h with h | h <;> rw [h]
      · exact ⟨2 ^ r * 3 ^ s, rfl⟩
      · exact ⟨-(2 ^ r * 3 ^ s), by ring⟩)
    have h2 : nrm 6 2 ((0, 1, 0) : Z3) = 2 := by decide
    rw [nrm_mul, h2] at h
    obtain ⟨u, hu, hn⟩ := decomp756 r s g' (by
      rcases h with h | h
      · left; linarith
      · right; linarith)
    exact ⟨u, by rw [hu, beta_succ_r, mul_assoc'], hn⟩
  | 0, s + 1, g, h => by
    have e : (2 : ℤ) ^ 0 * 3 ^ (s + 1) = 3 * (2 ^ 0 * 3 ^ s) := by ring
    rw [e] at h
    obtain ⟨g', rfl⟩ := div3 g (by
      rcases h with h | h <;> rw [h]
      · exact ⟨2 ^ 0 * 3 ^ s, rfl⟩
      · exact ⟨-(2 ^ 0 * 3 ^ s), by ring⟩)
    have h3 : nrm 6 2 ((1, 1, 0) : Z3) = -3 := by decide
    rw [nrm_mul, h3] at h
    obtain ⟨u, hu, hn⟩ := decomp756 0 s g' (by
      rcases h with h | h
      · right; linarith
      · left; linarith)
    exact ⟨u, by rw [hu, beta_succ_s, mul_assoc'], hn⟩

/-- **`NormRep` for every norm `±2^r 3^s` in the field 756**, with any representative `γ₀` of
that norm. -/
theorem normRep756 (N : ℤ) (g0 : Z3) (r s : ℕ) (hN : N = 2 ^ r * 3 ^ s ∨ N = -(2 ^ r * 3 ^ s))
    (hg0 : nrm 6 2 g0 = N) : NormRep 6 2 N [g0] := by
  intro g hg
  obtain ⟨u, hu, hnu⟩ := decomp756 r s g (by rw [hg]; exact hN)
  obtain ⟨v, hv, hnv⟩ := decomp756 r s g0 (by rw [hg0]; exact hN)
  obtain ⟨v', hvv'⟩ := unit_of_nrm hnv
  have hnv' : nrm 6 2 v' = 1 ∨ nrm 6 2 v' = -1 := by
    have := congrArg (nrm 6 2) hvv'
    rw [nrm_mul, nrm_one] at this
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hw : nrm 6 2 (mul 6 2 v' u) = 1 ∨ nrm 6 2 (mul 6 2 v' u) = -1 := by
    rw [nrm_mul]
    rcases hnv' with h1 | h1 <;> rcases hnu with h2 | h2 <;> rw [h1, h2] <;> norm_num
  obtain ⟨w, hw'⟩ := unit_of_nrm hw
  refine ⟨g0, List.mem_singleton_self _, mul 6 2 v' u, w, hw', ?_⟩
  rw [hv, mul_assoc', ← mul_assoc' 6 2 v v' u, hvv', one_mul', hu]

end PerfectPower.NormRepProof
