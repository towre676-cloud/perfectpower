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

/-- **Norm `1`**: every element of norm `1` is `1 · unit` (the adjugate is its inverse), so a unit
equation needs no norm-representative search. -/
theorem normRep_one (P Q : ℤ) : NormRep P Q 1 [(1, 0, 0)] := by
  intro g hg
  obtain ⟨v, hv⟩ := unit_of_nrm (Or.inl hg)
  exact ⟨(1, 0, 0), List.mem_singleton_self _, g, v, hv, (one_mul' P Q g).symm⟩

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

/-! ### Norm representatives from a residue check

For a target `N` and representatives `γ` of norm `±N`: if every residue class `r` modulo `m`
(`N ∣ m`) with `N(r) ≡ N` has some `γ` with `γ# r ≡ 0 (mod N(γ))`, then every `g` of norm `N` is
`γ` times a unit.  The quotient is `u = g γ# / N(γ)`: integral by the congruence, `γ u = g`, and
`N(u) = N/N(γ) = ±1`.  Nothing about class numbers or ideals is used. -/

/-- The residue certificate. -/
def resRepB (P Q N : ℤ) (m : ℕ) (reps : List Z3) : Bool :=
  decide (0 < m) && decide ((m : ℤ) % N = 0) &&
  reps.all (fun γ => decide (nrm P Q γ = N ∨ nrm P Q γ = -N)) &&
  (List.range m).all fun a => (List.range m).all fun b => (List.range m).all fun c =>
    decide (nrm P Q ((a : ℤ), (b : ℤ), (c : ℤ)) % m ≠ N % m) || reps.any fun γ =>
      decide ((mul P Q ((a : ℤ), (b : ℤ), (c : ℤ)) (adj P Q γ)).1 % nrm P Q γ = 0 ∧
        (mul P Q ((a : ℤ), (b : ℤ), (c : ℤ)) (adj P Q γ)).2.1 % nrm P Q γ = 0 ∧
        (mul P Q ((a : ℤ), (b : ℤ), (c : ℤ)) (adj P Q γ)).2.2 % nrm P Q γ = 0)

lemma cast_mul_eq {m : ℕ} {P Q A B C a b c : ℤ} (hA : (A : ZMod m) = a) (hB : (B : ZMod m) = b)
    (hC : (C : ZMod m) = c) (X : Z3) :
    ((mul P Q (A, B, C) X).1 : ZMod m) = (mul P Q (a, b, c) X).1 ∧
    ((mul P Q (A, B, C) X).2.1 : ZMod m) = (mul P Q (a, b, c) X).2.1 ∧
    ((mul P Q (A, B, C) X).2.2 : ZMod m) = (mul P Q (a, b, c) X).2.2 := by
  obtain ⟨x, y, z⟩ := X
  simp only [mul]
  push_cast
  rw [hA, hB, hC]
  exact ⟨rfl, rfl, rfl⟩

lemma mul_smul3 (P Q d : ℤ) (g u : Z3) :
    mul P Q g (d * u.1, d * u.2.1, d * u.2.2) =
      (d * (mul P Q g u).1, d * (mul P Q g u).2.1, d * (mul P Q g u).2.2) := by
  obtain ⟨a, b, c⟩ := g
  obtain ⟨x, y, z⟩ := u
  simp only [mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

lemma nrm_smul3 (P Q d : ℤ) (u : Z3) : nrm P Q (d * u.1, d * u.2.1, d * u.2.2) = d ^ 3 * nrm P Q u := by
  obtain ⟨x, y, z⟩ := u
  simp only [nrm]; ring

/-- **Norm representatives from a residue certificate.** -/
theorem normRep_of_res {P Q N : ℤ} {m : ℕ} {reps : List Z3} (hN : N ≠ 0)
    (h : resRepB P Q N m reps = true) : NormRep P Q N reps := by
  simp only [resRepB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨hm, hmN⟩, hreps⟩, hres⟩ := h
  intro g hg
  obtain ⟨A, B, C⟩ := g
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  set a := (A % m).toNat
  set b := (B % m).toNat
  set c := (C % m).toNat
  have ea : ((a : ℕ) : ℤ) = A % m := Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne')
  have eb : ((b : ℕ) : ℤ) = B % m := Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne')
  have ec : ((c : ℕ) : ℤ) = C % m := Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne')
  have la : a < m := by have := Int.emod_lt_of_pos A hm'; omega
  have lb : b < m := by have := Int.emod_lt_of_pos B hm'; omega
  have lc : c < m := by have := Int.emod_lt_of_pos C hm'; omega
  have hA : (A : ZMod m) = ((a : ℤ) : ZMod m) := by
    rw [ea, ZMod.intCast_mod]
  have hB : (B : ZMod m) = ((b : ℤ) : ZMod m) := by rw [eb, ZMod.intCast_mod]
  have hC : (C : ZMod m) = ((c : ℤ) : ZMod m) := by rw [ec, ZMod.intCast_mod]
  -- the norm modulo m
  have hn : nrm P Q ((a : ℤ), (b : ℤ), (c : ℤ)) % m = N % m := by
    have h1 : ((nrm P Q (A, B, C) : ℤ) : ZMod m) = ((nrm P Q ((a : ℤ), (b : ℤ), (c : ℤ)) : ℤ) : ZMod m) := by
      rw [nrm_cast, nrm_cast, hA, hB, hC]
    rw [hg] at h1
    exact ((ZMod.intCast_eq_intCast_iff' _ _ _).mp h1).symm
  obtain ⟨γ, hγ, hdiv⟩ := (hres a la b lb c lc).resolve_left (by simpa using hn)
  obtain ⟨d1, d2, d3⟩ := hdiv
  set d := nrm P Q γ with hd
  have hdN : d = N ∨ d = -N := hreps γ hγ
  have hd0 : d ≠ 0 := by rcases hdN with h | h <;> rw [h] <;> simpa using hN
  have hdm : d ∣ (m : ℤ) := by
    rcases hdN with h | h <;> rw [h]
    · exact Int.dvd_of_emod_eq_zero hmN
    · exact (neg_dvd).mpr (Int.dvd_of_emod_eq_zero hmN)
  -- the product `g γ#` modulo m, then modulo d
  obtain ⟨c1, c2, c3⟩ := cast_mul_eq (P := P) (Q := Q) hA hB hC (adj P Q γ)
  have tr : ∀ {x y : ℤ}, (x : ZMod m) = (y : ZMod m) → y % d = 0 → d ∣ x := by
    intro x y hxy hy
    have := (ZMod.intCast_eq_intCast_iff' _ _ _).mp hxy
    have hxy' : x ≡ y [ZMOD m] := this
    have h1 : d ∣ y - x := dvd_trans hdm hxy'.dvd
    have h2 : d ∣ y := Int.dvd_of_emod_eq_zero hy
    have := dvd_sub h2 h1
    rwa [sub_sub_cancel] at this
  set q := mul P Q (A, B, C) (adj P Q γ)
  obtain ⟨k1, hk1⟩ := tr c1 d1
  obtain ⟨k2, hk2⟩ := tr c2 d2
  obtain ⟨k3, hk3⟩ := tr c3 d3
  set u : Z3 := (k1, k2, k3)
  have hq : q = (d * u.1, d * u.2.1, d * u.2.2) := by
    simp only [u]; exact Prod.ext hk1 (Prod.ext hk2 hk3)
  -- γ u = g
  have hγu : mul P Q γ u = (A, B, C) := by
    have e1 : mul P Q γ q = (d * A, d * B, d * C) := by
      simp only [q]
      rw [← mul_assoc' P Q γ (A, B, C) (adj P Q γ), mul_comm' P Q γ (A, B, C),
        mul_assoc' P Q (A, B, C) γ (adj P Q γ), mul_adj]
      simp only [mul, Prod.mk.injEq]
      refine ⟨by ring, by ring, by ring⟩
    rw [hq, mul_smul3] at e1
    simp only [Prod.mk.injEq] at e1
    obtain ⟨f1, f2, f3⟩ := e1
    exact Prod.ext (mul_left_cancel₀ hd0 f1) (Prod.ext (mul_left_cancel₀ hd0 f2) (mul_left_cancel₀ hd0 f3))
  -- N(u) = ±1
  have hadj : nrm P Q (adj P Q γ) = d ^ 2 := by
    have := nrm_mul P Q γ (adj P Q γ)
    rw [mul_adj] at this
    have h3 : nrm P Q (d, 0, 0) = d ^ 3 := by simp only [nrm]; ring
    rw [h3] at this
    have : d * (nrm P Q (adj P Q γ) - d ^ 2) = 0 := by rw [← hd] at this; linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hd0
    · linarith
  have hnu : d * nrm P Q u = N := by
    have e := nrm_mul P Q (A, B, C) (adj P Q γ)
    rw [hadj, hg] at e
    have e' : nrm P Q q = d ^ 3 * nrm P Q u := by rw [hq, nrm_smul3]
    have : d ^ 2 * (d * nrm P Q u - N) = 0 := by
      have : nrm P Q q = N * d ^ 2 := e
      rw [e'] at this; linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hd0
    · linarith
  have hu : nrm P Q u = 1 ∨ nrm P Q u = -1 := by
    rcases hdN with h | h
    · left; rw [h] at hnu; exact (mul_right_eq_self₀.mp (by linarith)).resolve_right hN
    · right; rw [h] at hnu
      have : N * (nrm P Q u + 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hN
      · linarith
  obtain ⟨v, hv⟩ := unit_of_nrm hu
  exact ⟨γ, hγ, u, v, hv, hγu.symm⟩

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
