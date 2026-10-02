import PerfectPower.NormRepProof

/-!
# Norm representatives from composable divisor covers

`NormRepProof.normRep_of_res` proves norm representatives for one target `N` from one residue table
of size `m³`, `N ∣ m`.  For a target such as `4096 = 4⁶` that table is out of reach.  This module
composes small tables instead (following the shared-norm-cover review of `6a7bc79`).

* **A divisor cover** (`coverB`, `cover_sound`): every residue class mod `m` whose norm is divisible
  by `d` is divisible by some `γ` with `N(γ) = ±d`.  Then `d ∣ N(g)` gives `g = γ u` with
  `N(γ) N(u) = N(g)`: the quotient `u = γ# g / N(γ)` is explicit (`div_of_adj`).
* **The induction step** (`normRepAbs_step`): from a cover for `d`, the representatives `L'` of norm
  `±N'`, and a checked closure (`closureB`: every product `γ t'` is associate to a member of `L`),
  the list `L` represents every element of norm `±d N'`.  Associates are decided by `assocB`: the
  quotient by the adjugate is integral and has norm `±1`.
* Starting from norm `1` (`normRepAbs_one`), a chain of steps gives `NormRepAbs P Q N L` for any
  product of covered divisors, and `normRep_of_abs` the `NormRep` that the source pipeline uses.

The closure check is where products are reduced (for instance by a unit relation such as
`A C ε₂ = −B²`): the list `L` need only contain one associate of each product.
-/

namespace PerfectPower.NormCover

open PerfectPower UnitBox UnitPremises NormRepProof

/-- **The quotient by the adjugate.**  If `N(γ) ≠ 0` divides every coordinate of `g γ#`, then
`g = γ u` with `N(γ) N(u) = N(g)`. -/
lemma div_of_adj {P Q : ℤ} {γ g : Z3} (hd0 : nrm P Q γ ≠ 0)
    (h1 : nrm P Q γ ∣ (mul P Q g (adj P Q γ)).1) (h2 : nrm P Q γ ∣ (mul P Q g (adj P Q γ)).2.1)
    (h3 : nrm P Q γ ∣ (mul P Q g (adj P Q γ)).2.2) :
    ∃ u, mul P Q γ u = g ∧ nrm P Q γ * nrm P Q u = nrm P Q g := by
  set d := nrm P Q γ with hd
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  obtain ⟨k3, hk3⟩ := h3
  set q := mul P Q g (adj P Q γ) with hqdef
  set u : Z3 := (k1, k2, k3)
  have hq : q = (d * u.1, d * u.2.1, d * u.2.2) := Prod.ext hk1 (Prod.ext hk2 hk3)
  obtain ⟨A, B, C⟩ := g
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
  refine ⟨u, hγu, ?_⟩
  rw [← hγu, nrm_mul]

/-! ### The divisor cover -/

/-- Some `γ` in `reps` divides `r` (`r γ# ≡ 0 mod N(γ)`). -/
def divB (P Q : ℤ) (reps : List Z3) (r : Z3) : Bool :=
  reps.any fun γ =>
    decide ((mul P Q r (adj P Q γ)).1 % nrm P Q γ = 0 ∧ (mul P Q r (adj P Q γ)).2.1 % nrm P Q γ = 0 ∧
      (mul P Q r (adj P Q γ)).2.2 % nrm P Q γ = 0)

/-- **The cover certificate**: `d ∣ m`, every representative has norm `±d`, and every residue class
mod `m` whose norm is divisible by `d` is divisible by a representative. -/
def coverB (P Q d : ℤ) (m : ℕ) (reps : List Z3) : Bool :=
  decide (0 < m) && decide ((m : ℤ) % d = 0) &&
  reps.all (fun γ => decide (nrm P Q γ = d ∨ nrm P Q γ = -d)) &&
  (List.range m).all fun a => (List.range m).all fun b => (List.range m).all fun c =>
    decide (nrm P Q ((a : ℤ), (b : ℤ), (c : ℤ)) % d ≠ 0) || divB P Q reps ((a : ℤ), (b : ℤ), (c : ℤ))

/-- **The cover is sound**: `d ∣ N(g)` gives `g = γ u`, `γ ∈ reps`, `N(γ) N(u) = N(g)`. -/
theorem cover_sound {P Q d : ℤ} {m : ℕ} {reps : List Z3} (hd : d ≠ 0) (h : coverB P Q d m reps = true)
    (g : Z3) (hg : d ∣ nrm P Q g) :
    ∃ γ ∈ reps, ∃ u, mul P Q γ u = g ∧ nrm P Q γ * nrm P Q u = nrm P Q g := by
  simp only [coverB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨hm, hmd⟩, hreps⟩, hres⟩ := h
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
  have hA : (A : ZMod m) = ((a : ℤ) : ZMod m) := by rw [ea, ZMod.intCast_mod]
  have hB : (B : ZMod m) = ((b : ℤ) : ZMod m) := by rw [eb, ZMod.intCast_mod]
  have hC : (C : ZMod m) = ((c : ℤ) : ZMod m) := by rw [ec, ZMod.intCast_mod]
  have hdm : d ∣ (m : ℤ) := Int.dvd_of_emod_eq_zero hmd
  -- an integer congruent mod m to a multiple of e (e ∣ m) is a multiple of e
  have tr : ∀ {e x y : ℤ}, e ∣ (m : ℤ) → (x : ZMod m) = (y : ZMod m) → e ∣ y → e ∣ x := by
    intro e x y hem hxy hy
    have hxy' : x ≡ y [ZMOD m] := (ZMod.intCast_eq_intCast_iff' _ _ _).mp hxy
    have := dvd_sub hy (dvd_trans hem hxy'.dvd)
    rwa [sub_sub_cancel] at this
  -- the residue's norm is divisible by d
  have hn : nrm P Q ((a : ℤ), (b : ℤ), (c : ℤ)) % d = 0 := by
    have h1 : ((nrm P Q (A, B, C) : ℤ) : ZMod m) = ((nrm P Q ((a : ℤ), (b : ℤ), (c : ℤ)) : ℤ) : ZMod m) := by
      rw [nrm_cast, nrm_cast, hA, hB, hC]
    exact Int.emod_eq_zero_of_dvd (tr hdm h1.symm hg)
  obtain ⟨γ, hγ, hdiv⟩ := List.any_eq_true.mp ((hres a la b lb c lc).resolve_left (by simpa using hn))
  simp only [decide_eq_true_eq] at hdiv
  obtain ⟨d1, d2, d3⟩ := hdiv
  have hγd : nrm P Q γ = d ∨ nrm P Q γ = -d := by simpa using hreps γ hγ
  have hγ0 : nrm P Q γ ≠ 0 := by rcases hγd with h | h <;> rw [h] <;> simpa using hd
  have hγm : nrm P Q γ ∣ (m : ℤ) := by
    rcases hγd with h | h <;> rw [h]
    · exact hdm
    · exact (neg_dvd).mpr hdm
  obtain ⟨c1, c2, c3⟩ := cast_mul_eq (P := P) (Q := Q) hA hB hC (adj P Q γ)
  exact ⟨γ, hγ, div_of_adj hγ0 (tr hγm c1 (Int.dvd_of_emod_eq_zero d1))
    (tr hγm c2 (Int.dvd_of_emod_eq_zero d2)) (tr hγm c3 (Int.dvd_of_emod_eq_zero d3))⟩

/-! ### Associates and the induction -/

/-- Norm representatives up to sign: every element of norm `±N` is a listed element times a unit. -/
def NormRepAbs (P Q N : ℤ) (L : List Z3) : Prop :=
  ∀ g : Z3, (nrm P Q g = N ∨ nrm P Q g = -N) → ∃ t ∈ L, ∃ u v : Z3, mul P Q u v = (1, 0, 0) ∧ g = mul P Q t u

theorem normRepAbs_one (P Q : ℤ) : NormRepAbs P Q 1 [(1, 0, 0)] := by
  intro g hg
  obtain ⟨v, hv⟩ := unit_of_nrm hg
  exact ⟨(1, 0, 0), List.mem_singleton_self _, g, v, hv, (one_mul' P Q g).symm⟩

/-- `x` is `t` times a unit: the adjugate quotient is integral and has norm `±1`. -/
def assocB (P Q : ℤ) (x t : Z3) : Bool :=
  let n := nrm P Q t
  let y := mul P Q x (adj P Q t)
  decide (n ≠ 0) && decide (y.1 % n = 0 ∧ y.2.1 % n = 0 ∧ y.2.2 % n = 0) &&
    decide (nrm P Q x = n ∨ nrm P Q x = -n)

theorem assoc_sound {P Q : ℤ} {x t : Z3} (h : assocB P Q x t = true) :
    ∃ u v : Z3, mul P Q u v = (1, 0, 0) ∧ x = mul P Q t u := by
  simp only [assocB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hn, d1, d2, d3⟩, hx⟩ := h
  obtain ⟨u, hu, hnu⟩ := div_of_adj hn (Int.dvd_of_emod_eq_zero d1) (Int.dvd_of_emod_eq_zero d2)
    (Int.dvd_of_emod_eq_zero d3)
  have hu1 : nrm P Q u = 1 ∨ nrm P Q u = -1 := by
    rcases hx with hx | hx
    · left
      have : nrm P Q t * (nrm P Q u - 1) = 0 := by rw [mul_sub, hnu, hx]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hn)
    · right
      have : nrm P Q t * (nrm P Q u + 1) = 0 := by rw [mul_add, hnu, hx]; ring
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left hn)
  obtain ⟨v, hv⟩ := unit_of_nrm hu1
  exact ⟨u, v, hv, hu.symm⟩

/-- Every product `γ t'` (`γ` in the cover, `t'` in the previous list) is associate to a member of `L`. -/
def closureB (P Q : ℤ) (reps L' L : List Z3) : Bool :=
  reps.all fun γ => L'.all fun t' => L.any fun t => assocB P Q (mul P Q γ t') t

lemma unit_mul {P Q : ℤ} {u v u' v' : Z3} (h : mul P Q u v = (1, 0, 0)) (h' : mul P Q u' v' = (1, 0, 0)) :
    mul P Q (mul P Q u u') (mul P Q v v') = (1, 0, 0) := by
  rw [mul_assoc', mul_comm' P Q u' (mul P Q v v'), mul_assoc', ← mul_assoc' P Q u v, h, one_mul',
    mul_comm' P Q v' u', h']

/-- **The induction step**: a cover for `d`, representatives of norm `±N'`, and the closure check give
representatives of norm `±(d N')`. -/
theorem normRepAbs_step {P Q d N' : ℤ} {m : ℕ} {reps L' L : List Z3} (hd : d ≠ 0)
    (hc : coverB P Q d m reps = true) (hprev : NormRepAbs P Q N' L') (hcl : closureB P Q reps L' L = true) :
    NormRepAbs P Q (d * N') L := by
  intro g hg
  have hdg : d ∣ nrm P Q g := by
    rcases hg with h | h <;> rw [h]
    · exact dvd_mul_right d N'
    · exact (dvd_neg).mpr (dvd_mul_right d N')
  obtain ⟨γ, hγ, q, hq, hnq⟩ := cover_sound hd hc g hdg
  have hcov := hc
  simp only [coverB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcov
  have hγd : nrm P Q γ = d ∨ nrm P Q γ = -d := hcov.1.2 γ hγ
  have hq' : nrm P Q q = N' ∨ nrm P Q q = -N' := by
    rcases hγd with h1 | h1 <;> rcases hg with h2 | h2 <;> rw [h1, h2] at hnq
    · left; exact mul_left_cancel₀ hd hnq
    · right; exact mul_left_cancel₀ hd (by linarith)
    · right; exact mul_left_cancel₀ hd (by linarith)
    · left; exact mul_left_cancel₀ hd (by linarith)
  obtain ⟨t', ht', u, v, huv, hqt⟩ := hprev q hq'
  simp only [closureB, List.all_eq_true, List.any_eq_true] at hcl
  obtain ⟨t, ht, has⟩ := hcl γ hγ t' ht'
  obtain ⟨w, w', hww, hγt⟩ := assoc_sound has
  refine ⟨t, ht, mul P Q w u, mul P Q w' v, unit_mul hww huv, ?_⟩
  rw [← hq, hqt, ← mul_assoc', hγt, mul_assoc']

/-- The step with the target written out: `d N' = N`. -/
theorem normRepAbs_step' {P Q d N' N : ℤ} {m : ℕ} {reps L' L : List Z3} (hd : d ≠ 0) (hN : d * N' = N)
    (hc : coverB P Q d m reps = true) (hprev : NormRepAbs P Q N' L') (hcl : closureB P Q reps L' L = true) :
    NormRepAbs P Q N L :=
  hN ▸ normRepAbs_step hd hc hprev hcl

/-- `NormRep` (norm exactly `N`) from `NormRepAbs`. -/
theorem normRep_of_abs {P Q N : ℤ} {L : List Z3} (h : NormRepAbs P Q N L) : NormRep P Q N L := by
  intro g hg
  obtain ⟨t, ht, u, v, huv, hgt⟩ := h g (Or.inl hg)
  exact ⟨t, ht, u, v, huv, hgt⟩

end PerfectPower.NormCover
