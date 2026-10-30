import PerfectPower.DescentRankBridge
import PerfectPower.DescentCover

namespace PerfectPower.DescentCounting

open DescentRankBridge
variable {G H A B : Type*} [AddCommGroup G] [AddCommGroup H]
  [AddCommGroup A] [AddCommGroup B]

/-- Exact kernel counting, including the intersection with the first image.
Nat.card and relindex use zero for infinite cardinalities; no cancellation is used. -/
theorem kernel_composition_count (f : G →+ H) (g : H →+ G) :
    f.range.relindex (f.range ⊔ g.ker) * Nat.card (g.comp f).ker =
      Nat.card f.ker * Nat.card g.ker := by
  have hle : f.ker ≤ (g.comp f).ker := by
    intro x hx
    change g (f x) = 0
    rw [show f x = 0 from hx, map_zero]
  have hmap : (g.comp f).ker.map f = f.range ⊓ g.ker := by
    rw [← AddMonoidHom.comap_ker, AddSubgroup.map_comap_eq]
  have h₁ := AddSubgroup.relindex_inf_mul_relindex
    (⊥ : AddSubgroup G) f.ker (g.comp f).ker
  rw [inf_of_le_left hle, bot_inf, AddSubgroup.relindex_bot_left,
    AddSubgroup.relindex_bot_left, AddSubgroup.relindex_ker, hmap] at h₁
  have h₂ := AddSubgroup.relindex_inf_mul_relindex
    (⊥ : AddSubgroup H) f.range g.ker
  rw [bot_inf, AddSubgroup.relindex_bot_left,
    AddSubgroup.relindex_bot_left] at h₂
  rw [AddSubgroup.relindex_sup_left]
  calc
    f.range.relindex g.ker * Nat.card (g.comp f).ker =
        Nat.card f.ker * (Nat.card (f.range ⊓ g.ker) * f.range.relindex g.ker) := by
          rw [← h₁]; ring
    _ = Nat.card f.ker * Nat.card g.ker := by rw [h₂]

/-- T3 before any rank interpretation: exact descent images count the doubling
quotient with its actual relative-kernel correction. -/
theorem exact_descent_count (f : G →+ H) (g : H →+ G)
    (α : H →+ A) (β : G →+ B)
    (hf : f.range = α.ker) (hg : g.range = β.ker)
    (hcomp : g.comp f = double G) :
    f.range.relindex (f.range ⊔ g.ker) * (double G).range.index =
      Nat.card α.range * Nat.card β.range := by
  have h := IsogenyIndexBridges.doubling_index f g (double G) hcomp
  simpa only [hf, hg, AddSubgroup.index_ker] using h

/-- The correction times rational two-torsion equals the product of isogeny
kernel orders. This statement does not require a Mordell--Weil decomposition. -/
theorem torsion_correction (f : G →+ H) (g : H →+ G)
    (hcomp : g.comp f = double G) :
    f.range.relindex (f.range ⊔ g.ker) * Nat.card (double G).ker =
      Nat.card f.ker * Nat.card g.ker := by
  rw [← hcomp]
  exact kernel_composition_count f g

/-- General divisor formula: a rank interpretation of the doubling index is
an explicit premise. The denominator is the product of kernel orders. -/
theorem rank_count_of_doubling_index (f : G →+ H) (g : H →+ G)
    (α : H →+ A) (β : G →+ B)
    (hf : f.range = α.ker) (hg : g.range = β.ker)
    (hcomp : g.comp f = double G) (r : ℕ)
    (hr : (double G).range.index = 2^r * Nat.card (double G).ker) :
    Nat.card α.range * Nat.card β.range =
      2^r * (Nat.card f.ker * Nat.card g.ker) := by
  have hc := exact_descent_count f g α β hf hg hcomp
  have ht := torsion_correction f g hcomp
  rw [hr] at hc
  calc
    Nat.card α.range * Nat.card β.range =
        2^r * (f.range.relindex (f.range ⊔ g.ker) * Nat.card (double G).ker) := by
          rw [← hc]; ring
    _ = _ := by rw [ht]

/-- The classical divisor four is a consequence of two kernel orders equal
to two, and not of a universally constant relative-kernel correction. -/
theorem divisor_four (f : G →+ H) (g : H →+ G)
    (α : H →+ A) (β : G →+ B)
    (hf : f.range = α.ker) (hg : g.range = β.ker)
    (hcomp : g.comp f = double G) (r : ℕ)
    (hr : (double G).range.index = 2^r * Nat.card (double G).ker)
    (hkf : Nat.card f.ker = 2) (hkg : Nat.card g.ker = 2) :
    Nat.card α.range * Nat.card β.range = 4 * 2^r := by
  rw [rank_count_of_doubling_index f g α β hf hg hcomp r hr, hkf, hkg]
  ring

/-- Unconditional rational elliptic image-count identity (no rank premise). -/
theorem elliptic_exact_descent_count (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (TwoIsogenyPointMap.phiHom a b hb hd).range.relindex
      ((TwoIsogenyPointMap.phiHom a b hb hd).range ⊔
        (TwoIsogenyDual.dualHom a b hb hd).ker) *
      (double (TwoIsogenyPointMap.E a b).Point).range.index =
    Nat.card (DescentDelta.deltaPhi a b hb hd).range *
      Nat.card (DescentDelta.deltaDual a b hb).range := by
  apply exact_descent_count _ _ _ _
    (DescentCover.phiHom_range_eq_deltaPhi_ker a b hb hd)
    (DescentCover.dualHom_range_eq_deltaDual_ker a b hb hd)
  ext P
  change TwoIsogenyDual.dualHom a b hb hd (TwoIsogenyPointMap.phi a b hb hd P) = (2:ℤ) • P
  rw [TwoIsogenyDual.dual_phi, two_zsmul]

/-- Cardinality two from an explicit description, without a Fintype instance. -/
theorem card_two_of_description (K : AddSubgroup G) (t : G)
    (ht : t ∈ K) (hne : t ≠ 0)
    (hK : ∀ x ∈ K, x = 0 ∨ x = t) : Nat.card K = 2 := by
  classical
  let e : K ≃ Bool :=
    { toFun := fun x => if (x : G) = 0 then false else true
      invFun := fun b => if b then ⟨t, ht⟩ else ⟨0, K.zero_mem⟩
      left_inv := by
        intro x
        rcases hK x x.property with hx | hx
        · apply Subtype.ext
          simp [hx]
        · apply Subtype.ext
          simp [hx, hne]
      right_inv := by
        intro b
        cases b <;> simp [hne] }
  calc
    Nat.card K = Nat.card Bool := Nat.card_congr e
    _ = 2 := by simp [Nat.card_eq_fintype_card]

open TwoIsogenyPointMap TwoIsogenyDual
open WeierstrassCurve WeierstrassCurve.Affine

theorem phi_kernel_card (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    Nat.card (phiHom a b hb hd).ker = 2 := by
  apply card_two_of_description _ (T a b hb hd)
  · exact phi_T a b hb hd
  · exact T_ne_zero a b hb hd
  · intro P hP
    exact (phi_eq_zero_iff a b hb hd P).mp hP

/-- The normalized dual has exactly the two rational kernel points O and (0,0).
The coordinate scaling does not introduce any extra kernel points. -/
theorem dual_eq_zero_iff (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P : (D a b).Point) :
    dualHom a b hb hd P = 0 ↔
      P = 0 ∨ P = T (-2*a) (a^2-4*b) hd (dual_smooth a b hb) := by
  cases P with
  | zero => simp
  | @some x y hp =>
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := by
        have he := (equation ..).mp hp.1
        simp only [zero_mul] at he
        exact pow_eq_zero he
      subst y
      have hz : dualHom a b hb hd (Point.some hp) = 0 := by
        change scaleBack a b hb hd (rawDualHom a b hb hd (Point.some hp)) = 0
        rw [rawDual_some_zero]
        rfl
      exact ⟨fun _ => Or.inr rfl, fun _ => hz⟩
    · obtain ⟨hq, he⟩ := dual_some a b x y hb hd hp hx
      constructor
      · intro hz
        rw [he] at hz
        exact False.elim (Point.some_ne_zero hq hz)
      · rintro (hz | hz)
        · exact False.elim (Point.some_ne_zero hp hz)
        · have hc : x = 0 ∧ y = 0 := by
            simpa only [T, Point.some.injEq] using hz
          exact False.elim (hx hc.1)

theorem dual_kernel_card (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    Nat.card (dualHom a b hb hd).ker = 2 := by
  apply card_two_of_description _
    (T (-2*a) (a^2-4*b) hd (dual_smooth a b hb))
  · exact (dual_eq_zero_iff a b hb hd _).mpr (Or.inr rfl)
  · exact T_ne_zero _ _ _ _
  · intro P hP
    exact (dual_eq_zero_iff a b hb hd P).mp hP

theorem elliptic_composition (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (dualHom a b hb hd).comp (phiHom a b hb hd) = double (E a b).Point := by
  ext P
  change dualHom a b hb hd (phi a b hb hd P) = (2:ℤ) • P
  rw [dual_phi, two_zsmul]

/-- Unconditional cancellation of the exceptional-kernel and two-torsion factors. -/
theorem elliptic_torsion_correction (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0) :
    (phiHom a b hb hd).range.relindex
      ((phiHom a b hb hd).range ⊔ (dualHom a b hb hd).ker) *
      Nat.card (double (E a b).Point).ker = 4 := by
  rw [torsion_correction _ _ (elliptic_composition a b hb hd),
    phi_kernel_card, dual_kernel_card]

/-- T3 without a rank premise: the product of the two actual descent image
orders, multiplied by rational two-torsion, is four times the doubling index. -/
theorem elliptic_torsion_normalized_count (a b : ℚ) (hb : b ≠ 0)
    (hd : a^2-4*b ≠ 0) :
    (Nat.card (DescentDelta.deltaPhi a b hb hd).range *
      Nat.card (DescentDelta.deltaDual a b hb).range) *
      Nat.card (double (E a b).Point).ker =
        4 * (double (E a b).Point).range.index := by
  have hc := elliptic_exact_descent_count a b hb hd
  have ht := elliptic_torsion_correction a b hb hd
  rw [← hc]
  calc
    _ = ((phiHom a b hb hd).range.relindex
        ((phiHom a b hb hd).range ⊔ (dualHom a b hb hd).ker) *
        Nat.card (double (E a b).Point).ker) *
        (double (E a b).Point).range.index := by ring
    _ = _ := by rw [ht]

/-- Finite descent images have the classical product, conditional only on the
explicit doubling-index/rank interpretation. No saturation or height input is inferred. -/
theorem elliptic_divisor_four (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (r : ℕ)
    (hr : (double (E a b).Point).range.index =
      2^r * Nat.card (double (E a b).Point).ker) :
    Nat.card (DescentDelta.deltaPhi a b hb hd).range *
      Nat.card (DescentDelta.deltaDual a b hb).range = 4 * 2^r := by
  exact divisor_four _ _ _ _
    (DescentCover.phiHom_range_eq_deltaPhi_ker a b hb hd)
    (DescentCover.dualHom_range_eq_deltaDual_ker a b hb hd)
    (elliptic_composition a b hb hd) r hr
    (phi_kernel_card a b hb hd) (dual_kernel_card a b hb hd)

/-- The full image count without discarding the Mordell--Weil decomposition premise. -/
theorem elliptic_count_from_decomposition {F T₀ : Type*}
    [AddCommGroup F] [AddCommGroup T₀] [Module.Free ℤ F] [Module.Finite ℤ F]
    [Finite T₀] (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (e : (E a b).Point ≃+ F × T₀) :
    (phiHom a b hb hd).range.relindex
      ((phiHom a b hb hd).range ⊔ (dualHom a b hb hd).ker) *
      (2^Module.finrank ℤ F * Nat.card (double T₀).ker) =
    Nat.card (DescentDelta.deltaPhi a b hb hd).range *
      Nat.card (DescentDelta.deltaDual a b hb).range := by
  rw [← doubling_index_from_decomposition e]
  exact elliptic_exact_descent_count a b hb hd

/-- Two-torsion is transported from the finite summand of an actual
free-plus-finite decomposition. -/
theorem doubling_kernel_card_from_decomposition {F T₀ : Type*}
    [AddCommGroup F] [AddCommGroup T₀] [Module.Free ℤ F] [Module.Finite ℤ F]
    [Finite T₀] (e : G ≃+ F × T₀) :
    Nat.card (double G).ker = Nat.card (double T₀).ker := by
  let k : (double G).ker ≃ (double T₀).ker :=
    { toFun := fun x => ⟨(e x).2, by
        have hx : (2:ℤ) • e (x:G) = 0 := by
          rw [← map_zsmul, show (2:ℤ) • (x:G) = 0 from x.property, map_zero]
        exact congrArg Prod.snd hx⟩
      invFun := fun t => ⟨e.symm (0,(t:T₀)), by
        apply e.injective
        rw [map_zsmul, e.apply_symm_apply, map_zero]
        apply Prod.ext
        · simp
        · exact t.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply e.injective
        rw [e.apply_symm_apply]
        have hx : (2:ℤ) • e (x:G) = 0 := by
          rw [← map_zsmul, show (2:ℤ) • (x:G) = 0 from x.property, map_zero]
        have hxF : (2:ℤ) • (e (x:G)).1 = 0 := congrArg Prod.fst hx
        have hz : (e (x:G)).1 = 0 :=
          (smul_eq_zero.mp hxF).resolve_left (by norm_num)
        exact Prod.ext hz.symm rfl
      right_inv := by
        intro t
        apply Subtype.ext
        exact congrArg Prod.snd (e.apply_symm_apply (0,(t:T₀))) }
  exact Nat.card_congr k

/-- Divisor four from a genuine Mordell--Weil decomposition; no numerical
rank assumption and no assumption that E has only two rational two-torsion points. -/
theorem elliptic_divisor_four_from_decomposition {F T₀ : Type*}
    [AddCommGroup F] [AddCommGroup T₀] [Module.Free ℤ F] [Module.Finite ℤ F]
    [Finite T₀] (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (e : (E a b).Point ≃+ F × T₀) :
    Nat.card (DescentDelta.deltaPhi a b hb hd).range *
      Nat.card (DescentDelta.deltaDual a b hb).range =
        4 * 2^Module.finrank ℤ F := by
  apply elliptic_divisor_four a b hb hd
  rw [doubling_index_from_decomposition e, doubling_kernel_card_from_decomposition e]

end PerfectPower.DescentCounting

