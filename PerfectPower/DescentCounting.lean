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

end PerfectPower.DescentCounting
