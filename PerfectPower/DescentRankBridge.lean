import PerfectPower.TwoIsogenyDual
import Mathlib.LinearAlgebra.FreeModule.ModN

namespace PerfectPower.DescentRankBridge

variable {G F T H : Type*} [AddCommGroup G] [AddCommGroup F] [AddCommGroup T]
  [AddCommGroup H]

abbrev double (G : Type*) [AddCommGroup G] : G →+ G := zsmulAddGroupHom 2

theorem free_doubling_index [Module.Free ℤ F] [Module.Finite ℤ F] :
    (double F).range.index = 2^Module.finrank ℤ F := by
  rw [AddSubgroup.index_eq_card]
  change Nat.card (ModN F 2) = _
  exact ModN.natCard_eq F 2

theorem finite_doubling_index [Finite T] :
    (double T).range.index = Nat.card (double T).ker :=
  AddSubgroup.index_range

theorem product_doubling_range :
    (double (F×T)).range = (double F).range.prod (double T).range := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨⟨q.1,rfl⟩,⟨q.2,rfl⟩⟩
  · rintro ⟨⟨f,hf⟩,⟨t,ht⟩⟩
    exact ⟨(f,t),Prod.ext hf ht⟩

theorem equiv_doubling_range (e : G ≃+ F×T) :
    (double G).range.map e.toAddMonoidHom = (double (F×T)).range := by
  ext p
  constructor
  · rintro ⟨q,⟨g,rfl⟩,rfl⟩
    exact ⟨e g,(map_zsmul e 2 g).symm⟩
  · rintro ⟨q,rfl⟩
    refine ⟨double G (e.symm q),⟨e.symm q,rfl⟩,?_⟩
    change e ((2:ℤ) • e.symm q) = (2:ℤ) • q
    rw [map_zsmul,e.apply_symm_apply]

/-- Rank follows from an actual free-plus-finite group decomposition, not a numerical premise. -/
theorem doubling_index_from_decomposition [Module.Free ℤ F] [Module.Finite ℤ F]
    [Finite T] (e : G ≃+ F×T) :
    (double G).range.index = 2^Module.finrank ℤ F * Nat.card (double T).ker := by
  have he := AddSubgroup.index_map_of_bijective (f := e.toAddMonoidHom) e.bijective (double G).range
  rw [equiv_doubling_range e,product_doubling_range,AddSubgroup.index_prod,
    free_doubling_index,finite_doubling_index] at he
  exact he.symm

/-- The corrected two-isogeny rank identity retains the torsion and kernel factors. -/
theorem descent_rank_equation [Module.Free ℤ F] [Module.Finite ℤ F] [Finite T]
    (e : G ≃+ F×T) (f : G →+ H) (g : H →+ G)
    (hcomp : g.comp f = double G) :
    f.range.relindex (f.range ⊔ g.ker) *
      (2^Module.finrank ℤ F * Nat.card (double T).ker) = f.range.index*g.range.index := by
  rw [← doubling_index_from_decomposition e]
  exact IsogenyIndexBridges.doubling_index f g (double G) hcomp


/-- Application to actual elliptic maps; the only remaining group input here is a
Mordell--Weil decomposition, whose free rank and finite torsion are explicit. -/
theorem elliptic_descent_rank (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    [Module.Free ℤ F] [Module.Finite ℤ F] [Finite T]
    (e : (TwoIsogenyPointMap.E a b).Point ≃+ F×T) :
    (TwoIsogenyPointMap.phiHom a b hb hd).range.relindex
      ((TwoIsogenyPointMap.phiHom a b hb hd).range ⊔ (TwoIsogenyDual.dualHom a b hb hd).ker) *
      (2^Module.finrank ℤ F * Nat.card (double T).ker) =
      (TwoIsogenyPointMap.phiHom a b hb hd).range.index*
        (TwoIsogenyDual.dualHom a b hb hd).range.index := by
  apply descent_rank_equation e
  ext P
  change TwoIsogenyDual.dualHom a b hb hd (TwoIsogenyPointMap.phi a b hb hd P)=(2:ℤ)•P
  rw [TwoIsogenyDual.dual_phi,two_zsmul]

end PerfectPower.DescentRankBridge
