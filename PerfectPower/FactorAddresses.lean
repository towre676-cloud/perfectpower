import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! Executable typed addresses for factored populations.
Each factor is a finite child table. Empty tables, the empty product and
nonuniform factor sizes are included. This does not verify JSON parsing or CRT.
-/
namespace PerfectPower.FactorAddresses

def Address : List ℕ → Type
  | [] => Fin 1
  | n :: ns => Fin n × Address ns

def addressEquiv : (ns : List ℕ) → Address ns ≃ Fin ns.prod
  | [] => Equiv.refl _
  | n :: ns => (Equiv.prodCongr (Equiv.refl (Fin n)) (addressEquiv ns)).trans
      finProdFinEquiv

def rank {ns : List ℕ} (a : Address ns) : Fin ns.prod := addressEquiv ns a
def select (ns : List ℕ) (i : Fin ns.prod) : Address ns := (addressEquiv ns).symm i

@[simp] theorem rank_select (ns : List ℕ) (i : Fin ns.prod) :
    rank (select ns i) = i := (addressEquiv ns).apply_symm_apply i

@[simp] theorem select_rank {ns : List ℕ} (a : Address ns) :
    select ns (rank a) = a := (addressEquiv ns).symm_apply_apply a

theorem rank_injective (ns : List ℕ) : Function.Injective (@rank ns) :=
  (addressEquiv ns).injective

theorem select_surjective (ns : List ℕ) : Function.Surjective (select ns) :=
  (addressEquiv ns).symm.surjective

theorem rank_cons (n : ℕ) (ns : List ℕ) (i : Fin n) (a : Address ns) :
    (rank (ns := n :: ns) (i,a)).val = (rank a).val + ns.prod*i.val := rfl

theorem address_card (ns : List ℕ) [Fintype (Address ns)] :
    Fintype.card (Address ns) = ns.prod := by
  rw [Fintype.card_congr (addressEquiv ns), Fintype.card_fin]

/-- A zero factor gives no address; no synthetic leaf is emitted. -/
theorem no_address_of_zero_product (ns : List ℕ) (h : ns.prod=0) :
    IsEmpty (Address ns) := by
  exact ⟨fun a => by have hlt : (rank a).val < ns.prod := (rank a).isLt; omega⟩

/-- The empty product is one leaf, rather than an empty population. -/
theorem empty_rank (a : Address []) : (rank a).val=0 := by
  exact Fin.eq_zero a ▸ rfl

/-- Sound rejection can never discard a source solution at that address. -/
theorem safe_pruning {ns : List ℕ} (source : Address ns → Prop)
    (keep : Address ns → Bool) (sound : ∀ a, source a → keep a=true)
    (i : Fin ns.prod) (rejected : keep (select ns i)=false) :
    ¬ source (select ns i) := by
  intro hs
  have := sound (select ns i) hs
  simp_all

/-- A complete leaf semantics remains complete after indexing. -/
theorem source_rank_iff {ns : List ℕ} (source : Address ns → Prop)
    (i : Fin ns.prod) : source (select ns i) ↔
      ∃ a, source a ∧ rank a=i := by
  constructor
  · intro h; exact ⟨select ns i,h,rank_select ns i⟩
  · rintro ⟨a,ha,hi⟩
    rw [← hi,select_rank]
    exact ha

example : (rank (ns := [2,3,5]) (⟨1,by decide⟩,⟨2,by decide⟩,
    ⟨4,by decide⟩,⟨0,by decide⟩)).val = 29 := by decide

example : (rank (select [7,11,13] ⟨997,by decide⟩)).val = 997 := by decide

end PerfectPower.FactorAddresses
