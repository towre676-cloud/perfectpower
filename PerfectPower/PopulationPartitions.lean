import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! Finite comparison laws and identity-preserving changes of address.

These are generic mathematical statements. They neither identify the Python
predicate compiler with these filters nor certify a curve's global completeness.
The address transport theorems assume supplied bijective address maps.
-/
namespace PerfectPower.PopulationPartitions

variable {α : Type*}
variable (U : Finset α) (A B : α → Prop) [DecidablePred A] [DecidablePred B]

def both := U.filter (fun x => A x ∧ B x)
def leftOnly := U.filter (fun x => A x ∧ ¬ B x)
def rightOnly := U.filter (fun x => ¬ A x ∧ B x)
def neither := U.filter (fun x => ¬ A x ∧ ¬ B x)

theorem four_cover [DecidableEq α] :
    both U A B ∪ leftOnly U A B ∪ rightOnly U A B ∪ neither U A B = U := by
  ext x
  simp only [both, leftOnly, rightOnly, neither, Finset.mem_union, Finset.mem_filter]
  tauto

theorem four_exclusive (x : α) :
    ¬ (x ∈ both U A B ∧ x ∈ leftOnly U A B) ∧
    ¬ (x ∈ both U A B ∧ x ∈ rightOnly U A B) ∧
    ¬ (x ∈ both U A B ∧ x ∈ neither U A B) ∧
    ¬ (x ∈ leftOnly U A B ∧ x ∈ rightOnly U A B) ∧
    ¬ (x ∈ leftOnly U A B ∧ x ∈ neither U A B) ∧
    ¬ (x ∈ rightOnly U A B ∧ x ∈ neither U A B) := by
  simp only [both, leftOnly, rightOnly, neither, Finset.mem_filter]
  tauto

theorem left_card :
    (U.filter A).card = (both U A B).card + (leftOnly U A B).card := by
  simpa [both, leftOnly, Finset.filter_filter] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := U.filter A) B).symm

theorem right_card :
    (U.filter B).card = (both U A B).card + (rightOnly U A B).card := by
  simpa [both, rightOnly, Finset.filter_filter, and_comm] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := U.filter B) A).symm

theorem complement_left_card :
    (U.filter (fun x => ¬ A x)).card =
      (rightOnly U A B).card + (neither U A B).card := by
  simpa [rightOnly, neither, Finset.filter_filter] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := U.filter (fun x => ¬ A x)) B).symm

theorem four_card :
    U.card = (both U A B).card + (leftOnly U A B).card +
      (rightOnly U A B).card + (neither U A B).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := U) A
  rw [left_card U A B, complement_left_card U A B] at h
  omega

theorem union_card :
    (U.filter (fun x => A x ∨ B x)).card =
      (both U A B).card + (leftOnly U A B).card + (rightOnly U A B).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := U.filter (fun x => A x ∨ B x)) A
  have h₁ : (U.filter (fun x => A x ∨ B x)).filter A = U.filter A := by
    ext x; simp only [Finset.mem_filter]; tauto
  have h₂ : (U.filter (fun x => A x ∨ B x)).filter (fun x => ¬ A x) = rightOnly U A B := by
    ext x; simp only [rightOnly, Finset.mem_filter]; tauto
  rw [h₁, h₂, left_card U A B] at h
  exact h.symm

theorem symmetric_difference_card :
    (U.filter (fun x => (A x ∧ ¬ B x) ∨ (¬ A x ∧ B x))).card =
      (leftOnly U A B).card + (rightOnly U A B).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := U.filter (fun x => (A x ∧ ¬ B x) ∨ (¬ A x ∧ B x))) A
  have h₁ : (U.filter (fun x => (A x ∧ ¬ B x) ∨ (¬ A x ∧ B x))).filter A = leftOnly U A B := by
    ext x; simp only [leftOnly, Finset.mem_filter]; tauto
  have h₂ : (U.filter (fun x => (A x ∧ ¬ B x) ∨ (¬ A x ∧ B x))).filter (fun x => ¬ A x) = rightOnly U A B := by
    ext x; simp only [rightOnly, Finset.mem_filter]; tauto
  rw [h₁, h₂] at h
  exact h.symm

section Addresses
variable {Object Address₁ Address₂ Address₃ : Type*}

/-- Decode the old address to its original object, then encode the new address. -/
def transport (first : Object ≃ Address₁) (second : Object ≃ Address₂) : Address₁ → Address₂ :=
  fun address => second (first.symm address)

theorem transport_identity (first : Object ≃ Address₁) (second : Object ≃ Address₂)
    (address : Address₁) :
    second.symm (transport first second address) = first.symm address := by
  simp [transport]

theorem transport_roundtrip (first : Object ≃ Address₁) (second : Object ≃ Address₂)
    (address : Address₁) : transport second first (transport first second address) = address := by
  simp [transport]

theorem transport_composition (first : Object ≃ Address₁) (second : Object ≃ Address₂)
    (third : Object ≃ Address₃) (address : Address₁) :
    transport second third (transport first second address) = transport first third address := by
  simp [transport]

theorem transport_injective (first : Object ≃ Address₁) (second : Object ≃ Address₂) :
    Function.Injective (transport first second) :=
  second.injective.comp first.symm.injective

/-- Inclusion into a restricted population preserves the actual object. -/
def includeRestriction {P Q : Object → Prop} (h : ∀ x, P x → Q x) :
    {x // P x} → {x // Q x} := fun x => ⟨x.val, h x.val x.property⟩

theorem restriction_identity {P Q : Object → Prop} (h : ∀ x, P x → Q x)
    (x : {x // P x}) : (includeRestriction h x).val = x.val := rfl

theorem restriction_injective {P Q : Object → Prop} (h : ∀ x, P x → Q x) :
    Function.Injective (includeRestriction h) := by
  intro x y equal
  apply Subtype.ext
  simpa [includeRestriction] using congrArg (fun z : {x // Q x} => z.val) equal
end Addresses
end PerfectPower.PopulationPartitions
