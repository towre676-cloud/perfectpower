import Mathlib.Tactic

/-! Finite certified solution charts with explicit residual obligations.
Inspired by the proof-engineering structure of GLC, not an application of its theorem.
Parameter coverage and exact reconstruction are distinct hypotheses. Multiplicities
are retained; a nonempty parameter residual need not contain an actual solution. -/
namespace PerfectPower.SolutionChart

structure Chart {α β : Type*} [DecidableEq α] [DecidableEq β] (P : α → Prop) where
  parameter : α → β
  parameters : Finset β
  covered : ∀ a, P a → parameter a ∈ parameters
  solved : Finset β
  solved_subset : solved ⊆ parameters
  fibre : β → Finset α
  fibre_exact : ∀ b ∈ solved, ∀ a, a ∈ fibre b ↔ P a ∧ parameter a = b

namespace Chart
variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable {P : α → Prop}

def known (c : Chart (β := β) P) : Finset α := c.solved.biUnion c.fibre

def residual (c : Chart (β := β) P) : Finset β := c.parameters \ c.solved

theorem known_iff (c : Chart (β := β) P) (a : α) :
    a ∈ c.known ↔ P a ∧ c.parameter a ∈ c.solved := by
  constructor
  · intro h
    obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hp, he⟩ := (c.fibre_exact b hb a).mp ha
    exact ⟨hp, he ▸ hb⟩
  · rintro ⟨hp, hb⟩
    exact Finset.mem_biUnion.mpr
      ⟨c.parameter a, hb, (c.fibre_exact _ hb a).mpr ⟨hp, rfl⟩⟩

theorem partition (c : Chart (β := β) P) (a : α) :
    P a ↔ a ∈ c.known ∨ (P a ∧ c.parameter a ∈ c.residual) := by
  rw [known_iff]
  constructor
  · intro hp
    by_cases h : c.parameter a ∈ c.solved
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, Finset.mem_sdiff.mpr ⟨c.covered a hp, h⟩⟩
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp

theorem complete (c : Chart (β := β) P) (closed : c.residual = ∅) (a : α) :
    P a ↔ a ∈ c.known := by
  rw [c.partition]
  simp [closed]

-- The precise unresolved obligation is absence of source solutions over residual
-- parameters. Counting or merely listing residual parameters does not close it.
theorem complete_iff (c : Chart (β := β) P) :
    (∀ a, P a ↔ a ∈ c.known) ↔
      ∀ a, P a → c.parameter a ∉ c.residual := by
  constructor
  · intro h a hp hr
    have hs := ((c.known_iff a).mp ((h a).mp hp)).2
    exact (Finset.mem_sdiff.mp hr).2 hs
  · intro h a
    constructor
    · intro hp
      rcases (c.partition a).mp hp with hk | ⟨_, hr⟩
      · exact hk
      · exact False.elim (h a hp hr)
    · exact fun hk => ((c.known_iff a).mp hk).1

theorem context_partition (c : Chart (β := β) P) (C : α → Prop) (a : α) :
    (P a ∧ C a) ↔
      (a ∈ c.known ∧ C a) ∨ (P a ∧ C a ∧ c.parameter a ∈ c.residual) := by
  rw [c.partition]
  tauto

theorem fibres_disjoint (c : Chart (β := β) P) :
    c.solved.toSet.PairwiseDisjoint c.fibre := by
  intro b hb d hd hbd
  apply Finset.disjoint_left.mpr
  intro a hab had
  have h1 := ((c.fibre_exact b hb a).mp hab).2
  have h2 := ((c.fibre_exact d hd a).mp had).2
  exact hbd (h1.symm.trans h2)

theorem card_known (c : Chart (β := β) P) :
    c.known.card = ∑ b ∈ c.solved, (c.fibre b).card :=
  Finset.card_biUnion c.fibres_disjoint

/-- Change source representation through a genuine equivalence. The parameter
map must commute, and every reconstructed point is transported back. -/
def transport (c : Chart (β := β) P) (e : γ ≃ α) : Chart (β := β) (fun x : γ => P (e x)) where
  parameter x := c.parameter (e x)
  parameters := c.parameters
  covered x h := c.covered (e x) h
  solved := c.solved
  solved_subset := c.solved_subset
  fibre b := (c.fibre b).image e.symm
  fibre_exact b hb x := by
    constructor
    · intro h
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
      have hx : a = e x := by
        have := congr_arg e he
        simpa using this
      subst a
      exact (c.fibre_exact b hb (e x)).mp ha
    · intro h
      exact Finset.mem_image.mpr
        ⟨e x, (c.fibre_exact b hb (e x)).mpr h, e.symm_apply_apply x⟩

theorem transport_known (c : Chart (β := β) P) (e : γ ≃ α) (x : γ) :
    x ∈ (c.transport e).known ↔ e x ∈ c.known := by
  rw [known_iff, known_iff]
  rfl

end Chart
end PerfectPower.SolutionChart
