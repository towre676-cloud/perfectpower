import Mathlib
namespace PerfectPower.TargetDecoder
variable {S O T : Type*}

/-- Recovery only requires constancy of the target on observation fibres. -/
theorem decoder_iff (obs : S → O) (target : S → T) [Nonempty T] :
    (∃ decode : O → T, ∀ s, decode (obs s)=target s) ↔
    (∀ s t, obs s=obs t → target s=target t) := by
  constructor
  · rintro ⟨decode,h⟩ s t he
    rw [← h s, ← h t, he]
  · intro h
    classical
    let decode : O → T := fun o => if ho : ∃ s, obs s=o then target ho.choose else Classical.choice inferInstance
    refine ⟨decode, ?_⟩
    intro s
    simp only [decode, dif_pos (show ∃ t, obs t=obs s from ⟨s,rfl⟩)]
    exact h _ s (Exists.choose_spec (show ∃ t, obs t=obs s from ⟨s,rfl⟩))

theorem separation_iff (obs : S → O) (target : S → T) :
    (∀ s t, obs s=obs t → target s=target t) ↔
    (∀ s t, target s ≠ target t → obs s ≠ obs t) := by
  constructor
  · intro h s t ht ho
    exact ht (h s t ho)
  · intro h s t ho
    by_contra ht
    exact h s t ht ho

/-- A collision refutes every possible decoder, not just the current algorithm. -/
theorem collision_no_decoder (obs : S → O) (target : S → T) (s t : S)
    (ho : obs s=obs t) (ht : target s ≠ target t) :
    ¬ ∃ decode : O → T, ∀ s, decode (obs s)=target s := by
  rintro ⟨d,h⟩
  apply ht
  rw [← h s, ← h t, ho]
end PerfectPower.TargetDecoder
