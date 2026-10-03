import PerfectPower.DiophBridge
import PerfectPower.Generated.ClassLists.K2
import PerfectPower.Generated.ClassLists.K3

/-!
# Decided Diophantine islands

For a fixed curve with a complete-list theorem, membership in the Diophantine set `mordell_dioph k`
is decided by the list. Kept apart from `DiophBridge` so the linted library does not import the
generated class lists.
-/

namespace PerfectPower.DiophBridge

/-- **A decided island**: `y² = x³ + 2` has no point with `x, y ∈ ℕ` (`K2.plus2`). -/
theorem plus2_nat (x y : ℕ) : y ^ 2 ≠ x ^ 3 + 2 := by
  intro h
  have h' : (y : ℤ) ^ 2 = (x : ℤ) ^ 3 + 2 := by exact_mod_cast h
  have := (Generated.ClassLists.K2.plus2 x y).mp h'
  simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at this
  omega

/-- **A decided island**: `y² = x³ + 3` has the single point `(1, 2)` with `x, y ∈ ℕ` (`K3.plus3`). -/
theorem plus3_nat (x y : ℕ) : y ^ 2 = x ^ 3 + 3 ↔ x = 1 ∧ y = 2 := by
  constructor
  · intro h
    have h' : (y : ℤ) ^ 2 = (x : ℤ) ^ 3 + 3 := by exact_mod_cast h
    have := (Generated.ClassLists.K3.plus3 x y).mp h'
    simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil, or_false] at this
    omega
  · rintro ⟨rfl, rfl⟩; norm_num

end PerfectPower.DiophBridge
