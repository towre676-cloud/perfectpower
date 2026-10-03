import Mathlib.NumberTheory.Dioph
import PerfectPower.Basic

/-!
# The repository's hit predicate and Diophantine sets (Mathlib's `Dioph`)

Mathlib formalizes Diophantine sets of natural-number vectors (`Dioph`) and Matiyasevich's step in
the negative solution of Hilbert's tenth problem: powering with a **variable** exponent is
Diophantine (`Dioph.pow_dioph`).  Mathlib does not contain the full DPRM theorem or the
undecidability statement itself; this module uses only what it proves.

* `isHit_nat_iff`: on natural numbers, the repository's `IsHit d v` (`∃ m : ℤ, v = m ^ d`) is
  exactly "a natural `d`-th power".
* **Variable exponent** (`perfectPower_dioph`): `{v | ∃ m d, 2 ≤ d ∧ v = m ^ d}` is Diophantine,
  through `pow_dioph`.  This is the relation whose Diophantine definability is the hard part of
  Matiyasevich's theorem.
* **Fixed exponent** (`fixedPower_dioph`, `mordell_dioph`): for fixed `d` or fixed `k` the
  relations are plainly polynomial.
* **A decided island** (`DiophBridgeCurves.plus2_nat`, `plus3_nat`): for a fixed curve with a complete-list theorem,
  membership in the Diophantine set is decided by that list.  This is a statement about one
  equation; it does not contradict the absence of an algorithm for all equations.
-/

namespace PerfectPower.DiophBridge

open Dioph

/-- **The hit predicate on natural numbers**: `IsHit d v ↔ v` is a natural `d`-th power. -/
theorem isHit_nat_iff (d v : ℕ) : IsHit d v ↔ ∃ m : ℕ, v = m ^ d := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m.natAbs, ?_⟩
    have h0 : (0 : ℤ) ≤ m ^ d := hm ▸ Nat.cast_nonneg v
    have : ((m.natAbs ^ d : ℕ) : ℤ) = m ^ d := by
      push_cast
      rw [← abs_pow, abs_of_nonneg h0]
    exact_mod_cast hm.trans this.symm
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; rfl⟩

/-- `d :: m :: v`, the auxiliary set behind `perfectPower_dioph`. -/
theorem aux_dioph : Dioph {v : Vector3 ℕ 3 | 2 ≤ v &0 ∧ v &2 = v &1 ^ v &0} :=
  Dioph.inter (Dioph.le_dioph (Dioph.const_dioph 2) (Dioph.proj_dioph_of_nat 0))
    (Dioph.eq_dioph (Dioph.proj_dioph_of_nat 2)
      (Dioph.pow_dioph (Dioph.proj_dioph_of_nat 1) (Dioph.proj_dioph_of_nat 0)))

/-- **Variable-exponent perfect powers are Diophantine** (Matiyasevich's step, `pow_dioph`). -/
theorem perfectPower_dioph : Dioph {v : Vector3 ℕ 1 | ∃ m d : ℕ, 2 ≤ d ∧ v &0 = m ^ d} := by
  have h2 := vec_ex1_dioph 2 aux_dioph
  have h1 := vec_ex1_dioph 1 h2
  refine h1.ext fun v => ?_
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, d, hd, hv⟩
    exact ⟨m, d, hd, hv⟩
  · rintro ⟨m, d, hd, hv⟩
    exact ⟨m, d, hd, hv⟩

/-- **Fixed exponent**: `{v | ∃ m, v = m ^ d}` is Diophantine (a polynomial relation). -/
theorem fixedPower_dioph (d : ℕ) : Dioph {v : Vector3 ℕ 1 | ∃ m : ℕ, v &0 = m ^ d} := by
  have h : Dioph {v : Vector3 ℕ 2 | v &1 = v &0 ^ d} :=
    Dioph.eq_dioph (Dioph.proj_dioph_of_nat 1) (Dioph.pow_dioph (Dioph.proj_dioph_of_nat 0) (Dioph.const_dioph d))
  refine (vec_ex1_dioph 1 h).ext fun v => ?_
  simp only [Set.mem_setOf_eq]
  exact ⟨fun ⟨m, hm⟩ => ⟨m, hm⟩, fun ⟨m, hm⟩ => ⟨m, hm⟩⟩

/-- **A fixed Mordell curve** `y² = x³ + k` on natural numbers is a Diophantine set. -/
theorem mordell_dioph (k : ℕ) : Dioph {v : Vector3 ℕ 2 | v &1 ^ 2 = v &0 ^ 3 + k} :=
  Dioph.eq_dioph (Dioph.pow_dioph (Dioph.proj_dioph_of_nat 1) (Dioph.const_dioph 2))
    (Dioph.add_dioph (Dioph.pow_dioph (Dioph.proj_dioph_of_nat 0) (Dioph.const_dioph 3)) (Dioph.const_dioph k))

end PerfectPower.DiophBridge
