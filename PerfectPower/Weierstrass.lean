import Mathlib.Tactic
import Mathlib.Data.Finsupp.Basic

/-!
# General Weierstrass models: completing the square, and transport defects

**Completing the square** (`complete_square`).  For
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`, put `Y = 2y + a₁x + a₃`; then
`Y² = 4x³ + (a₁² + 4a₂)x² + (2a₁a₃ + 4a₄)x + a₃² + 4a₆`, and conversely.  The integral inverse
`y = (Y − a₁x − a₃)/2` needs `Y ≡ a₁x + a₃ (mod 2)`; that parity is *implied* by the second
equation (`parity_of_sq`), so `readout` needs no extra hypothesis.  This is the exact interface
for reading integral points of a general model off a model `Y² = cubic`; it proves nothing about
which points exist.

**Transport defects** (`defect_comp`).  A list `A` gives the chain `[A] = Σ_{a ∈ A} e_a` (with
multiplicities).  The defect of a map `φ` from `A` to the list `B` is `Δ_φ = φ_#[A] − [B]`; then
`Δ_{ψ ∘ φ} = ψ_# Δ_φ + Δ_ψ`.  This keeps exact account of merges and multiplicities along a chain
of transports.  It is separate from solution `Finset`s, which forget multiplicity on purpose.

Both are from the tau-crystal salvage review; the archive's Lean files are not imported.
-/

namespace PerfectPower.Weierstrass

/-- The right-hand side after completing the square. -/
def quartRHS (a1 a2 a3 a4 a6 x : ℤ) : ℤ :=
  4 * x ^ 3 + (a1 ^ 2 + 4 * a2) * x ^ 2 + (2 * a1 * a3 + 4 * a4) * x + a3 ^ 2 + 4 * a6

theorem complete_square (a1 a2 a3 a4 a6 x y : ℤ) :
    y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x ^ 2 + a4 * x + a6 ↔
      (2 * y + a1 * x + a3) ^ 2 = quartRHS a1 a2 a3 a4 a6 x := by
  unfold quartRHS
  constructor
  · intro h; linear_combination 4 * h
  · intro h
    apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
    linear_combination h

/-- The parity needed for the integral inverse follows from the equation itself. -/
theorem parity_of_sq {a1 a2 a3 a4 a6 x Y : ℤ} (h : Y ^ 2 = quartRHS a1 a2 a3 a4 a6 x) :
    (2 : ℤ) ∣ Y - (a1 * x + a3) := by
  have h4 : (4 : ℤ) ∣ (Y - (a1 * x + a3)) * (Y + (a1 * x + a3)) :=
    ⟨x ^ 3 + a2 * x ^ 2 + a4 * x + a6, by unfold quartRHS at h; linear_combination h⟩
  by_contra hodd
  have h2 : ¬ (2 : ℤ) ∣ Y + (a1 * x + a3) := by
    intro h'
    apply hodd
    have : Y - (a1 * x + a3) = (Y + (a1 * x + a3)) - 2 * (a1 * x + a3) := by ring
    rw [this]
    exact dvd_sub h' (dvd_mul_right _ _)
  have : ¬ (2 : ℤ) ∣ (Y - (a1 * x + a3)) * (Y + (a1 * x + a3)) := by
    intro hd
    rcases Int.prime_two.dvd_mul.mp hd with h' | h'
    · exact hodd h'
    · exact h2 h'
  exact this (dvd_trans ⟨2, by norm_num⟩ h4)

/-- **The integral readout**: a solution of the completed equation gives a point of the general
model, with `y = (Y − a₁x − a₃)/2`. -/
theorem readout {a1 a2 a3 a4 a6 x Y : ℤ} (h : Y ^ 2 = quartRHS a1 a2 a3 a4 a6 x) :
    ∃ y : ℤ, 2 * y + a1 * x + a3 = Y ∧ y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x ^ 2 + a4 * x + a6 := by
  obtain ⟨y, hy⟩ := parity_of_sq h
  refine ⟨y, by linarith, ?_⟩
  rw [complete_square]
  have : 2 * y + a1 * x + a3 = Y := by linarith
  rw [this, h]

/-! ### Transport defects -/

open Finsupp

/-- The chain `[A] = Σ_{a ∈ A} e_a` of a list, with multiplicities. -/
noncomputable def chain {α : Type*} (A : List α) : α →₀ ℤ := (A.map fun a => single a 1).sum

/-- The defect of `φ` from the list `A` to the list `B`: `φ_#[A] − [B]`. -/
noncomputable def defect {α β : Type*} (φ : α → β) (A : List α) (B : List β) : β →₀ ℤ :=
  mapDomain φ (chain A) - chain B

/-- **The cocycle identity** `Δ_{ψ ∘ φ} = ψ_# Δ_φ + Δ_ψ`. -/
theorem defect_comp {α β γ : Type*} (φ : α → β) (ψ : β → γ) (A : List α) (B : List β) (C : List γ) :
    defect (ψ ∘ φ) A C = mapDomain ψ (defect φ A B) + defect ψ B C := by
  simp only [defect]
  have hsub : mapDomain ψ (mapDomain φ (chain A) - chain B) =
      mapDomain ψ (mapDomain φ (chain A)) - mapDomain ψ (chain B) := by
    rw [eq_sub_iff_add_eq, ← mapDomain_add, sub_add_cancel]
  rw [hsub, mapDomain_comp]
  abel

/-- The chain of a mapped list is the pushed chain: a map with no merges and no losses has defect `0`. -/
theorem chain_map {α β : Type*} (φ : α → β) (A : List α) : chain (A.map φ) = mapDomain φ (chain A) := by
  induction A with
  | nil => simp [chain]
  | cons a A ih =>
    simp only [chain, List.map_cons, List.sum_cons] at ih ⊢
    rw [mapDomain_add, mapDomain_single, ih]

theorem defect_map {α β : Type*} (φ : α → β) (A : List α) : defect φ A (A.map φ) = 0 := by
  simp [defect, chain_map]

end PerfectPower.Weierstrass
