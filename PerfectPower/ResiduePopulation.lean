import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Nonenumerating counts for finite unions of disjoint residue cells. -/
namespace PerfectPower.ResiduePopulation
open scoped BigOperators

/-- One bounded arithmetic progression in original integer coordinates. -/
structure Cell where
  /-- Inclusive lower endpoint. -/
  lower : ℤ
  /-- Inclusive upper endpoint. -/
  upper : ℤ
  /-- Positive lattice period, checked by the count theorem. -/
  modulus : ℤ
  /-- Canonical residue, checked to lie below the period. -/
  residue : ℤ

/-- Original-coordinate cell predicate. -/
def accepts (c : Cell) (x : ℤ) : Prop :=
  c.lower ≤ x ∧ x ≤ c.upper ∧ x % c.modulus = c.residue

instance (c : Cell) : DecidablePred (accepts c) := fun _ => inferInstanceAs
  (Decidable (_ ∧ _ ∧ _))

/-- Native finite set with deduplication semantics. -/
def values (c : Cell) : Finset ℤ := (Finset.Icc c.lower c.upper).filter (accepts c)

@[simp] theorem mem_values (c : Cell) (x : ℤ) : x ∈ values c ↔ accepts c x := by
  simp only [values, Finset.mem_filter, Finset.mem_Icc, accepts]
  tauto

/-- The floor-quotient count does not enumerate the interval. -/
def count (c : Cell) : ℕ :=
  ((c.upper-c.residue)/c.modulus - (c.lower-1-c.residue)/c.modulus).toNat

private theorem coordinate (m r n : ℤ) (hr : 0 ≤ r) (hrm : r < m) :
    n % m = r ↔ ∃ k : ℤ, n = r + m*k := by
  constructor
  · intro h
    exact ⟨n/m, by simpa [h] using (Int.emod_add_ediv n m).symm⟩
  · rintro ⟨k,rfl⟩
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr hrm]

private theorem bounds (lo hi m r k : ℤ) (hm : 0 < m) :
    lo ≤ r+m*k ∧ r+m*k ≤ hi ↔
      (lo-1-r)/m+1 ≤ k ∧ k ≤ (hi-r)/m := by
  rw [show (lo-1-r)/m+1 ≤ k ↔ (lo-1-r)/m < k by omega,
    Int.ediv_lt_iff_lt_mul hm, Int.le_ediv_iff_mul_le hm]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

/-- A residue cell is an injective image of its exact lattice interval. -/
theorem interval_image (c : Cell) (hm : 0 < c.modulus)
    (hr : 0 ≤ c.residue) (hrm : c.residue < c.modulus) :
    values c = (Finset.Icc ((c.lower-1-c.residue)/c.modulus+1)
      ((c.upper-c.residue)/c.modulus)).image (fun k => c.residue+c.modulus*k) := by
  ext x
  simp only [mem_values, accepts, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨hlo,hhi,hx⟩
    obtain ⟨k,rfl⟩ := (coordinate c.modulus c.residue x hr hrm).mp hx
    exact ⟨k,(bounds _ _ _ _ _ hm).mp ⟨hlo,hhi⟩,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨((bounds _ _ _ _ _ hm).mpr hk).1,
      ((bounds _ _ _ _ _ hm).mpr hk).2,(coordinate _ _ _ hr hrm).mpr ⟨k,rfl⟩⟩

/-- Kernel theorem for one nonenumerated cell count. -/
theorem card_values (c : Cell) (hm : 0 < c.modulus)
    (hr : 0 ≤ c.residue) (hrm : c.residue < c.modulus) :
    (values c).card = count c := by
  rw [interval_image c hm hr hrm, Finset.card_image_of_injective]
  · rw [Int.card_Icc]
    unfold count
    congr 1
    ring
  · intro a b h
    exact mul_left_cancel₀ (ne_of_gt hm) (add_left_cancel h)

/-- Union of a finite indexed family of cells. -/
def population {ι : Type*} [Fintype ι] (cells : ι → Cell) : Finset ℤ :=
  Finset.univ.biUnion (fun i => values (cells i))

/-- Source membership remains in original coordinates. -/
theorem population_complete {ι : Type*} [Fintype ι] (cells : ι → Cell) (x : ℤ) :
    x ∈ population cells ↔ ∃ i, accepts (cells i) x := by
  simp [population]

/-- Disjoint cells can be counted by short floor arithmetic, regardless of width. -/
theorem population_count {ι : Type*} [Fintype ι] (cells : ι → Cell)
    (hv : ∀ i, 0 < (cells i).modulus ∧ 0 ≤ (cells i).residue ∧
      (cells i).residue < (cells i).modulus)
    (hd : ∀ i j, i ≠ j → Disjoint (values (cells i)) (values (cells j))) :
    (population cells).card = ∑ i, count (cells i) := by
  rw [population, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact card_values _ (hv i).1 (hv i).2.1 (hv i).2.2
  · intro i _ j _ hij
    exact hd i j hij

end PerfectPower.ResiduePopulation
