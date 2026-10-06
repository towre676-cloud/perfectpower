import PerfectPower.NativeRationalRoots
import PerfectPower.EllipticPointDivision
import PerfectPower.ResiduePopulation
import PerfectPower.PicardLefschetz
namespace PerfectPower.ResiduePacket_db96a4a822f92ced
open PerfectPower.ResiduePopulation
private def original (x : ℤ) : Prop := ((((1000000000000000000000000000000) + x * (((1) + x * (0)))) ≥ (0)) ∧ (((-1000000000000000000000000000000) + x * (((1) + x * (0)))) ≤ (0)) ∧ (((((0) + x * (((1) + x * (0))))) % (6)) = (1)) ∧ (((((0) + x * (((1) + x * (0))))) % (9)) = (4)))
private def cells : Fin 1 → Cell := ![⟨(-999999999999999999999999999999),(999999999999999999999999999998),(18),(13)⟩]

theorem source_complete (x : ℤ) : original x ↔ x ∈ population cells := by
  rw [population_complete]
  simp [original, cells, accepts, Fin.exists_fin_succ] <;> omega

private theorem valid_cells : ∀ i, 0 < (cells i).modulus ∧ 0 ≤ (cells i).residue ∧
    (cells i).residue < (cells i).modulus := by
  intro i
  fin_cases i <;> norm_num [cells]

private theorem disjoint_cells : ∀ i j, i ≠ j →
    Disjoint (values (cells i)) (values (cells j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rw [mem_values] at hx hy
  fin_cases i <;> fin_cases j <;> simp [cells, accepts] at hx hy hij <;> omega

theorem count_checked : (population cells).card = 111111111111111111111111111111 := by
  rw [population_count cells valid_cells disjoint_cells]
  norm_num [cells, count, Fin.sum_univ_succ] <;> decide +kernel
end PerfectPower.ResiduePacket_db96a4a822f92ced
#print axioms PerfectPower.ResiduePacket_db96a4a822f92ced.source_complete
#print axioms PerfectPower.ResiduePacket_db96a4a822f92ced.count_checked
namespace PerfectPower.ResiduePacket_75c940a75a65b7ec
open PerfectPower.ResiduePopulation
private def original (x : ℤ) : Prop := ((((50) + x * (((1) + x * (0)))) ≥ (0)) ∧ (((-50) + x * (((1) + x * (0)))) ≤ (0)) ∧ ((((((0) + x * (((1) + x * (0))))) % (3)) = (0)) ∨ (((((0) + x * (((1) + x * (0))))) % (4)) = (1))) ∧ (¬ (((((0) + x * (((1) + x * (0))))) % (6)) = (0))))
private def cells : Fin 4 → Cell := ![⟨(-49),(49),(12),(1)⟩,⟨(-49),(49),(12),(3)⟩,⟨(-49),(49),(12),(5)⟩,⟨(-49),(49),(12),(9)⟩]

theorem source_complete (x : ℤ) : original x ↔ x ∈ population cells := by
  rw [population_complete]
  simp [original, cells, accepts, Fin.exists_fin_succ] <;> omega

private theorem valid_cells : ∀ i, 0 < (cells i).modulus ∧ 0 ≤ (cells i).residue ∧
    (cells i).residue < (cells i).modulus := by
  intro i
  fin_cases i <;> norm_num [cells]

private theorem disjoint_cells : ∀ i j, i ≠ j →
    Disjoint (values (cells i)) (values (cells j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rw [mem_values] at hx hy
  fin_cases i <;> fin_cases j <;> simp [cells, accepts] at hx hy hij <;> omega

theorem count_checked : (population cells).card = 33 := by
  rw [population_count cells valid_cells disjoint_cells]
  norm_num [cells, count, Fin.sum_univ_succ] <;> decide +kernel
end PerfectPower.ResiduePacket_75c940a75a65b7ec
#print axioms PerfectPower.ResiduePacket_75c940a75a65b7ec.source_complete
#print axioms PerfectPower.ResiduePacket_75c940a75a65b7ec.count_checked
namespace PerfectPower.ResiduePacket_529921e165bf028e
open PerfectPower.ResiduePopulation
private def original (x : ℤ) : Prop := ((((40) + x * (((1) + x * (0)))) ≥ (0)) ∧ (((-40) + x * (((1) + x * (0)))) ≤ (0)) ∧ (((((3) + x * (((-2) + x * (0))))) % (5)) ≥ (2)))
private def cells : Fin 6 → Cell := ![⟨(-40),(38),(5),(0)⟩,⟨(-40),(38),(5),(2)⟩,⟨(-40),(38),(5),(3)⟩,⟨(40),(40),(5),(0)⟩,⟨(40),(40),(5),(2)⟩,⟨(40),(40),(5),(3)⟩]

theorem source_complete (x : ℤ) : original x ↔ x ∈ population cells := by
  rw [population_complete]
  simp [original, cells, accepts, Fin.exists_fin_succ] <;> omega

private theorem valid_cells : ∀ i, 0 < (cells i).modulus ∧ 0 ≤ (cells i).residue ∧
    (cells i).residue < (cells i).modulus := by
  intro i
  fin_cases i <;> norm_num [cells]

private theorem disjoint_cells : ∀ i j, i ≠ j →
    Disjoint (values (cells i)) (values (cells j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rw [mem_values] at hx hy
  fin_cases i <;> fin_cases j <;> simp [cells, accepts] at hx hy hij <;> omega

theorem count_checked : (population cells).card = 49 := by
  rw [population_count cells valid_cells disjoint_cells]
  norm_num [cells, count, Fin.sum_univ_succ] <;> decide +kernel
end PerfectPower.ResiduePacket_529921e165bf028e
#print axioms PerfectPower.ResiduePacket_529921e165bf028e.source_complete
#print axioms PerfectPower.ResiduePacket_529921e165bf028e.count_checked
namespace PerfectPower.ResiduePacket_fcbcf165908dd18a
open PerfectPower.ResiduePopulation
private def original (x : ℤ) : Prop := False
private def cells : Fin 0 → Cell := fun i => Fin.elim0 i

theorem source_complete (x : ℤ) : original x ↔ x ∈ population cells := by
  rw [population_complete]
  simp [original, cells, accepts, Fin.exists_fin_succ] <;> omega

private theorem valid_cells : ∀ i, 0 < (cells i).modulus ∧ 0 ≤ (cells i).residue ∧
    (cells i).residue < (cells i).modulus := by
  intro i
  fin_cases i <;> norm_num [cells]

private theorem disjoint_cells : ∀ i j, i ≠ j →
    Disjoint (values (cells i)) (values (cells j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rw [mem_values] at hx hy
  fin_cases i <;> fin_cases j <;> simp [cells, accepts] at hx hy hij <;> omega

theorem count_checked : (population cells).card = 0 := by
  rw [population_count cells valid_cells disjoint_cells]
  norm_num [cells, count, Fin.sum_univ_succ] <;> decide +kernel
end PerfectPower.ResiduePacket_fcbcf165908dd18a
#print axioms PerfectPower.ResiduePacket_fcbcf165908dd18a.source_complete
#print axioms PerfectPower.ResiduePacket_fcbcf165908dd18a.count_checked
namespace PerfectPower.ResiduePacket_001712ad3c093b50
open PerfectPower.ResiduePopulation
private def original (x : ℤ) : Prop := ((((20) + x * (((1) + x * (0)))) ≥ (0)) ∧ (((-20) + x * (((1) + x * (0)))) ≤ (0)) ∧ (((((0) + x * (((1) + x * (0))))) % (6)) = (1)) ∧ (((((0) + x * (((1) + x * (0))))) % (9)) = (2)))
private def cells : Fin 0 → Cell := fun i => Fin.elim0 i

theorem source_complete (x : ℤ) : original x ↔ x ∈ population cells := by
  rw [population_complete]
  simp [original, cells, accepts, Fin.exists_fin_succ] <;> omega

private theorem valid_cells : ∀ i, 0 < (cells i).modulus ∧ 0 ≤ (cells i).residue ∧
    (cells i).residue < (cells i).modulus := by
  intro i
  fin_cases i <;> norm_num [cells]

private theorem disjoint_cells : ∀ i j, i ≠ j →
    Disjoint (values (cells i)) (values (cells j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rw [mem_values] at hx hy
  fin_cases i <;> fin_cases j <;> simp [cells, accepts] at hx hy hij <;> omega

theorem count_checked : (population cells).card = 0 := by
  rw [population_count cells valid_cells disjoint_cells]
  norm_num [cells, count, Fin.sum_univ_succ] <;> decide +kernel
end PerfectPower.ResiduePacket_001712ad3c093b50
#print axioms PerfectPower.ResiduePacket_001712ad3c093b50.source_complete
#print axioms PerfectPower.ResiduePacket_001712ad3c093b50.count_checked
