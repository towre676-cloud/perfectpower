import PerfectPower.NativeRationalRoots
import PerfectPower.EllipticPointDivision
import PerfectPower.ResiduePopulation
import PerfectPower.PicardLefschetz
namespace PerfectPower.BraidPacket_242ac5af3fd38b1d
open scoped BigOperators
open PerfectPower.PicardLefschetz
private def intersection : Matrix (Fin 2) (Fin 2) ℤ := !![(0),(1);(-1),(0)]
private def cycle_0 : Fin 2 → ℤ := ![(1),(0)]
private def factor_0 : Matrix (Fin 2) (Fin 2) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_0 i * ∑ l, cycle_0 l * intersection l j)
private def cycle_1 : Fin 2 → ℤ := ![(0),(1)]
private def factor_1 : Matrix (Fin 2) (Fin 2) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_1 i * ∑ l, cycle_1 l * intersection l j)
private def cycle_2 : Fin 2 → ℤ := ![(-1),(0)]
private def factor_2 : Matrix (Fin 2) (Fin 2) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_2 i * ∑ l, cycle_2 l * intersection l j)
private def cycle_3 : Fin 2 → ℤ := ![(-1),(0)]
private def factor_3 : Matrix (Fin 2) (Fin 2) ℤ :=
  1 + Matrix.of (fun i j => (-1) * cycle_3 i * ∑ l, cycle_3 l * intersection l j)
private def cycle_4 : Fin 2 → ℤ := ![(0),(1)]
private def factor_4 : Matrix (Fin 2) (Fin 2) ℤ :=
  1 + Matrix.of (fun i j => (-1) * cycle_4 i * ∑ l, cycle_4 l * intersection l j)
private def cycle_5 : Fin 2 → ℤ := ![(1),(0)]
private def factor_5 : Matrix (Fin 2) (Fin 2) ℤ :=
  1 + Matrix.of (fun i j => (-1) * cycle_5 i * ∑ l, cycle_5 l * intersection l j)
private def stage_0 : Matrix (Fin 2) (Fin 2) ℤ := !![(1),(0);(0),(1)]
private def stage_1 : Matrix (Fin 2) (Fin 2) ℤ := !![(1),(1);(0),(1)]
private def stage_2 : Matrix (Fin 2) (Fin 2) ℤ := !![(0),(1);(-1),(1)]
private def stage_3 : Matrix (Fin 2) (Fin 2) ℤ := !![(0),(1);(-1),(0)]
private def stage_4 : Matrix (Fin 2) (Fin 2) ℤ := !![(0),(1);(-1),(1)]
private def stage_5 : Matrix (Fin 2) (Fin 2) ℤ := !![(1),(1);(0),(1)]
private def stage_6 : Matrix (Fin 2) (Fin 2) ℤ := !![(1),(0);(0),(1)]
private theorem step_0 : stage_0 * factor_0 = stage_1 := by decide +kernel
private theorem step_1 : stage_1 * factor_1 = stage_2 := by decide +kernel
private theorem step_2 : stage_2 * factor_2 = stage_3 := by decide +kernel
private theorem step_3 : stage_3 * factor_3 = stage_4 := by decide +kernel
private theorem step_4 : stage_4 * factor_4 = stage_5 := by decide +kernel
private theorem step_5 : stage_5 * factor_5 = stage_6 := by decide +kernel
private def steps : List ((Fin 2 → ℤ) × ℤ) := [(cycle_0, (1)),(cycle_1, (1)),(cycle_2, (1)),(cycle_3, (-1)),(cycle_4, (-1)),(cycle_5, (-1))]
def action : Matrix (Fin 2) (Fin 2) ℤ := wordMatrix intersection steps

theorem word_action_checked : action = !![(1),(0);(0),(1)] := by
  change (((((((1 : Matrix (Fin 2) (Fin 2) ℤ) * factor_0) * factor_1) * factor_2) * factor_3) * factor_4) * factor_5) = stage_6
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℤ) = stage_0 by decide +kernel]
  rw [step_0, step_1, step_2, step_3, step_4, step_5]

theorem integral_symplectic : action.transpose * intersection * action = intersection := by
  rw [word_action_checked]
  decide +kernel
end PerfectPower.BraidPacket_242ac5af3fd38b1d
#print axioms PerfectPower.BraidPacket_242ac5af3fd38b1d.word_action_checked
#print axioms PerfectPower.BraidPacket_242ac5af3fd38b1d.integral_symplectic
namespace PerfectPower.BraidPacket_b6e2fdbea30fa578
open scoped BigOperators
open PerfectPower.PicardLefschetz
private def intersection : Matrix (Fin 4) (Fin 4) ℤ := !![(0),(0),(1),(0);(0),(0),(0),(1);(-1),(0),(0),(0);(0),(-1),(0),(0)]
private def cycle_0 : Fin 4 → ℤ := ![(1),(0),(0),(0)]
private def factor_0 : Matrix (Fin 4) (Fin 4) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_0 i * ∑ l, cycle_0 l * intersection l j)
private def cycle_1 : Fin 4 → ℤ := ![(0),(0),(1),(0)]
private def factor_1 : Matrix (Fin 4) (Fin 4) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_1 i * ∑ l, cycle_1 l * intersection l j)
private def cycle_2 : Fin 4 → ℤ := ![(1),(0),(0),(0)]
private def factor_2 : Matrix (Fin 4) (Fin 4) ℤ :=
  1 + Matrix.of (fun i j => (-1) * cycle_2 i * ∑ l, cycle_2 l * intersection l j)
private def cycle_3 : Fin 4 → ℤ := ![(-1),(1),(0),(0)]
private def factor_3 : Matrix (Fin 4) (Fin 4) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_3 i * ∑ l, cycle_3 l * intersection l j)
private def cycle_4 : Fin 4 → ℤ := ![(0),(0),(0),(1)]
private def factor_4 : Matrix (Fin 4) (Fin 4) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_4 i * ∑ l, cycle_4 l * intersection l j)
private def cycle_5 : Fin 4 → ℤ := ![(0),(-1),(0),(0)]
private def factor_5 : Matrix (Fin 4) (Fin 4) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_5 i * ∑ l, cycle_5 l * intersection l j)
private def stage_0 : Matrix (Fin 4) (Fin 4) ℤ := !![(1),(0),(0),(0);(0),(1),(0),(0);(0),(0),(1),(0);(0),(0),(0),(1)]
private def stage_1 : Matrix (Fin 4) (Fin 4) ℤ := !![(1),(0),(1),(0);(0),(1),(0),(0);(0),(0),(1),(0);(0),(0),(0),(1)]
private def stage_2 : Matrix (Fin 4) (Fin 4) ℤ := !![(0),(0),(1),(0);(0),(1),(0),(0);(-1),(0),(1),(0);(0),(0),(0),(1)]
private def stage_3 : Matrix (Fin 4) (Fin 4) ℤ := !![(0),(0),(1),(0);(0),(1),(0),(0);(-1),(0),(2),(0);(0),(0),(0),(1)]
private def stage_4 : Matrix (Fin 4) (Fin 4) ℤ := !![(0),(0),(1),(0);(0),(1),(-1),(1);(-1),(0),(1),(1);(0),(0),(0),(1)]
private def stage_5 : Matrix (Fin 4) (Fin 4) ℤ := !![(0),(0),(1),(0);(0),(0),(-1),(1);(-1),(-1),(1),(1);(0),(-1),(0),(1)]
private def stage_6 : Matrix (Fin 4) (Fin 4) ℤ := !![(0),(0),(1),(0);(0),(0),(-1),(1);(-1),(-1),(1),(0);(0),(-1),(0),(0)]
private theorem step_0 : stage_0 * factor_0 = stage_1 := by decide +kernel
private theorem step_1 : stage_1 * factor_1 = stage_2 := by decide +kernel
private theorem step_2 : stage_2 * factor_2 = stage_3 := by decide +kernel
private theorem step_3 : stage_3 * factor_3 = stage_4 := by decide +kernel
private theorem step_4 : stage_4 * factor_4 = stage_5 := by decide +kernel
private theorem step_5 : stage_5 * factor_5 = stage_6 := by decide +kernel
private def steps : List ((Fin 4 → ℤ) × ℤ) := [(cycle_0, (1)),(cycle_1, (1)),(cycle_2, (-1)),(cycle_3, (1)),(cycle_4, (1)),(cycle_5, (1))]
def action : Matrix (Fin 4) (Fin 4) ℤ := wordMatrix intersection steps

theorem word_action_checked : action = !![(0),(0),(1),(0);(0),(0),(-1),(1);(-1),(-1),(1),(0);(0),(-1),(0),(0)] := by
  change (((((((1 : Matrix (Fin 4) (Fin 4) ℤ) * factor_0) * factor_1) * factor_2) * factor_3) * factor_4) * factor_5) = stage_6
  rw [show (1 : Matrix (Fin 4) (Fin 4) ℤ) = stage_0 by decide +kernel]
  rw [step_0, step_1, step_2, step_3, step_4, step_5]

theorem integral_symplectic : action.transpose * intersection * action = intersection := by
  rw [word_action_checked]
  decide +kernel
end PerfectPower.BraidPacket_b6e2fdbea30fa578
#print axioms PerfectPower.BraidPacket_b6e2fdbea30fa578.word_action_checked
#print axioms PerfectPower.BraidPacket_b6e2fdbea30fa578.integral_symplectic
namespace PerfectPower.BraidPacket_8d4ae824ca2ae4f4
open scoped BigOperators
open PerfectPower.PicardLefschetz
private def intersection : Matrix (Fin 6) (Fin 6) ℤ := !![(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(1);(-1),(0),(0),(0),(0),(0);(0),(-1),(0),(0),(0),(0);(0),(0),(-1),(0),(0),(0)]
private def cycle_0 : Fin 6 → ℤ := ![(1),(0),(0),(0),(0),(0)]
private def factor_0 : Matrix (Fin 6) (Fin 6) ℤ :=
  1 + Matrix.of (fun i j => (-1) * cycle_0 i * ∑ l, cycle_0 l * intersection l j)
private def cycle_1 : Fin 6 → ℤ := ![(0),(0),(0),(1),(0),(0)]
private def factor_1 : Matrix (Fin 6) (Fin 6) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_1 i * ∑ l, cycle_1 l * intersection l j)
private def cycle_2 : Fin 6 → ℤ := ![(-1),(1),(0),(0),(0),(0)]
private def factor_2 : Matrix (Fin 6) (Fin 6) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_2 i * ∑ l, cycle_2 l * intersection l j)
private def cycle_3 : Fin 6 → ℤ := ![(0),(0),(0),(0),(1),(0)]
private def factor_3 : Matrix (Fin 6) (Fin 6) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_3 i * ∑ l, cycle_3 l * intersection l j)
private def cycle_4 : Fin 6 → ℤ := ![(0),(-1),(1),(0),(0),(0)]
private def factor_4 : Matrix (Fin 6) (Fin 6) ℤ :=
  1 + Matrix.of (fun i j => (-1) * cycle_4 i * ∑ l, cycle_4 l * intersection l j)
private def cycle_5 : Fin 6 → ℤ := ![(0),(0),(0),(0),(0),(1)]
private def factor_5 : Matrix (Fin 6) (Fin 6) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_5 i * ∑ l, cycle_5 l * intersection l j)
private def cycle_6 : Fin 6 → ℤ := ![(0),(0),(-1),(0),(0),(0)]
private def factor_6 : Matrix (Fin 6) (Fin 6) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_6 i * ∑ l, cycle_6 l * intersection l j)
private def cycle_7 : Fin 6 → ℤ := ![(1),(0),(0),(0),(0),(0)]
private def factor_7 : Matrix (Fin 6) (Fin 6) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_7 i * ∑ l, cycle_7 l * intersection l j)
private def stage_0 : Matrix (Fin 6) (Fin 6) ℤ := !![(1),(0),(0),(0),(0),(0);(0),(1),(0),(0),(0),(0);(0),(0),(1),(0),(0),(0);(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(1)]
private def stage_1 : Matrix (Fin 6) (Fin 6) ℤ := !![(1),(0),(0),(-1),(0),(0);(0),(1),(0),(0),(0),(0);(0),(0),(1),(0),(0),(0);(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(1)]
private def stage_2 : Matrix (Fin 6) (Fin 6) ℤ := !![(2),(0),(0),(-1),(0),(0);(0),(1),(0),(0),(0),(0);(0),(0),(1),(0),(0),(0);(-1),(0),(0),(1),(0),(0);(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(1)]
private def stage_3 : Matrix (Fin 6) (Fin 6) ℤ := !![(2),(0),(0),(1),(-2),(0);(0),(1),(0),(-1),(1),(0);(0),(0),(1),(0),(0),(0);(-1),(0),(0),(0),(1),(0);(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(1)]
private def stage_4 : Matrix (Fin 6) (Fin 6) ℤ := !![(2),(2),(0),(1),(-2),(0);(0),(0),(0),(-1),(1),(0);(0),(0),(1),(0),(0),(0);(-1),(-1),(0),(0),(1),(0);(0),(-1),(0),(0),(1),(0);(0),(0),(0),(0),(0),(1)]
private def stage_5 : Matrix (Fin 6) (Fin 6) ℤ := !![(2),(2),(0),(1),(-4),(2);(0),(0),(0),(-1),(1),(0);(0),(0),(1),(0),(1),(-1);(-1),(-1),(0),(0),(2),(-1);(0),(-1),(0),(0),(2),(-1);(0),(0),(0),(0),(0),(1)]
private def stage_6 : Matrix (Fin 6) (Fin 6) ℤ := !![(2),(2),(-2),(1),(-4),(2);(0),(0),(0),(-1),(1),(0);(0),(0),(2),(0),(1),(-1);(-1),(-1),(1),(0),(2),(-1);(0),(-1),(1),(0),(2),(-1);(0),(0),(-1),(0),(0),(1)]
private def stage_7 : Matrix (Fin 6) (Fin 6) ℤ := !![(2),(2),(-2),(1),(-4),(0);(0),(0),(0),(-1),(1),(0);(0),(0),(2),(0),(1),(1);(-1),(-1),(1),(0),(2),(0);(0),(-1),(1),(0),(2),(0);(0),(0),(-1),(0),(0),(0)]
private def stage_8 : Matrix (Fin 6) (Fin 6) ℤ := !![(2),(2),(-2),(3),(-4),(0);(0),(0),(0),(-1),(1),(0);(0),(0),(2),(0),(1),(1);(-1),(-1),(1),(-1),(2),(0);(0),(-1),(1),(0),(2),(0);(0),(0),(-1),(0),(0),(0)]
private theorem step_0 : stage_0 * factor_0 = stage_1 := by decide +kernel
private theorem step_1 : stage_1 * factor_1 = stage_2 := by decide +kernel
private theorem step_2 : stage_2 * factor_2 = stage_3 := by decide +kernel
private theorem step_3 : stage_3 * factor_3 = stage_4 := by decide +kernel
private theorem step_4 : stage_4 * factor_4 = stage_5 := by decide +kernel
private theorem step_5 : stage_5 * factor_5 = stage_6 := by decide +kernel
private theorem step_6 : stage_6 * factor_6 = stage_7 := by decide +kernel
private theorem step_7 : stage_7 * factor_7 = stage_8 := by decide +kernel
private def steps : List ((Fin 6 → ℤ) × ℤ) := [(cycle_0, (-1)),(cycle_1, (1)),(cycle_2, (1)),(cycle_3, (1)),(cycle_4, (-1)),(cycle_5, (1)),(cycle_6, (1)),(cycle_7, (1))]
def action : Matrix (Fin 6) (Fin 6) ℤ := wordMatrix intersection steps

theorem word_action_checked : action = !![(2),(2),(-2),(3),(-4),(0);(0),(0),(0),(-1),(1),(0);(0),(0),(2),(0),(1),(1);(-1),(-1),(1),(-1),(2),(0);(0),(-1),(1),(0),(2),(0);(0),(0),(-1),(0),(0),(0)] := by
  change (((((((((1 : Matrix (Fin 6) (Fin 6) ℤ) * factor_0) * factor_1) * factor_2) * factor_3) * factor_4) * factor_5) * factor_6) * factor_7) = stage_8
  rw [show (1 : Matrix (Fin 6) (Fin 6) ℤ) = stage_0 by decide +kernel]
  rw [step_0, step_1, step_2, step_3, step_4, step_5, step_6, step_7]

theorem integral_symplectic : action.transpose * intersection * action = intersection := by
  rw [word_action_checked]
  decide +kernel
end PerfectPower.BraidPacket_8d4ae824ca2ae4f4
#print axioms PerfectPower.BraidPacket_8d4ae824ca2ae4f4.word_action_checked
#print axioms PerfectPower.BraidPacket_8d4ae824ca2ae4f4.integral_symplectic
namespace PerfectPower.BraidPacket_63eac896ddb7a171
open scoped BigOperators
open PerfectPower.PicardLefschetz
private def intersection : Matrix (Fin 8) (Fin 8) ℤ := !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(0),(0),(1);(-1),(0),(0),(0),(0),(0),(0),(0);(0),(-1),(0),(0),(0),(0),(0),(0);(0),(0),(-1),(0),(0),(0),(0),(0);(0),(0),(0),(-1),(0),(0),(0),(0)]
private def cycle_0 : Fin 8 → ℤ := ![(1),(0),(0),(0),(0),(0),(0),(0)]
private def factor_0 : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_0 i * ∑ l, cycle_0 l * intersection l j)
private def cycle_1 : Fin 8 → ℤ := ![(0),(0),(0),(0),(1),(0),(0),(0)]
private def factor_1 : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_1 i * ∑ l, cycle_1 l * intersection l j)
private def cycle_2 : Fin 8 → ℤ := ![(-1),(1),(0),(0),(0),(0),(0),(0)]
private def factor_2 : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_2 i * ∑ l, cycle_2 l * intersection l j)
private def cycle_3 : Fin 8 → ℤ := ![(0),(0),(0),(0),(0),(1),(0),(0)]
private def factor_3 : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_3 i * ∑ l, cycle_3 l * intersection l j)
private def cycle_4 : Fin 8 → ℤ := ![(0),(-1),(1),(0),(0),(0),(0),(0)]
private def factor_4 : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_4 i * ∑ l, cycle_4 l * intersection l j)
private def cycle_5 : Fin 8 → ℤ := ![(0),(0),(0),(0),(0),(0),(1),(0)]
private def factor_5 : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_5 i * ∑ l, cycle_5 l * intersection l j)
private def cycle_6 : Fin 8 → ℤ := ![(0),(0),(-1),(1),(0),(0),(0),(0)]
private def factor_6 : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_6 i * ∑ l, cycle_6 l * intersection l j)
private def cycle_7 : Fin 8 → ℤ := ![(0),(0),(0),(0),(0),(0),(0),(1)]
private def factor_7 : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_7 i * ∑ l, cycle_7 l * intersection l j)
private def cycle_8 : Fin 8 → ℤ := ![(0),(0),(0),(-1),(0),(0),(0),(0)]
private def factor_8 : Matrix (Fin 8) (Fin 8) ℤ :=
  1 + Matrix.of (fun i j => (1) * cycle_8 i * ∑ l, cycle_8 l * intersection l j)
private def stage_0 : Matrix (Fin 8) (Fin 8) ℤ := !![(1),(0),(0),(0),(0),(0),(0),(0);(0),(1),(0),(0),(0),(0),(0),(0);(0),(0),(1),(0),(0),(0),(0),(0);(0),(0),(0),(1),(0),(0),(0),(0);(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(0),(0),(1)]
private def stage_1 : Matrix (Fin 8) (Fin 8) ℤ := !![(1),(0),(0),(0),(1),(0),(0),(0);(0),(1),(0),(0),(0),(0),(0),(0);(0),(0),(1),(0),(0),(0),(0),(0);(0),(0),(0),(1),(0),(0),(0),(0);(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(0),(0),(1)]
private def stage_2 : Matrix (Fin 8) (Fin 8) ℤ := !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(1),(0),(0),(0),(0),(0),(0);(0),(0),(1),(0),(0),(0),(0),(0);(0),(0),(0),(1),(0),(0),(0),(0);(-1),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(0),(0),(1)]
private def stage_3 : Matrix (Fin 8) (Fin 8) ℤ := !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(1),(0),(0),(-1),(1),(0),(0);(0),(0),(1),(0),(0),(0),(0),(0);(0),(0),(0),(1),(0),(0),(0),(0);(-1),(0),(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(0),(0),(1)]
private def stage_4 : Matrix (Fin 8) (Fin 8) ℤ := !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(-1),(1),(0),(0);(0),(0),(1),(0),(0),(0),(0),(0);(0),(0),(0),(1),(0),(0),(0),(0);(-1),(-1),(0),(0),(0),(1),(0),(0);(0),(-1),(0),(0),(0),(1),(0),(0);(0),(0),(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(0),(0),(1)]
private def stage_5 : Matrix (Fin 8) (Fin 8) ℤ := !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(-1),(1),(0),(0);(0),(0),(1),(0),(0),(-1),(1),(0);(0),(0),(0),(1),(0),(0),(0),(0);(-1),(-1),(0),(0),(0),(0),(1),(0);(0),(-1),(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(0),(0),(1)]
private def stage_6 : Matrix (Fin 8) (Fin 8) ℤ := !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(-1),(1),(0),(0);(0),(0),(0),(0),(0),(-1),(1),(0);(0),(0),(0),(1),(0),(0),(0),(0);(-1),(-1),(-1),(0),(0),(0),(1),(0);(0),(-1),(-1),(0),(0),(0),(1),(0);(0),(0),(-1),(0),(0),(0),(1),(0);(0),(0),(0),(0),(0),(0),(0),(1)]
private def stage_7 : Matrix (Fin 8) (Fin 8) ℤ := !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(-1),(1),(0),(0);(0),(0),(0),(0),(0),(-1),(1),(0);(0),(0),(0),(1),(0),(0),(-1),(1);(-1),(-1),(-1),(0),(0),(0),(0),(1);(0),(-1),(-1),(0),(0),(0),(0),(1);(0),(0),(-1),(0),(0),(0),(0),(1);(0),(0),(0),(0),(0),(0),(0),(1)]
private def stage_8 : Matrix (Fin 8) (Fin 8) ℤ := !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(-1),(1),(0),(0);(0),(0),(0),(0),(0),(-1),(1),(0);(0),(0),(0),(0),(0),(0),(-1),(1);(-1),(-1),(-1),(-1),(0),(0),(0),(1);(0),(-1),(-1),(-1),(0),(0),(0),(1);(0),(0),(-1),(-1),(0),(0),(0),(1);(0),(0),(0),(-1),(0),(0),(0),(1)]
private def stage_9 : Matrix (Fin 8) (Fin 8) ℤ := !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(-1),(1),(0),(0);(0),(0),(0),(0),(0),(-1),(1),(0);(0),(0),(0),(0),(0),(0),(-1),(1);(-1),(-1),(-1),(-1),(0),(0),(0),(0);(0),(-1),(-1),(-1),(0),(0),(0),(0);(0),(0),(-1),(-1),(0),(0),(0),(0);(0),(0),(0),(-1),(0),(0),(0),(0)]
private theorem step_0 : stage_0 * factor_0 = stage_1 := by decide +kernel
private theorem step_1 : stage_1 * factor_1 = stage_2 := by decide +kernel
private theorem step_2 : stage_2 * factor_2 = stage_3 := by decide +kernel
private theorem step_3 : stage_3 * factor_3 = stage_4 := by decide +kernel
private theorem step_4 : stage_4 * factor_4 = stage_5 := by decide +kernel
private theorem step_5 : stage_5 * factor_5 = stage_6 := by decide +kernel
private theorem step_6 : stage_6 * factor_6 = stage_7 := by decide +kernel
private theorem step_7 : stage_7 * factor_7 = stage_8 := by decide +kernel
private theorem step_8 : stage_8 * factor_8 = stage_9 := by decide +kernel
private def steps : List ((Fin 8 → ℤ) × ℤ) := [(cycle_0, (1)),(cycle_1, (1)),(cycle_2, (1)),(cycle_3, (1)),(cycle_4, (1)),(cycle_5, (1)),(cycle_6, (1)),(cycle_7, (1)),(cycle_8, (1))]
def action : Matrix (Fin 8) (Fin 8) ℤ := wordMatrix intersection steps

theorem word_action_checked : action = !![(0),(0),(0),(0),(1),(0),(0),(0);(0),(0),(0),(0),(-1),(1),(0),(0);(0),(0),(0),(0),(0),(-1),(1),(0);(0),(0),(0),(0),(0),(0),(-1),(1);(-1),(-1),(-1),(-1),(0),(0),(0),(0);(0),(-1),(-1),(-1),(0),(0),(0),(0);(0),(0),(-1),(-1),(0),(0),(0),(0);(0),(0),(0),(-1),(0),(0),(0),(0)] := by
  change ((((((((((1 : Matrix (Fin 8) (Fin 8) ℤ) * factor_0) * factor_1) * factor_2) * factor_3) * factor_4) * factor_5) * factor_6) * factor_7) * factor_8) = stage_9
  rw [show (1 : Matrix (Fin 8) (Fin 8) ℤ) = stage_0 by decide +kernel]
  rw [step_0, step_1, step_2, step_3, step_4, step_5, step_6, step_7, step_8]

theorem integral_symplectic : action.transpose * intersection * action = intersection := by
  rw [word_action_checked]
  decide +kernel
end PerfectPower.BraidPacket_63eac896ddb7a171
#print axioms PerfectPower.BraidPacket_63eac896ddb7a171.word_action_checked
#print axioms PerfectPower.BraidPacket_63eac896ddb7a171.integral_symplectic
namespace PerfectPower.BraidPacket_effc2e59da94fea1
open scoped BigOperators
open PerfectPower.PicardLefschetz
private def intersection : Matrix (Fin 4) (Fin 4) ℤ := !![(0),(0),(1),(0);(0),(0),(0),(1);(-1),(0),(0),(0);(0),(-1),(0),(0)]

private def stage_0 : Matrix (Fin 4) (Fin 4) ℤ := !![(1),(0),(0),(0);(0),(1),(0),(0);(0),(0),(1),(0);(0),(0),(0),(1)]

private def steps : List ((Fin 4 → ℤ) × ℤ) := []
def action : Matrix (Fin 4) (Fin 4) ℤ := wordMatrix intersection steps

theorem word_action_checked : action = !![(1),(0),(0),(0);(0),(1),(0),(0);(0),(0),(1),(0);(0),(0),(0),(1)] := by
  decide +kernel

theorem integral_symplectic : action.transpose * intersection * action = intersection := by
  rw [word_action_checked]
  decide +kernel
end PerfectPower.BraidPacket_effc2e59da94fea1
#print axioms PerfectPower.BraidPacket_effc2e59da94fea1.word_action_checked
#print axioms PerfectPower.BraidPacket_effc2e59da94fea1.integral_symplectic
