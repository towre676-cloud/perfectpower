import PerfectPower.IntegralKernelWitness
import PerfectPower.ResidueDeterminantCertificate
import Mathlib.Tactic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Kernel_02bb339b209d7de9
open Matrix
def A : Matrix (Fin 2) (Fin 2) ℤ := !![(1), (0); (0), (1)]
def K : Matrix (Fin 2) (Fin 2) ℤ := !![(0), (0); (0), (0)]
theorem annihilates : A * K = 0 := by decide +kernel
def B : Matrix (Fin 2) (Fin 2) ℤ := !![(1), (0); (0), (1)]
def rowIndices : Fin 2 → Fin 2 := ![(0), (1)]
theorem B_is_selected : B = (fun i j => A (rowIndices i) j) := by decide +kernel
theorem K_is_kernel : K = PerfectPower.IntegralKernelWitness.integralKernelMatrix B := by decide +kernel
theorem gram_nonzero : (B * B.transpose).det ≠ 0 := by decide +kernel
theorem rational_spanning (x : Fin 2 → ℚ) (hx : (A.map (Int.castRingHom ℚ)) *ᵥ x = 0) :
    x ∈ Submodule.span ℚ (Set.range (fun j => fun i => (K i j : ℚ))) := by
  let Bq := B.map (Int.castRingHom ℚ)
  have hb : Bq *ᵥ x = 0 := by
    ext i
    simpa only [Bq, B_is_selected, Matrix.map_apply, Matrix.mulVec] using congrFun hx (rowIndices i)
  have hd : (Bq * Bq.transpose).det ≠ 0 := by
    have he := (Int.castRingHom ℚ).map_det (B * B.transpose)
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at he
    change ((B * B.transpose).det : ℚ) = (Bq * Bq.transpose).det at he
    rw [← he]
    exact_mod_cast gram_nonzero
  have hs := PerfectPower.IntegralKernelWitness.mem_span_integralKernelMatrix_columns Bq hd x hb
  have hk : PerfectPower.IntegralKernelWitness.integralKernelMatrix Bq = K.map (Int.castRingHom ℚ) := by
    simpa only [K_is_kernel, Bq] using (PerfectPower.IntegralKernelWitness.integralKernelMatrix_map (Int.castRingHom ℚ) B).symm
  simpa only [hk, Matrix.map_apply] using hs
#print axioms rational_spanning
#print axioms annihilates
end Kernel_02bb339b209d7de9
