import PerfectPower.WeightedHodge
import PerfectPower.SymplecticTransport
namespace PerfectPower.ParallelCertificates
open Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def hodge_1_G : Matrix (Fin 3) (Fin 3) ℚ := !![0,0,0;
0,0,0;
0,0,0]
def hodge_1_B : Matrix (Fin 3) (Fin 3) ℚ := !![(1/4),(1/3),(-5/12);
(1/4),(1/3),(-5/12);
(-1/4),(-1/3),(5/12)]
def hodge_1_H : Matrix (Fin 3) (Fin 3) ℚ := !![(3/4),(-1/3),(5/12);
(-1/4),(2/3),(5/12);
(1/4),(1/3),(7/12)]
def hodge_1_L : Matrix (Fin 3) (Fin 3) ℚ := !![(11/10),(22/15),(-11/6);
(11/10),(22/15),(-11/6);
(-11/10),(-22/15),(11/6)]
def hodge_1_M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.diagonal (fun i => (i.val+3 : ℚ))
theorem hodge_1_checked : hodge_1_G*hodge_1_G=hodge_1_G ∧ hodge_1_B*hodge_1_B=hodge_1_B ∧ hodge_1_G*hodge_1_B=0 ∧ hodge_1_B*hodge_1_G=0 ∧ hodge_1_G+hodge_1_B+hodge_1_H=1 ∧ hodge_1_L*hodge_1_H=0 ∧ hodge_1_H.transpose*hodge_1_M=hodge_1_M*hodge_1_H ∧ Matrix.trace hodge_1_H=2 := by decide +kernel
theorem hodge_1_idempotent : hodge_1_H*hodge_1_H=hodge_1_H := by
  have hc := hodge_1_checked
  have he : hodge_1_H=1-hodge_1_G-hodge_1_B := by rw [← hc.2.2.2.2.1]; abel
  rw [he]
  exact (PerfectPower.WeightedHodge.harmonic_projector hodge_1_G hodge_1_B hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1).1
end PerfectPower.ParallelCertificates
