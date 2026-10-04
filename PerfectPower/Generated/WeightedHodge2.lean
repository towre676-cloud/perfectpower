import PerfectPower.WeightedHodge
import PerfectPower.SymplecticTransport
namespace PerfectPower.ParallelCertificates
open Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def hodge_2_G : Matrix (Fin 9) (Fin 9) ℚ := !![0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0]
def hodge_2_B : Matrix (Fin 9) (Fin 9) ℚ := !![(9/38),(4/19),0,0,(-21/38),(4/19),0,0,0;
(3/19),(9/19),0,0,(-7/19),(-10/19),0,0,0;
0,0,(27/61),(12/61),0,0,0,(-34/61),(-22/61);
0,0,(10/61),(18/61),0,0,0,(10/61),(-33/61);
(-9/38),(-4/19),0,0,(21/38),(-4/19),0,0,0;
(3/38),(-5/19),0,0,(-7/38),(14/19),0,0,0;
0,0,0,0,0,0,1,0,0;
0,0,(-17/61),(6/61),0,0,0,(44/61),(-11/61);
0,0,(-10/61),(-18/61),0,0,0,(-10/61),(33/61)]
def hodge_2_H : Matrix (Fin 9) (Fin 9) ℚ := !![(29/38),(-4/19),0,0,(21/38),(-4/19),0,0,0;
(-3/19),(10/19),0,0,(7/19),(10/19),0,0,0;
0,0,(34/61),(-12/61),0,0,0,(34/61),(22/61);
0,0,(-10/61),(43/61),0,0,0,(-10/61),(33/61);
(9/38),(4/19),0,0,(17/38),(4/19),0,0,0;
(-3/38),(5/19),0,0,(7/38),(5/19),0,0,0;
0,0,0,0,0,0,0,0,0;
0,0,(17/61),(-6/61),0,0,0,(17/61),(11/61);
0,0,(10/61),(18/61),0,0,0,(10/61),(28/61)]
def hodge_2_L : Matrix (Fin 9) (Fin 9) ℚ := !![(11/10),(4/5),0,0,(-77/30),(4/3),0,0,0;
(3/5),(48/35),0,0,(-7/5),(-8/7),(9/7),0,0;
0,0,(9/8),(3/5),0,0,(9/8),(-5/4),(-11/10);
0,0,(1/2),(19/15),0,0,0,(10/9),(-209/90);
(-11/10),(-4/5),0,0,(77/30),(-4/3),0,0,0;
(1/2),(-4/7),0,0,(-7/6),(52/21),(-9/7),0,0;
0,(4/7),(5/8),0,0,(-8/7),(135/56),(-5/4),0;
0,0,(-5/8),(2/3),0,0,(-9/8),(85/36),(-11/9);
0,0,(-1/2),(-19/15),0,0,0,(-10/9),(209/90)]
def hodge_2_M : Matrix (Fin 9) (Fin 9) ℚ := Matrix.diagonal (fun i => (i.val+3 : ℚ))
theorem hodge_2_checked : hodge_2_G*hodge_2_G=hodge_2_G ∧ hodge_2_B*hodge_2_B=hodge_2_B ∧ hodge_2_G*hodge_2_B=0 ∧ hodge_2_B*hodge_2_G=0 ∧ hodge_2_G+hodge_2_B+hodge_2_H=1 ∧ hodge_2_L*hodge_2_H=0 ∧ hodge_2_H.transpose*hodge_2_M=hodge_2_M*hodge_2_H ∧ Matrix.trace hodge_2_H=4 := by decide +kernel
theorem hodge_2_idempotent : hodge_2_H*hodge_2_H=hodge_2_H := by
  have hc := hodge_2_checked
  have he : hodge_2_H=1-hodge_2_G-hodge_2_B := by rw [← hc.2.2.2.2.1]; abel
  rw [he]
  exact (PerfectPower.WeightedHodge.harmonic_projector hodge_2_G hodge_2_B hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1).1
end PerfectPower.ParallelCertificates
