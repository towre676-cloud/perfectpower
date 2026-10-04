import PerfectPower.WeightedHodge
import PerfectPower.SymplecticTransport
namespace PerfectPower.ParallelCertificates
open Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def surface_cli_square_torus_O : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;
-1,0]
def surface_cli_square_torus_S : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;
0,1]
def surface_cli_square_torus_I : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;
0,1]
def surface_cli_square_torus_J : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;
-1,0]
theorem surface_cli_square_torus_checked : surface_cli_square_torus_S*surface_cli_square_torus_I=1 ∧ surface_cli_square_torus_I*surface_cli_square_torus_S=1 ∧ surface_cli_square_torus_S.transpose*surface_cli_square_torus_O*surface_cli_square_torus_S=surface_cli_square_torus_J ∧ surface_cli_square_torus_O.transpose = -surface_cli_square_torus_O := by decide +kernel
def surface_genus_four_O : Matrix (Fin 8) (Fin 8) ℤ := !![0,1,0,0,1,-1,0,0;
-1,0,0,0,0,0,0,0;
0,0,0,0,-1,0,0,0;
0,0,0,0,-1,0,-1,0;
-1,0,1,1,0,0,0,1;
1,0,0,0,0,0,0,-1;
0,0,0,1,0,0,0,0;
0,0,0,0,-1,1,0,0]
def surface_genus_four_S : Matrix (Fin 8) (Fin 8) ℤ := !![1,0,0,0,0,0,0,0;
0,0,0,1,1,1,0,0;
0,1,1,0,0,0,0,1;
0,0,-1,0,0,0,0,0;
0,0,0,0,0,-1,0,0;
0,0,0,1,0,0,0,0;
0,0,0,0,0,0,1,0;
0,0,0,0,0,0,0,-1]
def surface_genus_four_I : Matrix (Fin 8) (Fin 8) ℤ := !![1,0,0,0,0,0,0,0;
0,0,1,1,0,0,0,1;
0,0,0,-1,0,0,0,0;
0,0,0,0,0,1,0,0;
0,1,0,0,1,-1,0,0;
0,0,0,0,-1,0,0,0;
0,0,0,0,0,0,1,0;
0,0,0,0,0,0,0,-1]
def surface_genus_four_J : Matrix (Fin 8) (Fin 8) ℤ := !![0,0,0,0,1,0,0,0;
0,0,0,0,0,1,0,0;
0,0,0,0,0,0,1,0;
0,0,0,0,0,0,0,1;
-1,0,0,0,0,0,0,0;
0,-1,0,0,0,0,0,0;
0,0,-1,0,0,0,0,0;
0,0,0,-1,0,0,0,0]
theorem surface_genus_four_checked : surface_genus_four_S*surface_genus_four_I=1 ∧ surface_genus_four_I*surface_genus_four_S=1 ∧ surface_genus_four_S.transpose*surface_genus_four_O*surface_genus_four_S=surface_genus_four_J ∧ surface_genus_four_O.transpose = -surface_genus_four_O := by decide +kernel
def surface_genus_three_O : Matrix (Fin 6) (Fin 6) ℤ := !![0,0,1,0,-1,-1;
0,0,1,-1,0,0;
-1,-1,0,0,1,0;
0,1,0,0,0,0;
1,0,-1,0,0,0;
1,0,0,0,0,0]
def surface_genus_three_S : Matrix (Fin 6) (Fin 6) ℤ := !![1,1,1,0,0,0;
0,-1,0,0,0,0;
0,0,1,1,0,-1;
0,0,1,0,1,-1;
0,0,1,0,0,0;
0,0,0,0,0,-1]
def surface_genus_three_I : Matrix (Fin 6) (Fin 6) ℤ := !![1,1,0,0,-1,0;
0,-1,0,0,0,0;
0,0,0,0,1,0;
0,0,1,0,-1,-1;
0,0,0,1,-1,-1;
0,0,0,0,0,-1]
def surface_genus_three_J : Matrix (Fin 6) (Fin 6) ℤ := !![0,0,0,1,0,0;
0,0,0,0,1,0;
0,0,0,0,0,1;
-1,0,0,0,0,0;
0,-1,0,0,0,0;
0,0,-1,0,0,0]
theorem surface_genus_three_checked : surface_genus_three_S*surface_genus_three_I=1 ∧ surface_genus_three_I*surface_genus_three_S=1 ∧ surface_genus_three_S.transpose*surface_genus_three_O*surface_genus_three_S=surface_genus_three_J ∧ surface_genus_three_O.transpose = -surface_genus_three_O := by decide +kernel
def surface_mixed_roots_genus_two_O : Matrix (Fin 4) (Fin 4) ℤ := !![0,1,1,1;
-1,0,-1,0;
-1,1,0,0;
-1,0,0,0]
def surface_mixed_roots_genus_two_S : Matrix (Fin 4) (Fin 4) ℤ := !![1,-1,0,0;
0,-1,1,1;
0,1,0,0;
0,0,0,-1]
def surface_mixed_roots_genus_two_I : Matrix (Fin 4) (Fin 4) ℤ := !![1,0,1,0;
0,0,1,0;
0,1,1,1;
0,0,0,-1]
def surface_mixed_roots_genus_two_J : Matrix (Fin 4) (Fin 4) ℤ := !![0,0,1,0;
0,0,0,1;
-1,0,0,0;
0,-1,0,0]
theorem surface_mixed_roots_genus_two_checked : surface_mixed_roots_genus_two_S*surface_mixed_roots_genus_two_I=1 ∧ surface_mixed_roots_genus_two_I*surface_mixed_roots_genus_two_S=1 ∧ surface_mixed_roots_genus_two_S.transpose*surface_mixed_roots_genus_two_O*surface_mixed_roots_genus_two_S=surface_mixed_roots_genus_two_J ∧ surface_mixed_roots_genus_two_O.transpose = -surface_mixed_roots_genus_two_O := by decide +kernel
def surface_original_genus_two_O : Matrix (Fin 4) (Fin 4) ℤ := !![0,-1,1,0;
1,0,-1,0;
-1,1,0,-1;
0,0,1,0]
def surface_original_genus_two_S : Matrix (Fin 4) (Fin 4) ℤ := !![1,1,0,0;
0,1,-1,0;
0,1,0,0;
0,0,0,-1]
def surface_original_genus_two_I : Matrix (Fin 4) (Fin 4) ℤ := !![1,0,-1,0;
0,0,1,0;
0,-1,1,0;
0,0,0,-1]
def surface_original_genus_two_J : Matrix (Fin 4) (Fin 4) ℤ := !![0,0,1,0;
0,0,0,1;
-1,0,0,0;
0,-1,0,0]
theorem surface_original_genus_two_checked : surface_original_genus_two_S*surface_original_genus_two_I=1 ∧ surface_original_genus_two_I*surface_original_genus_two_S=1 ∧ surface_original_genus_two_S.transpose*surface_original_genus_two_O*surface_original_genus_two_S=surface_original_genus_two_J ∧ surface_original_genus_two_O.transpose = -surface_original_genus_two_O := by decide +kernel
def surface_real_genus_two_O : Matrix (Fin 4) (Fin 4) ℤ := !![0,-1,0,0;
1,0,-1,1;
0,1,0,-1;
0,-1,1,0]
def surface_real_genus_two_S : Matrix (Fin 4) (Fin 4) ℤ := !![1,1,0,1;
0,0,-1,0;
0,1,0,0;
0,0,0,-1]
def surface_real_genus_two_I : Matrix (Fin 4) (Fin 4) ℤ := !![1,0,-1,1;
0,0,1,0;
0,-1,0,0;
0,0,0,-1]
def surface_real_genus_two_J : Matrix (Fin 4) (Fin 4) ℤ := !![0,0,1,0;
0,0,0,1;
-1,0,0,0;
0,-1,0,0]
theorem surface_real_genus_two_checked : surface_real_genus_two_S*surface_real_genus_two_I=1 ∧ surface_real_genus_two_I*surface_real_genus_two_S=1 ∧ surface_real_genus_two_S.transpose*surface_real_genus_two_O*surface_real_genus_two_S=surface_real_genus_two_J ∧ surface_real_genus_two_O.transpose = -surface_real_genus_two_O := by decide +kernel
def surface_square_torus_O : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;
-1,0]
def surface_square_torus_S : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;
0,1]
def surface_square_torus_I : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;
0,1]
def surface_square_torus_J : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;
-1,0]
theorem surface_square_torus_checked : surface_square_torus_S*surface_square_torus_I=1 ∧ surface_square_torus_I*surface_square_torus_S=1 ∧ surface_square_torus_S.transpose*surface_square_torus_O*surface_square_torus_S=surface_square_torus_J ∧ surface_square_torus_O.transpose = -surface_square_torus_O := by decide +kernel
end PerfectPower.ParallelCertificates
