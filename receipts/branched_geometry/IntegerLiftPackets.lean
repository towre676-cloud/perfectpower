import PerfectPower.IntegerLiftRecovery
namespace PerfectPower.Generated.IntegerLiftPackets
open Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def case_0_A : Matrix (Fin 1) (Fin 2) ℤ := ![![2,3]]
def case_0_U : Matrix (Fin 1) (Fin 1) ℤ := ![![1]]
def case_0_Ui : Matrix (Fin 1) (Fin 1) ℤ := ![![1]]
def case_0_V : Matrix (Fin 2) (Fin 2) ℤ := ![![-1,3],![1,-2]]
def case_0_Vi : Matrix (Fin 2) (Fin 2) ℤ := ![![2,3],![1,1]]
def case_0_D : Matrix (Fin 1) (Fin 2) ℤ := ![![1,0]]
theorem case_0_all (x : Fin 2 → ℤ) (b : Fin 1 → ℤ) :
    case_0_A *ᵥ x=b ↔ case_0_D *ᵥ (case_0_Vi *ᵥ x)=case_0_U *ᵥ b := by
  exact PerfectPower.IntegerLiftRecovery.transformed_fibre case_0_A case_0_U case_0_Ui case_0_V case_0_Vi case_0_D
    (by decide +kernel) (by decide +kernel) (by decide +kernel) x b
#print axioms case_0_all
def case_1_A : Matrix (Fin 1) (Fin 2) ℤ := ![![4,6]]
def case_1_U : Matrix (Fin 1) (Fin 1) ℤ := ![![1]]
def case_1_Ui : Matrix (Fin 1) (Fin 1) ℤ := ![![1]]
def case_1_V : Matrix (Fin 2) (Fin 2) ℤ := ![![-1,3],![1,-2]]
def case_1_Vi : Matrix (Fin 2) (Fin 2) ℤ := ![![2,3],![1,1]]
def case_1_D : Matrix (Fin 1) (Fin 2) ℤ := ![![2,0]]
theorem case_1_all (x : Fin 2 → ℤ) (b : Fin 1 → ℤ) :
    case_1_A *ᵥ x=b ↔ case_1_D *ᵥ (case_1_Vi *ᵥ x)=case_1_U *ᵥ b := by
  exact PerfectPower.IntegerLiftRecovery.transformed_fibre case_1_A case_1_U case_1_Ui case_1_V case_1_Vi case_1_D
    (by decide +kernel) (by decide +kernel) (by decide +kernel) x b
#print axioms case_1_all
def case_2_A : Matrix (Fin 2) (Fin 3) ℤ := ![![2,0,1],![0,3,1]]
def case_2_U : Matrix (Fin 2) (Fin 2) ℤ := ![![1,0],![1,-1]]
def case_2_Ui : Matrix (Fin 2) (Fin 2) ℤ := ![![1,0],![1,-1]]
def case_2_V : Matrix (Fin 3) (Fin 3) ℤ := ![![0,2,-3],![0,1,-2],![1,-4,6]]
def case_2_Vi : Matrix (Fin 3) (Fin 3) ℤ := ![![2,0,1],![2,-3,0],![1,-2,0]]
def case_2_D : Matrix (Fin 2) (Fin 3) ℤ := ![![1,0,0],![0,1,0]]
theorem case_2_all (x : Fin 3 → ℤ) (b : Fin 2 → ℤ) :
    case_2_A *ᵥ x=b ↔ case_2_D *ᵥ (case_2_Vi *ᵥ x)=case_2_U *ᵥ b := by
  exact PerfectPower.IntegerLiftRecovery.transformed_fibre case_2_A case_2_U case_2_Ui case_2_V case_2_Vi case_2_D
    (by decide +kernel) (by decide +kernel) (by decide +kernel) x b
#print axioms case_2_all
def case_3_A : Matrix (Fin 2) (Fin 2) ℤ := ![![2,4],![6,12]]
def case_3_U : Matrix (Fin 2) (Fin 2) ℤ := ![![1,0],![-3,1]]
def case_3_Ui : Matrix (Fin 2) (Fin 2) ℤ := ![![1,0],![3,1]]
def case_3_V : Matrix (Fin 2) (Fin 2) ℤ := ![![1,-2],![0,1]]
def case_3_Vi : Matrix (Fin 2) (Fin 2) ℤ := ![![1,2],![0,1]]
def case_3_D : Matrix (Fin 2) (Fin 2) ℤ := ![![2,0],![0,0]]
theorem case_3_all (x : Fin 2 → ℤ) (b : Fin 2 → ℤ) :
    case_3_A *ᵥ x=b ↔ case_3_D *ᵥ (case_3_Vi *ᵥ x)=case_3_U *ᵥ b := by
  exact PerfectPower.IntegerLiftRecovery.transformed_fibre case_3_A case_3_U case_3_Ui case_3_V case_3_Vi case_3_D
    (by decide +kernel) (by decide +kernel) (by decide +kernel) x b
#print axioms case_3_all
def case_4_A : Matrix (Fin 2) (Fin 2) ℤ := ![![2,0],![0,3]]
def case_4_U : Matrix (Fin 2) (Fin 2) ℤ := ![![1,1],![3,2]]
def case_4_Ui : Matrix (Fin 2) (Fin 2) ℤ := ![![-2,1],![3,-1]]
def case_4_V : Matrix (Fin 2) (Fin 2) ℤ := ![![-1,3],![1,-2]]
def case_4_Vi : Matrix (Fin 2) (Fin 2) ℤ := ![![2,3],![1,1]]
def case_4_D : Matrix (Fin 2) (Fin 2) ℤ := ![![1,0],![0,6]]
theorem case_4_all (x : Fin 2 → ℤ) (b : Fin 2 → ℤ) :
    case_4_A *ᵥ x=b ↔ case_4_D *ᵥ (case_4_Vi *ᵥ x)=case_4_U *ᵥ b := by
  exact PerfectPower.IntegerLiftRecovery.transformed_fibre case_4_A case_4_U case_4_Ui case_4_V case_4_Vi case_4_D
    (by decide +kernel) (by decide +kernel) (by decide +kernel) x b
#print axioms case_4_all
end PerfectPower.Generated.IntegerLiftPackets
