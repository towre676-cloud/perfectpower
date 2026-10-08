import PerfectPower.WeilSpectral
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace PerfectPower.WeilSpectralExample4
noncomputable section
open Matrix Polynomial
open scoped BigOperators
abbrev M := Matrix (Fin 4) (Fin 4) ℚ
def phi : Polynomial ℚ := C (1) * X^0 + C (1) * X^2
def fourier : Matrix (Fin 4) (Fin 4) (Polynomial ℚ) := !![C (1) * X^0, C (1) * X^0, C (1) * X^0, C (1) * X^0;
  C (1) * X^0, C (1) * X^1, C (1) * X^2, C (1) * X^3;
  C (1) * X^0, C (1) * X^2, C (1) * X^0, C (1) * X^2;
  C (1) * X^0, C (1) * X^3, C (1) * X^2, C (1) * X^1]
def chirp : Matrix (Fin 4) (Fin 4) (Polynomial ℚ) := !![C (1) * X^0, 0, 0, 0;
  0, C (1) * X^1, 0, 0;
  0, 0, C (1) * X^0, 0;
  0, 0, 0, C (1) * X^1]
def P0 : M := !![(1 / 2), 0, (1 / 2), 0;
  0, 0, 0, 0;
  (1 / 2), 0, (1 / 2), 0;
  0, 0, 0, 0]
def Q0 : Matrix (Fin 4) (Fin 4) (Polynomial ℚ) := !![0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0;
  C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0, 0;
  0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0;
  C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0, 0]
theorem fourier_factor_0 : (P0.map C)*fourier-fourier*(P0.map C)=phi • Q0 := by
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P0,fourier,phi,Q0,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem chirp_commutes_0 : Commute (P0.map C) chirp := by
  change (P0.map C)*chirp=chirp*(P0.map C)
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P0,chirp,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem source_fourier_commutes_0 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) (hf : f phi=0) :
    Commute ((P0.map C).map f) (fourier.map f) :=
  PerfectPower.WeilSpectral.polynomial_commute_of_factor phi fourier_factor_0 f hf
theorem source_chirp_commutes_0 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) :
    Commute ((P0.map C).map f) (chirp.map f) := by
  have h := congrArg (fun A => A.map f) chirp_commutes_0.eq
  simpa only [Matrix.map_mul] using h
def P1 : M := !![0, 0, 0, 0;
  0, (1 / 2), 0, (-1 / 2);
  0, 0, 0, 0;
  0, (-1 / 2), 0, (1 / 2)]
def Q1 : Matrix (Fin 4) (Fin 4) (Polynomial ℚ) := !![0, 0, 0, 0;
  0, 0, 0, 0;
  0, 0, 0, 0;
  0, 0, 0, 0]
theorem fourier_factor_1 : (P1.map C)*fourier-fourier*(P1.map C)=phi • Q1 := by
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P1,fourier,phi,Q1,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem chirp_commutes_1 : Commute (P1.map C) chirp := by
  change (P1.map C)*chirp=chirp*(P1.map C)
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P1,chirp,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem source_fourier_commutes_1 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) (hf : f phi=0) :
    Commute ((P1.map C).map f) (fourier.map f) :=
  PerfectPower.WeilSpectral.polynomial_commute_of_factor phi fourier_factor_1 f hf
theorem source_chirp_commutes_1 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) :
    Commute ((P1.map C).map f) (chirp.map f) := by
  have h := congrArg (fun A => A.map f) chirp_commutes_1.eq
  simpa only [Matrix.map_mul] using h
def P2 : M := !![(1 / 2), 0, (-1 / 2), 0;
  0, (1 / 2), 0, (1 / 2);
  (-1 / 2), 0, (1 / 2), 0;
  0, (1 / 2), 0, (1 / 2)]
def Q2 : Matrix (Fin 4) (Fin 4) (Polynomial ℚ) := !![0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0;
  C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0, 0;
  0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0;
  C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0, 0]
theorem fourier_factor_2 : (P2.map C)*fourier-fourier*(P2.map C)=phi • Q2 := by
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P2,fourier,phi,Q2,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem chirp_commutes_2 : Commute (P2.map C) chirp := by
  change (P2.map C)*chirp=chirp*(P2.map C)
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P2,chirp,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem source_fourier_commutes_2 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) (hf : f phi=0) :
    Commute ((P2.map C).map f) (fourier.map f) :=
  PerfectPower.WeilSpectral.polynomial_commute_of_factor phi fourier_factor_2 f hf
theorem source_chirp_commutes_2 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) :
    Commute ((P2.map C).map f) (chirp.map f) := by
  have h := congrArg (fun A => A.map f) chirp_commutes_2.eq
  simpa only [Matrix.map_mul] using h
def projectors : Fin 3 → M := ![P0, P1, P2]
def ranks : Fin 3 → ℚ := ![1, 1, 2]
theorem orthogonal_entries : ∀ i j : Fin 3, ∀ x y : Fin 4, (projectors i * projectors j) x y = if i=j then projectors i x y else 0 := by
  decide +kernel
theorem symmetric_entries : ∀ i : Fin 3, ∀ x y : Fin 4, projectors i x y = projectors i y x := by
  decide +kernel
theorem partition_entries : ∀ x y : Fin 4, (∑ i,projectors i) x y = if x=y then 1 else 0 := by
  decide +kernel
theorem trace_ranks : ∀ i : Fin 3, Matrix.trace (projectors i)=ranks i := by
  decide +kernel
theorem orthogonal_partition (i j : Fin 3) : projectors i * projectors j = if i=j then projectors i else 0 := by
  ext x y; by_cases h : i=j <;> simpa [h] using orthogonal_entries i j x y
theorem partition : (∑ i,projectors i) = 1 := by
  ext x y; simpa only [Matrix.one_apply] using partition_entries x y
end
end PerfectPower.WeilSpectralExample4
