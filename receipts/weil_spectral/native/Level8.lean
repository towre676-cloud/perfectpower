import PerfectPower.WeilSpectral
set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace PerfectPower.WeilSpectralExample8
noncomputable section
open Matrix Polynomial
open scoped BigOperators
abbrev M := Matrix (Fin 8) (Fin 8) ℚ
def phi : Polynomial ℚ := C (1) * X^0 + C (1) * X^4
def fourier : Matrix (Fin 8) (Fin 8) (Polynomial ℚ) := !![C (1) * X^0, C (1) * X^0, C (1) * X^0, C (1) * X^0, C (1) * X^0, C (1) * X^0, C (1) * X^0, C (1) * X^0;
  C (1) * X^0, C (1) * X^1, C (1) * X^2, C (1) * X^3, C (1) * X^4, C (1) * X^5, C (1) * X^6, C (1) * X^7;
  C (1) * X^0, C (1) * X^2, C (1) * X^4, C (1) * X^6, C (1) * X^0, C (1) * X^2, C (1) * X^4, C (1) * X^6;
  C (1) * X^0, C (1) * X^3, C (1) * X^6, C (1) * X^1, C (1) * X^4, C (1) * X^7, C (1) * X^2, C (1) * X^5;
  C (1) * X^0, C (1) * X^4, C (1) * X^0, C (1) * X^4, C (1) * X^0, C (1) * X^4, C (1) * X^0, C (1) * X^4;
  C (1) * X^0, C (1) * X^5, C (1) * X^2, C (1) * X^7, C (1) * X^4, C (1) * X^1, C (1) * X^6, C (1) * X^3;
  C (1) * X^0, C (1) * X^6, C (1) * X^4, C (1) * X^2, C (1) * X^0, C (1) * X^6, C (1) * X^4, C (1) * X^2;
  C (1) * X^0, C (1) * X^7, C (1) * X^6, C (1) * X^5, C (1) * X^4, C (1) * X^3, C (1) * X^2, C (1) * X^1]
def chirp : Matrix (Fin 8) (Fin 8) (Polynomial ℚ) := !![C (1) * X^0, 0, 0, 0, 0, 0, 0, 0;
  0, C (1) * X^1, 0, 0, 0, 0, 0, 0;
  0, 0, C (1) * X^4, 0, 0, 0, 0, 0;
  0, 0, 0, C (1) * X^1, 0, 0, 0, 0;
  0, 0, 0, 0, C (1) * X^0, 0, 0, 0;
  0, 0, 0, 0, 0, C (1) * X^1, 0, 0;
  0, 0, 0, 0, 0, 0, C (1) * X^4, 0;
  0, 0, 0, 0, 0, 0, 0, C (1) * X^1]
def P0 : M := !![(1 / 2), 0, 0, 0, (1 / 2), 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, (1 / 2), 0, 0, 0, (1 / 2), 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  (1 / 2), 0, 0, 0, (1 / 2), 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, (1 / 2), 0, 0, 0, (1 / 2), 0;
  0, 0, 0, 0, 0, 0, 0, 0]
def Q0 : Matrix (Fin 8) (Fin 8) (Polynomial ℚ) := !![0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0;
  C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^2, 0;
  0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^2;
  C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^2, 0;
  0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^0;
  C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^2, 0;
  0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^2;
  C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^2, 0]
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
def P1 : M := !![0, 0, 0, 0, 0, 0, 0, 0;
  0, (1 / 4), 0, (-1 / 4), 0, (-1 / 4), 0, (1 / 4);
  0, 0, 0, 0, 0, 0, 0, 0;
  0, (-1 / 4), 0, (1 / 4), 0, (1 / 4), 0, (-1 / 4);
  0, 0, 0, 0, 0, 0, 0, 0;
  0, (-1 / 4), 0, (1 / 4), 0, (1 / 4), 0, (-1 / 4);
  0, 0, 0, 0, 0, 0, 0, 0;
  0, (1 / 4), 0, (-1 / 4), 0, (-1 / 4), 0, (1 / 4)]
def Q1 : Matrix (Fin 8) (Fin 8) (Polynomial ℚ) := !![0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0]
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
def P2 : M := !![0, 0, 0, 0, 0, 0, 0, 0;
  0, (1 / 4), 0, (1 / 4), 0, (-1 / 4), 0, (-1 / 4);
  0, 0, 0, 0, 0, 0, 0, 0;
  0, (1 / 4), 0, (1 / 4), 0, (-1 / 4), 0, (-1 / 4);
  0, 0, 0, 0, 0, 0, 0, 0;
  0, (-1 / 4), 0, (-1 / 4), 0, (1 / 4), 0, (1 / 4);
  0, 0, 0, 0, 0, 0, 0, 0;
  0, (-1 / 4), 0, (-1 / 4), 0, (1 / 4), 0, (1 / 4)]
def Q2 : Matrix (Fin 8) (Fin 8) (Polynomial ℚ) := !![0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0]
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
def P3 : M := !![(1 / 2), 0, 0, 0, (-1 / 2), 0, 0, 0;
  0, (1 / 4), 0, (1 / 4), 0, (1 / 4), 0, (1 / 4);
  0, 0, 0, 0, 0, 0, 0, 0;
  0, (1 / 4), 0, (1 / 4), 0, (1 / 4), 0, (1 / 4);
  (-1 / 2), 0, 0, 0, (1 / 2), 0, 0, 0;
  0, (1 / 4), 0, (1 / 4), 0, (1 / 4), 0, (1 / 4);
  0, 0, 0, 0, 0, 0, 0, 0;
  0, (1 / 4), 0, (1 / 4), 0, (1 / 4), 0, (1 / 4)]
def Q3 : Matrix (Fin 8) (Fin 8) (Polynomial ℚ) := !![0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0;
  C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^2, 0;
  0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^2;
  C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^2, 0;
  0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0, 0, C ((-1 / 2)) * X^0;
  C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^2, 0;
  0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^2, 0, C ((-1 / 2)) * X^2;
  C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^2, 0, C ((1 / 2)) * X^0, 0, C ((1 / 2)) * X^2, 0]
theorem fourier_factor_3 : (P3.map C)*fourier-fourier*(P3.map C)=phi • Q3 := by
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P3,fourier,phi,Q3,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem chirp_commutes_3 : Commute (P3.map C) chirp := by
  change (P3.map C)*chirp=chirp*(P3.map C)
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P3,chirp,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem source_fourier_commutes_3 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) (hf : f phi=0) :
    Commute ((P3.map C).map f) (fourier.map f) :=
  PerfectPower.WeilSpectral.polynomial_commute_of_factor phi fourier_factor_3 f hf
theorem source_chirp_commutes_3 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) :
    Commute ((P3.map C).map f) (chirp.map f) := by
  have h := congrArg (fun A => A.map f) chirp_commutes_3.eq
  simpa only [Matrix.map_mul] using h
def P4 : M := !![0, 0, 0, 0, 0, 0, 0, 0;
  0, (1 / 4), 0, (-1 / 4), 0, (1 / 4), 0, (-1 / 4);
  0, 0, (1 / 2), 0, 0, 0, (-1 / 2), 0;
  0, (-1 / 4), 0, (1 / 4), 0, (-1 / 4), 0, (1 / 4);
  0, 0, 0, 0, 0, 0, 0, 0;
  0, (1 / 4), 0, (-1 / 4), 0, (1 / 4), 0, (-1 / 4);
  0, 0, (-1 / 2), 0, 0, 0, (1 / 2), 0;
  0, (-1 / 4), 0, (1 / 4), 0, (-1 / 4), 0, (1 / 4)]
def Q4 : Matrix (Fin 8) (Fin 8) (Polynomial ℚ) := !![0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0, 0]
theorem fourier_factor_4 : (P4.map C)*fourier-fourier*(P4.map C)=phi • Q4 := by
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P4,fourier,phi,Q4,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem chirp_commutes_4 : Commute (P4.map C) chirp := by
  change (P4.map C)*chirp=chirp*(P4.map C)
  ext x y : 2; simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,Matrix.map_apply]; fin_cases x <;> fin_cases y <;>
    norm_num [P4,chirp,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.map_apply] <;> ring <;> simp [Polynomial.coeff_C,Polynomial.coeff_one] <;> split_ifs <;> norm_num
theorem source_fourier_commutes_4 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) (hf : f phi=0) :
    Commute ((P4.map C).map f) (fourier.map f) :=
  PerfectPower.WeilSpectral.polynomial_commute_of_factor phi fourier_factor_4 f hf
theorem source_chirp_commutes_4 {K : Type*} [Field K] (f : Polynomial ℚ →+* K) :
    Commute ((P4.map C).map f) (chirp.map f) := by
  have h := congrArg (fun A => A.map f) chirp_commutes_4.eq
  simpa only [Matrix.map_mul] using h
def projectors : Fin 5 → M := ![P0, P1, P2, P3, P4]
def ranks : Fin 5 → ℚ := ![2, 1, 1, 2, 2]
theorem orthogonal_entries : ∀ i j : Fin 5, ∀ x y : Fin 8, (projectors i * projectors j) x y = if i=j then projectors i x y else 0 := by
  decide +kernel
theorem symmetric_entries : ∀ i : Fin 5, ∀ x y : Fin 8, projectors i x y = projectors i y x := by
  decide +kernel
theorem partition_entries : ∀ x y : Fin 8, (∑ i,projectors i) x y = if x=y then 1 else 0 := by
  decide +kernel
theorem trace_ranks : ∀ i : Fin 5, Matrix.trace (projectors i)=ranks i := by
  decide +kernel
theorem orthogonal_partition (i j : Fin 5) : projectors i * projectors j = if i=j then projectors i else 0 := by
  ext x y; by_cases h : i=j <;> simpa [h] using orthogonal_entries i j x y
theorem partition : (∑ i,projectors i) = 1 := by
  ext x y; simpa only [Matrix.one_apply] using partition_entries x y
end
end PerfectPower.WeilSpectralExample8
