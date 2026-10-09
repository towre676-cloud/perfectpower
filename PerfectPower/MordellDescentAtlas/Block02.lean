import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m8352 (x y : ℤ) : y^2 ≠ x^3+(-8352) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -44) (b := 196) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m8336 (x y : ℤ) : y^2 ≠ x^3+(-8336) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -22) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m8332 (x y : ℤ) : y^2 ≠ x^3+(-8332) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m8306 (x y : ℤ) : y^2 ≠ x^3+(-8306) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 28) (b := 123) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 123) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8289 (x y : ℤ) : y^2 ≠ x^3+(-8289) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 46) (b := 325) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 325) (u := 18) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8288 (x y : ℤ) : y^2 ≠ x^3+(-8288) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -20) (b := 12) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m8281 (x y : ℤ) : y^2 ≠ x^3+(-8281) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 39) (b := 260) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8277 (x y : ℤ) : y^2 ≠ x^3+(-8277) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -17) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8242 (x y : ℤ) : y^2 ≠ x^3+(-8242) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -20) (b := 11) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8226 (x y : ℤ) : y^2 ≠ x^3+(-8226) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 57) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 57) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8225 (x y : ℤ) : y^2 ≠ x^3+(-8225) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8201 (x y : ℤ) : y^2 ≠ x^3+(-8201) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 35) (b := 226) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 113) (u := 15) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8162 (x y : ℤ) : y^2 ≠ x^3+(-8162) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -20) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8144 (x y : ℤ) : y^2 ≠ x^3+(-8144) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -18) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m8137 (x y : ℤ) : y^2 ≠ x^3+(-8137) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8121 (x y : ℤ) : y^2 ≠ x^3+(-8121) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 137) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 137) (u := 37) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8109 (x y : ℤ) : y^2 ≠ x^3+(-8109) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 43) (b := 296) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8073 (x y : ℤ) : y^2 ≠ x^3+(-8073) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8032 (x y : ℤ) : y^2 ≠ x^3+(-8032) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -20) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m8025 (x y : ℤ) : y^2 ≠ x^3+(-8025) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 122) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8018 (x y : ℤ) : y^2 ≠ x^3+(-8018) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -20) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m8002 (x y : ℤ) : y^2 ≠ x^3+(-8002) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -20) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7998 (x y : ℤ) : y^2 ≠ x^3+(-7998) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7978 (x y : ℤ) : y^2 ≠ x^3+(-7978) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 67) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 67) (u := 20) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7968 (x y : ℤ) : y^2 ≠ x^3+(-7968) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m7962 (x y : ℤ) : y^2 ≠ x^3+(-7962) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 26) (b := 113) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 113) (u := 26) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7946 (x y : ℤ) : y^2 ≠ x^3+(-7946) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -14) (b := 51) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 51) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7929 (x y : ℤ) : y^2 ≠ x^3+(-7929) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7913 (x y : ℤ) : y^2 ≠ x^3+(-7913) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 2) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7902 (x y : ℤ) : y^2 ≠ x^3+(-7902) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 7) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7883 (x y : ℤ) : y^2 ≠ x^3+(-7883) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -19) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7861 (x y : ℤ) : y^2 ≠ x^3+(-7861) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 106) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8352
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8336
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8332
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8306
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8289
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8288
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8281
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8277
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8242
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8226
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8225
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8201
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8162
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8144
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8137
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8121
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8109
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8073
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8032
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8025
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8018
#print axioms PerfectPower.MordellDescentAtlas.no_points_m8002
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7998
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7978
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7968
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7962
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7946
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7929
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7913
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7902
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7883
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7861
