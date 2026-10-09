import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m6513 (x y : ℤ) : y^2 ≠ x^3+(-6513) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -17) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6508 (x y : ℤ) : y^2 ≠ x^3+(-6508) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m6490 (x y : ℤ) : y^2 ≠ x^3+(-6490) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 2) (b := 57) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 57) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6482 (x y : ℤ) : y^2 ≠ x^3+(-6482) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 36) (b := 163) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 163) (u := 18) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6480 (x y : ℤ) : y^2 ≠ x^3+(-6480) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -18) (b := 18) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m6476 (x y : ℤ) : y^2 ≠ x^3+(-6476) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m6465 (x y : ℤ) : y^2 ≠ x^3+(-6465) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 61) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6457 (x y : ℤ) : y^2 ≠ x^3+(-6457) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 25) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6442 (x y : ℤ) : y^2 ≠ x^3+(-6442) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -14) (b := 43) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 43) (u := 16) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6434 (x y : ℤ) : y^2 ≠ x^3+(-6434) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 4) (b := 57) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 57) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6432 (x y : ℤ) : y^2 ≠ x^3+(-6432) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 28) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m6427 (x y : ℤ) : y^2 ≠ x^3+(-6427) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -3) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6416 (x y : ℤ) : y^2 ≠ x^3+(-6416) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -22) (b := 46) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m6401 (x y : ℤ) : y^2 ≠ x^3+(-6401) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6381 (x y : ℤ) : y^2 ≠ x^3+(-6381) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6373 (x y : ℤ) : y^2 ≠ x^3+(-6373) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6329 (x y : ℤ) : y^2 ≠ x^3+(-6329) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6323 (x y : ℤ) : y^2 ≠ x^3+(-6323) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 17) (b := 106) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6293 (x y : ℤ) : y^2 ≠ x^3+(-6293) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 64) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 6 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6275 (x y : ℤ) : y^2 ≠ x^3+(-6275) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 5) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6252 (x y : ℤ) : y^2 ≠ x^3+(-6252) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 130) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m6225 (x y : ℤ) : y^2 ≠ x^3+(-6225) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6217 (x y : ℤ) : y^2 ≠ x^3+(-6217) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 39) (b := 256) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 8 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6205 (x y : ℤ) : y^2 ≠ x^3+(-6205) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6155 (x y : ℤ) : y^2 ≠ x^3+(-6155) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 41) (b := 274) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 137) (u := 37) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6121 (x y : ℤ) : y^2 ≠ x^3+(-6121) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6110 (x y : ℤ) : y^2 ≠ x^3+(-6110) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -28) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 25) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6106 (x y : ℤ) : y^2 ≠ x^3+(-6106) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -14) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6078 (x y : ℤ) : y^2 ≠ x^3+(-6078) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 31) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6069 (x y : ℤ) : y^2 ≠ x^3+(-6069) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -17) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6057 (x y : ℤ) : y^2 ≠ x^3+(-6057) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6049 (x y : ℤ) : y^2 ≠ x^3+(-6049) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 109) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 109) (u := 33) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6513
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6508
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6490
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6482
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6480
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6476
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6465
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6457
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6442
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6434
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6432
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6427
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6416
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6401
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6381
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6373
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6329
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6323
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6293
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6275
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6252
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6225
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6217
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6205
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6155
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6121
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6110
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6106
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6078
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6069
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6057
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6049
