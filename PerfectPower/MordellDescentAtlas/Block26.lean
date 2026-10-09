import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p3495 (x y : ℤ) : y^2 ≠ x^3+(3495) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3509 (x y : ℤ) : y^2 ≠ x^3+(3509) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 45) (b := 296) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3578 (x y : ℤ) : y^2 ≠ x^3+(3578) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 6) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3586 (x y : ℤ) : y^2 ≠ x^3+(3586) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -28) (b := 113) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 113) (u := 51) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3642 (x y : ℤ) : y^2 ≠ x^3+(3642) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -26) (b := 103) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 103) (u := 38) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3650 (x y : ℤ) : y^2 ≠ x^3+(3650) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 31) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3654 (x y : ℤ) : y^2 ≠ x^3+(3654) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 33) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 33) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3757 (x y : ℤ) : y^2 ≠ x^3+(3757) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 17) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3796 (x y : ℤ) : y^2 ≠ x^3+(3796) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 38) (b := 226) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 113) (u := 15) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p3798 (x y : ℤ) : y^2 ≠ x^3+(3798) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 26) (b := 83) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 83) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3802 (x y : ℤ) : y^2 ≠ x^3+(3802) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -10) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3863 (x y : ℤ) : y^2 ≠ x^3+(3863) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 42) (b := 265) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 265) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3924 (x y : ℤ) : y^2 ≠ x^3+(3924) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p4016 (x y : ℤ) : y^2 ≠ x^3+(4016) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -6) (b := 46) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p4128 (x y : ℤ) : y^2 ≠ x^3+(4128) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 44) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p4150 (x y : ℤ) : y^2 ≠ x^3+(4150) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 42) (b := 187) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 187) (u := 41) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4151 (x y : ℤ) : y^2 ≠ x^3+(4151) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4155 (x y : ℤ) : y^2 ≠ x^3+(4155) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4191 (x y : ℤ) : y^2 ≠ x^3+(4191) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 31) (b := 160) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4237 (x y : ℤ) : y^2 ≠ x^3+(4237) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 17) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4250 (x y : ℤ) : y^2 ≠ x^3+(4250) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -18) (b := 71) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 71) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4253 (x y : ℤ) : y^2 ≠ x^3+(4253) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 33) (b := 178) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4302 (x y : ℤ) : y^2 ≠ x^3+(4302) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 43) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 43) (u := 16) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4311 (x y : ℤ) : y^2 ≠ x^3+(4311) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 46) (b := 305) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 305) (u := 72) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4354 (x y : ℤ) : y^2 ≠ x^3+(4354) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 47) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 47) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4359 (x y : ℤ) : y^2 ≠ x^3+(4359) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4374 (x y : ℤ) : y^2 ≠ x^3+(4374) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 27) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4382 (x y : ℤ) : y^2 ≠ x^3+(4382) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 44) (b := 201) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 201) (u := 20) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4389 (x y : ℤ) : y^2 ≠ x^3+(4389) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 25) (b := 106) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4410 (x y : ℤ) : y^2 ≠ x^3+(4410) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -2) (b := 47) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 47) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4431 (x y : ℤ) : y^2 ≠ x^3+(4431) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 43) (b := 274) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 137) (u := 37) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4454 (x y : ℤ) : y^2 ≠ x^3+(4454) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 26) (b := 81) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 81) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3495
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3509
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3578
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3586
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3642
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3650
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3654
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3757
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3796
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3798
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3802
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3863
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3924
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4016
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4128
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4150
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4151
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4155
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4191
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4237
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4250
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4253
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4302
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4311
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4354
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4359
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4374
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4382
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4389
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4410
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4431
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4454
