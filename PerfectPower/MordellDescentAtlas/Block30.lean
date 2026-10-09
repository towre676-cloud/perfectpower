import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p7661 (x y : ℤ) : y^2 ≠ x^3+(7661) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7712 (x y : ℤ) : y^2 ≠ x^3+(7712) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 12) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p7758 (x y : ℤ) : y^2 ≠ x^3+(7758) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 11) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7838 (x y : ℤ) : y^2 ≠ x^3+(7838) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7839 (x y : ℤ) : y^2 ≠ x^3+(7839) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 53) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7842 (x y : ℤ) : y^2 ≠ x^3+(7842) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 25) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7887 (x y : ℤ) : y^2 ≠ x^3+(7887) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 31) (b := 148) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7962 (x y : ℤ) : y^2 ≠ x^3+(7962) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -26) (b := 113) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 113) (u := 51) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7968 (x y : ℤ) : y^2 ≠ x^3+(7968) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p7982 (x y : ℤ) : y^2 ≠ x^3+(7982) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7998 (x y : ℤ) : y^2 ≠ x^3+(7998) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8002 (x y : ℤ) : y^2 ≠ x^3+(8002) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 20) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8005 (x y : ℤ) : y^2 ≠ x^3+(8005) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 29) (b := 128) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 7 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8014 (x y : ℤ) : y^2 ≠ x^3+(8014) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 36) (b := 139) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 139) (u := 50) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8032 (x y : ℤ) : y^2 ≠ x^3+(8032) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 20) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p8039 (x y : ℤ) : y^2 ≠ x^3+(8039) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 42) (b := 257) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 257) (u := 16) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8071 (x y : ℤ) : y^2 ≠ x^3+(8071) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 64) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 6 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8098 (x y : ℤ) : y^2 ≠ x^3+(8098) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 20) (b := 7) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8148 (x y : ℤ) : y^2 ≠ x^3+(8148) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p8167 (x y : ℤ) : y^2 ≠ x^3+(8167) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 26) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8174 (x y : ℤ) : y^2 ≠ x^3+(8174) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 28) (b := 83) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 83) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8231 (x y : ℤ) : y^2 ≠ x^3+(8231) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 30) (b := 137) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 137) (u := 37) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8237 (x y : ℤ) : y^2 ≠ x^3+(8237) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8243 (x y : ℤ) : y^2 ≠ x^3+(8243) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 39) (b := 226) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 113) (u := 15) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8354 (x y : ℤ) : y^2 ≠ x^3+(8354) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 71) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 71) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8447 (x y : ℤ) : y^2 ≠ x^3+(8447) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 106) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8475 (x y : ℤ) : y^2 ≠ x^3+(8475) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 31) (b := 146) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8496 (x y : ℤ) : y^2 ≠ x^3+(8496) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -38) (b := 178) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 89) (u := 25) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p8532 (x y : ℤ) : y^2 ≠ x^3+(8532) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 46) (b := 298) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 149) (u := 44) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p8560 (x y : ℤ) : y^2 ≠ x^3+(8560) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -22) (b := 98) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p8578 (x y : ℤ) : y^2 ≠ x^3+(8578) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 20) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8598 (x y : ℤ) : y^2 ≠ x^3+(8598) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 26) (b := 67) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 67) (u := 20) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7661
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7712
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7758
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7838
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7839
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7842
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7887
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7962
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7968
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7982
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7998
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8002
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8005
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8014
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8032
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8039
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8071
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8098
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8148
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8167
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8174
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8231
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8237
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8243
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8354
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8447
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8475
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8496
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8532
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8560
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8578
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8598
