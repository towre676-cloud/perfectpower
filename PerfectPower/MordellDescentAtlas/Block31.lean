import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p8688 (x y : ℤ) : y^2 ≠ x^3+(8688) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 10) (b := 62) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p8800 (x y : ℤ) : y^2 ≠ x^3+(8800) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -28) (b := 124) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p8803 (x y : ℤ) : y^2 ≠ x^3+(8803) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8830 (x y : ℤ) : y^2 ≠ x^3+(8830) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 28) (b := 81) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 81) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8838 (x y : ℤ) : y^2 ≠ x^3+(8838) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 50) (b := 241) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 241) (u := 38) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8861 (x y : ℤ) : y^2 ≠ x^3+(8861) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8867 (x y : ℤ) : y^2 ≠ x^3+(8867) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 104) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8901 (x y : ℤ) : y^2 ≠ x^3+(8901) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 25) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8928 (x y : ℤ) : y^2 ≠ x^3+(8928) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 92) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p8930 (x y : ℤ) : y^2 ≠ x^3+(8930) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 32) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8967 (x y : ℤ) : y^2 ≠ x^3+(8967) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p8994 (x y : ℤ) : y^2 ≠ x^3+(8994) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -44) (b := 217) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 217) (u := 39) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9005 (x y : ℤ) : y^2 ≠ x^3+(9005) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9046 (x y : ℤ) : y^2 ≠ x^3+(9046) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 34) (b := 123) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 123) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9058 (x y : ℤ) : y^2 ≠ x^3+(9058) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 20) (b := 23) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9082 (x y : ℤ) : y^2 ≠ x^3+(9082) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -10) (b := 71) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 71) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9118 (x y : ℤ) : y^2 ≠ x^3+(9118) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 36) (b := 137) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 137) (u := 51) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9122 (x y : ℤ) : y^2 ≠ x^3+(9122) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -36) (b := 167) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 167) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9184 (x y : ℤ) : y^2 ≠ x^3+(9184) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p9197 (x y : ℤ) : y^2 ≠ x^3+(9197) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9245 (x y : ℤ) : y^2 ≠ x^3+(9245) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9279 (x y : ℤ) : y^2 ≠ x^3+(9279) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9312 (x y : ℤ) : y^2 ≠ x^3+(9312) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 4) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p9375 (x y : ℤ) : y^2 ≠ x^3+(9375) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 34) (b := 173) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 173) (u := 80) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9463 (x y : ℤ) : y^2 ≠ x^3+(9463) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9492 (x y : ℤ) : y^2 ≠ x^3+(9492) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p9568 (x y : ℤ) : y^2 ≠ x^3+(9568) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 20) (b := 28) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p9655 (x y : ℤ) : y^2 ≠ x^3+(9655) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 26) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9658 (x y : ℤ) : y^2 ≠ x^3+(9658) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -10) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 32) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9667 (x y : ℤ) : y^2 ≠ x^3+(9667) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9683 (x y : ℤ) : y^2 ≠ x^3+(9683) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 100) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p9807 (x y : ℤ) : y^2 ≠ x^3+(9807) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 29) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8688
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8800
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8803
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8830
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8838
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8861
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8867
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8901
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8928
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8930
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8967
#print axioms PerfectPower.MordellDescentAtlas.no_points_p8994
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9005
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9046
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9058
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9082
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9118
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9122
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9184
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9197
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9245
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9279
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9312
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9375
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9463
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9492
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9568
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9655
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9658
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9667
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9683
#print axioms PerfectPower.MordellDescentAtlas.no_points_p9807
