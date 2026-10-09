import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m7098 (x y : ℤ) : y^2 ≠ x^3+(-7098) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 50) (b := 257) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 257) (u := 68) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7073 (x y : ℤ) : y^2 ≠ x^3+(-7073) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 26) (b := 157) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 157) (u := 28) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7067 (x y : ℤ) : y^2 ≠ x^3+(-7067) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -7) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7046 (x y : ℤ) : y^2 ≠ x^3+(-7046) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -34) (b := 127) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 127) (u := 16) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7026 (x y : ℤ) : y^2 ≠ x^3+(-7026) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 59) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 59) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7009 (x y : ℤ) : y^2 ≠ x^3+(-7009) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6988 (x y : ℤ) : y^2 ≠ x^3+(-6988) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m6969 (x y : ℤ) : y^2 ≠ x^3+(-6969) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 65) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6954 (x y : ℤ) : y^2 ≠ x^3+(-6954) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 2) (b := 59) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 59) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6942 (x y : ℤ) : y^2 ≠ x^3+(-6942) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 23) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6937 (x y : ℤ) : y^2 ≠ x^3+(-6937) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 113) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 113) (u := 15) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6930 (x y : ℤ) : y^2 ≠ x^3+(-6930) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 51) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 51) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6923 (x y : ℤ) : y^2 ≠ x^3+(-6923) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -19) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6921 (x y : ℤ) : y^2 ≠ x^3+(-6921) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6918 (x y : ℤ) : y^2 ≠ x^3+(-6918) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -26) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 32) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6898 (x y : ℤ) : y^2 ≠ x^3+(-6898) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 4) (b := 59) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 59) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6875 (x y : ℤ) : y^2 ≠ x^3+(-6875) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -19) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6849 (x y : ℤ) : y^2 ≠ x^3+(-6849) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6821 (x y : ℤ) : y^2 ≠ x^3+(-6821) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6800 (x y : ℤ) : y^2 ≠ x^3+(-6800) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -18) (b := 22) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m6739 (x y : ℤ) : y^2 ≠ x^3+(-6739) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -15) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6732 (x y : ℤ) : y^2 ≠ x^3+(-6732) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m6725 (x y : ℤ) : y^2 ≠ x^3+(-6725) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6723 (x y : ℤ) : y^2 ≠ x^3+(-6723) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 1) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6714 (x y : ℤ) : y^2 ≠ x^3+(-6714) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -6) (b := 57) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 57) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6697 (x y : ℤ) : y^2 ≠ x^3+(-6697) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6673 (x y : ℤ) : y^2 ≠ x^3+(-6673) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 29) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6665 (x y : ℤ) : y^2 ≠ x^3+(-6665) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6625 (x y : ℤ) : y^2 ≠ x^3+(-6625) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 100) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6597 (x y : ℤ) : y^2 ≠ x^3+(-6597) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 116) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6562 (x y : ℤ) : y^2 ≠ x^3+(-6562) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 57) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 57) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m6525 (x y : ℤ) : y^2 ≠ x^3+(-6525) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7098
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7073
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7067
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7046
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7026
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7009
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6988
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6969
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6954
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6942
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6937
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6930
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6923
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6921
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6918
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6898
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6875
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6849
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6821
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6800
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6739
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6732
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6725
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6723
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6714
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6697
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6673
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6665
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6625
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6597
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6562
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6525
