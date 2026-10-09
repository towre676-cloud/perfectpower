import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m1130 (x y : ℤ) : y^2 ≠ x^3+(-1130) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 59) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 59) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1129 (x y : ℤ) : y^2 ≠ x^3+(-1129) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1126 (x y : ℤ) : y^2 ≠ x^3+(-1126) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -42) (b := 191) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 191) (u := 57) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1100 (x y : ℤ) : y^2 ≠ x^3+(-1100) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m1057 (x y : ℤ) : y^2 ≠ x^3+(-1057) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 29) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1054 (x y : ℤ) : y^2 ≠ x^3+(-1054) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -36) (b := 151) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 151) (u := 46) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1051 (x y : ℤ) : y^2 ≠ x^3+(-1051) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -3) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1030 (x y : ℤ) : y^2 ≠ x^3+(-1030) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -18) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1025 (x y : ℤ) : y^2 ≠ x^3+(-1025) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 5) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1019 (x y : ℤ) : y^2 ≠ x^3+(-1019) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -7) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1004 (x y : ℤ) : y^2 ≠ x^3+(-1004) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m1002 (x y : ℤ) : y^2 ≠ x^3+(-1002) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 50) (b := 251) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 251) (u := 91) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1001 (x y : ℤ) : y^2 ≠ x^3+(-1001) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m998 (x y : ℤ) : y^2 ≠ x^3+(-998) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -10) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m997 (x y : ℤ) : y^2 ≠ x^3+(-997) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m985 (x y : ℤ) : y^2 ≠ x^3+(-985) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m978 (x y : ℤ) : y^2 ≠ x^3+(-978) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 67) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 67) (u := 20) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m977 (x y : ℤ) : y^2 ≠ x^3+(-977) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 61) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m976 (x y : ℤ) : y^2 ≠ x^3+(-976) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -2) (b := 22) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m946 (x y : ℤ) : y^2 ≠ x^3+(-946) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 28) (b := 107) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 107) (u := 31) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m940 (x y : ℤ) : y^2 ≠ x^3+(-940) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m938 (x y : ℤ) : y^2 ≠ x^3+(-938) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -6) (b := 19) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 19) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m902 (x y : ℤ) : y^2 ≠ x^3+(-902) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -10) (b := 7) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m899 (x y : ℤ) : y^2 ≠ x^3+(-899) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 5) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m864 (x y : ℤ) : y^2 ≠ x^3+(-864) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 36) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m849 (x y : ℤ) : y^2 ≠ x^3+(-849) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 29) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m848 (x y : ℤ) : y^2 ≠ x^3+(-848) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 30) (b := 118) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 59) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m841 (x y : ℤ) : y^2 ≠ x^3+(-841) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 25) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m833 (x y : ℤ) : y^2 ≠ x^3+(-833) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 2) (b := 29) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m829 (x y : ℤ) : y^2 ≠ x^3+(-829) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m813 (x y : ℤ) : y^2 ≠ x^3+(-813) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m801 (x y : ℤ) : y^2 ≠ x^3+(-801) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1130
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1129
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1126
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1100
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1057
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1054
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1051
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1030
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1025
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1019
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1004
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1002
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1001
#print axioms PerfectPower.MordellDescentAtlas.no_points_m998
#print axioms PerfectPower.MordellDescentAtlas.no_points_m997
#print axioms PerfectPower.MordellDescentAtlas.no_points_m985
#print axioms PerfectPower.MordellDescentAtlas.no_points_m978
#print axioms PerfectPower.MordellDescentAtlas.no_points_m977
#print axioms PerfectPower.MordellDescentAtlas.no_points_m976
#print axioms PerfectPower.MordellDescentAtlas.no_points_m946
#print axioms PerfectPower.MordellDescentAtlas.no_points_m940
#print axioms PerfectPower.MordellDescentAtlas.no_points_m938
#print axioms PerfectPower.MordellDescentAtlas.no_points_m902
#print axioms PerfectPower.MordellDescentAtlas.no_points_m899
#print axioms PerfectPower.MordellDescentAtlas.no_points_m864
#print axioms PerfectPower.MordellDescentAtlas.no_points_m849
#print axioms PerfectPower.MordellDescentAtlas.no_points_m848
#print axioms PerfectPower.MordellDescentAtlas.no_points_m841
#print axioms PerfectPower.MordellDescentAtlas.no_points_m833
#print axioms PerfectPower.MordellDescentAtlas.no_points_m829
#print axioms PerfectPower.MordellDescentAtlas.no_points_m813
#print axioms PerfectPower.MordellDescentAtlas.no_points_m801
