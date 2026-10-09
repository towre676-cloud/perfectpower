import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p4463 (x y : ℤ) : y^2 ≠ x^3+(4463) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4482 (x y : ℤ) : y^2 ≠ x^3+(4482) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 79) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 79) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4634 (x y : ℤ) : y^2 ≠ x^3+(4634) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 6) (b := 47) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 47) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4637 (x y : ℤ) : y^2 ≠ x^3+(4637) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4638 (x y : ℤ) : y^2 ≠ x^3+(4638) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4666 (x y : ℤ) : y^2 ≠ x^3+(4666) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 14) (b := 31) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4738 (x y : ℤ) : y^2 ≠ x^3+(4738) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4794 (x y : ℤ) : y^2 ≠ x^3+(4794) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -2) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4799 (x y : ℤ) : y^2 ≠ x^3+(4799) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 122) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4807 (x y : ℤ) : y^2 ≠ x^3+(4807) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 26) (b := 113) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 113) (u := 15) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4813 (x y : ℤ) : y^2 ≠ x^3+(4813) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 17) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4826 (x y : ℤ) : y^2 ≠ x^3+(4826) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -18) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 32) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4866 (x y : ℤ) : y^2 ≠ x^3+(4866) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 4) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4909 (x y : ℤ) : y^2 ≠ x^3+(4909) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 17) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4982 (x y : ℤ) : y^2 ≠ x^3+(4982) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 34) (b := 131) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 131) (u := 28) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p4991 (x y : ℤ) : y^2 ≠ x^3+(4991) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 29) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5018 (x y : ℤ) : y^2 ≠ x^3+(5018) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 6) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5079 (x y : ℤ) : y^2 ≠ x^3+(5079) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 34) (b := 185) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 185) (u := 43) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5090 (x y : ℤ) : y^2 ≠ x^3+(5090) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5110 (x y : ℤ) : y^2 ≠ x^3+(5110) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 19) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 19) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5114 (x y : ℤ) : y^2 ≠ x^3+(5114) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -42) (b := 199) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 199) (u := 20) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5165 (x y : ℤ) : y^2 ≠ x^3+(5165) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 64) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 6 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5172 (x y : ℤ) : y^2 ≠ x^3+(5172) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p5186 (x y : ℤ) : y^2 ≠ x^3+(5186) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -36) (b := 161) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 161) (u := 18) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5207 (x y : ℤ) : y^2 ≠ x^3+(5207) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 25) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5227 (x y : ℤ) : y^2 ≠ x^3+(5227) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 47) (b := 314) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 157) (u := 28) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5232 (x y : ℤ) : y^2 ≠ x^3+(5232) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 10) (b := 46) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p5239 (x y : ℤ) : y^2 ≠ x^3+(5239) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 35) (b := 194) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 97) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5254 (x y : ℤ) : y^2 ≠ x^3+(5254) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5259 (x y : ℤ) : y^2 ≠ x^3+(5259) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5319 (x y : ℤ) : y^2 ≠ x^3+(5319) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5408 (x y : ℤ) : y^2 ≠ x^3+(5408) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 36) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4463
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4482
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4634
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4637
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4638
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4666
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4738
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4794
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4799
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4807
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4813
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4826
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4866
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4909
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4982
#print axioms PerfectPower.MordellDescentAtlas.no_points_p4991
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5018
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5079
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5090
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5110
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5114
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5165
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5172
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5186
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5207
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5227
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5232
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5239
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5254
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5259
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5319
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5408
