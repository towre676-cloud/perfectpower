import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m4901 (x y : ℤ) : y^2 ≠ x^3+(-4901) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4873 (x y : ℤ) : y^2 ≠ x^3+(-4873) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 42) (b := 281) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 281) (u := 53) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4867 (x y : ℤ) : y^2 ≠ x^3+(-4867) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 33) (b := 202) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 101) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4826 (x y : ℤ) : y^2 ≠ x^3+(-4826) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4825 (x y : ℤ) : y^2 ≠ x^3+(-4825) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 64) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 6 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4816 (x y : ℤ) : y^2 ≠ x^3+(-4816) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 46) (b := 226) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 113) (u := 26) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m4774 (x y : ℤ) : y^2 ≠ x^3+(-4774) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -18) (b := 23) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4770 (x y : ℤ) : y^2 ≠ x^3+(-4770) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 57) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 57) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4749 (x y : ℤ) : y^2 ≠ x^3+(-4749) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4747 (x y : ℤ) : y^2 ≠ x^3+(-4747) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 9) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4733 (x y : ℤ) : y^2 ≠ x^3+(-4733) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 130) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4721 (x y : ℤ) : y^2 ≠ x^3+(-4721) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 61) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4697 (x y : ℤ) : y^2 ≠ x^3+(-4697) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4684 (x y : ℤ) : y^2 ≠ x^3+(-4684) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 30) (b := 178) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m4651 (x y : ℤ) : y^2 ≠ x^3+(-4651) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -3) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4649 (x y : ℤ) : y^2 ≠ x^3+(-4649) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 35) (b := 218) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 109) (u := 33) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4638 (x y : ℤ) : y^2 ≠ x^3+(-4638) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4625 (x y : ℤ) : y^2 ≠ x^3+(-4625) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4597 (x y : ℤ) : y^2 ≠ x^3+(-4597) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4593 (x y : ℤ) : y^2 ≠ x^3+(-4593) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 43) (b := 290) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 145) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4531 (x y : ℤ) : y^2 ≠ x^3+(-4531) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -15) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4499 (x y : ℤ) : y^2 ≠ x^3+(-4499) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 5) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4481 (x y : ℤ) : y^2 ≠ x^3+(-4481) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4441 (x y : ℤ) : y^2 ≠ x^3+(-4441) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 65) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4425 (x y : ℤ) : y^2 ≠ x^3+(-4425) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4377 (x y : ℤ) : y^2 ≠ x^3+(-4377) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 106) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4369 (x y : ℤ) : y^2 ≠ x^3+(-4369) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 101) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 101) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4364 (x y : ℤ) : y^2 ≠ x^3+(-4364) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m4329 (x y : ℤ) : y^2 ≠ x^3+(-4329) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4320 (x y : ℤ) : y^2 ≠ x^3+(-4320) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 36) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m4281 (x y : ℤ) : y^2 ≠ x^3+(-4281) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m4236 (x y : ℤ) : y^2 ≠ x^3+(-4236) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 122) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4901
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4873
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4867
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4826
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4825
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4816
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4774
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4770
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4749
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4747
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4733
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4721
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4697
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4684
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4651
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4649
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4638
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4625
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4597
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4593
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4531
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4499
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4481
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4441
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4425
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4377
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4369
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4364
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4329
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4320
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4281
#print axioms PerfectPower.MordellDescentAtlas.no_points_m4236
