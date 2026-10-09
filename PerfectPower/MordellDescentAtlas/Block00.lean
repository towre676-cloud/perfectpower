import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m9985 (x y : ℤ) : y^2 ≠ x^3+(-9985) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 101) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 101) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9973 (x y : ℤ) : y^2 ≠ x^3+(-9973) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 100) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9971 (x y : ℤ) : y^2 ≠ x^3+(-9971) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 17) (b := 122) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9969 (x y : ℤ) : y^2 ≠ x^3+(-9969) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9937 (x y : ℤ) : y^2 ≠ x^3+(-9937) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -21) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9905 (x y : ℤ) : y^2 ≠ x^3+(-9905) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 106) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9875 (x y : ℤ) : y^2 ≠ x^3+(-9875) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 5) (b := 100) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9824 (x y : ℤ) : y^2 ≠ x^3+(-9824) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 76) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 19) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m9793 (x y : ℤ) : y^2 ≠ x^3+(-9793) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 125) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 125) (u := 57) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9737 (x y : ℤ) : y^2 ≠ x^3+(-9737) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 148) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9706 (x y : ℤ) : y^2 ≠ x^3+(-9706) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -14) (b := 59) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 59) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9661 (x y : ℤ) : y^2 ≠ x^3+(-9661) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -21) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9658 (x y : ℤ) : y^2 ≠ x^3+(-9658) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9657 (x y : ℤ) : y^2 ≠ x^3+(-9657) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 100) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9625 (x y : ℤ) : y^2 ≠ x^3+(-9625) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9563 (x y : ℤ) : y^2 ≠ x^3+(-9563) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -19) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9553 (x y : ℤ) : y^2 ≠ x^3+(-9553) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 61) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9537 (x y : ℤ) : y^2 ≠ x^3+(-9537) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -17) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9525 (x y : ℤ) : y^2 ≠ x^3+(-9525) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 128) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 7 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9517 (x y : ℤ) : y^2 ≠ x^3+(-9517) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -21) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9485 (x y : ℤ) : y^2 ≠ x^3+(-9485) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 104) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9470 (x y : ℤ) : y^2 ≠ x^3+(-9470) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -28) (b := 79) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 79) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9458 (x y : ℤ) : y^2 ≠ x^3+(-9458) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -20) (b := 27) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9433 (x y : ℤ) : y^2 ≠ x^3+(-9433) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 42) (b := 289) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 289) (u := 38) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9417 (x y : ℤ) : y^2 ≠ x^3+(-9417) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9401 (x y : ℤ) : y^2 ≠ x^3+(-9401) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 2) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9361 (x y : ℤ) : y^2 ≠ x^3+(-9361) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -21) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9325 (x y : ℤ) : y^2 ≠ x^3+(-9325) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -21) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9312 (x y : ℤ) : y^2 ≠ x^3+(-9312) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m9297 (x y : ℤ) : y^2 ≠ x^3+(-9297) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 43) (b := 298) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 149) (u := 44) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9277 (x y : ℤ) : y^2 ≠ x^3+(-9277) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -21) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m9265 (x y : ℤ) : y^2 ≠ x^3+(-9265) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -21) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9985
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9973
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9971
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9969
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9937
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9905
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9875
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9824
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9793
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9737
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9706
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9661
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9658
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9657
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9625
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9563
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9553
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9537
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9525
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9517
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9485
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9470
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9458
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9433
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9417
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9401
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9361
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9325
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9312
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9297
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9277
#print axioms PerfectPower.MordellDescentAtlas.no_points_m9265
