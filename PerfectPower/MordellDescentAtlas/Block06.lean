import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m6001 (x y : ℤ) : y^2 ≠ x^3+(-6001) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 13) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5995 (x y : ℤ) : y^2 ≠ x^3+(-5995) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 9) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5982 (x y : ℤ) : y^2 ≠ x^3+(-5982) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -44) (b := 199) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 199) (u := 20) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5968 (x y : ℤ) : y^2 ≠ x^3+(-5968) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 14) (b := 66) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 33) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m5962 (x y : ℤ) : y^2 ≠ x^3+(-5962) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 59) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 59) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5955 (x y : ℤ) : y^2 ≠ x^3+(-5955) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -11) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5937 (x y : ℤ) : y^2 ≠ x^3+(-5937) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -17) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5932 (x y : ℤ) : y^2 ≠ x^3+(-5932) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m5917 (x y : ℤ) : y^2 ≠ x^3+(-5917) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 160) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5904 (x y : ℤ) : y^2 ≠ x^3+(-5904) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -18) (b := 6) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m5875 (x y : ℤ) : y^2 ≠ x^3+(-5875) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -15) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5857 (x y : ℤ) : y^2 ≠ x^3+(-5857) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 5) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5840 (x y : ℤ) : y^2 ≠ x^3+(-5840) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -18) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m5836 (x y : ℤ) : y^2 ≠ x^3+(-5836) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m5833 (x y : ℤ) : y^2 ≠ x^3+(-5833) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5830 (x y : ℤ) : y^2 ≠ x^3+(-5830) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -18) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5819 (x y : ℤ) : y^2 ≠ x^3+(-5819) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -7) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5778 (x y : ℤ) : y^2 ≠ x^3+(-5778) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 83) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 83) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5761 (x y : ℤ) : y^2 ≠ x^3+(-5761) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 30) (b := 181) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 181) (u := 19) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5757 (x y : ℤ) : y^2 ≠ x^3+(-5757) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 43) (b := 292) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5734 (x y : ℤ) : y^2 ≠ x^3+(-5734) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -18) (b := 7) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5691 (x y : ℤ) : y^2 ≠ x^3+(-5691) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 25) (b := 146) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5601 (x y : ℤ) : y^2 ≠ x^3+(-5601) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5600 (x y : ℤ) : y^2 ≠ x^3+(-5600) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 44) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m5589 (x y : ℤ) : y^2 ≠ x^3+(-5589) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -17) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5561 (x y : ℤ) : y^2 ≠ x^3+(-5561) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5553 (x y : ℤ) : y^2 ≠ x^3+(-5553) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 53) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5545 (x y : ℤ) : y^2 ≠ x^3+(-5545) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5498 (x y : ℤ) : y^2 ≠ x^3+(-5498) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 57) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 57) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5484 (x y : ℤ) : y^2 ≠ x^3+(-5484) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m5477 (x y : ℤ) : y^2 ≠ x^3+(-5477) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m5475 (x y : ℤ) : y^2 ≠ x^3+(-5475) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 1) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m6001
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5995
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5982
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5968
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5962
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5955
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5937
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5932
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5917
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5904
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5875
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5857
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5840
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5836
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5833
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5830
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5819
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5778
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5761
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5757
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5734
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5691
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5601
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5600
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5589
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5561
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5553
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5545
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5498
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5484
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5477
#print axioms PerfectPower.MordellDescentAtlas.no_points_m5475
