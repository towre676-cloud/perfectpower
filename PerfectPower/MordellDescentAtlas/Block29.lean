import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p6421 (x y : ℤ) : y^2 ≠ x^3+(6421) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 41) (b := 250) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 125) (u := 57) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6423 (x y : ℤ) : y^2 ≠ x^3+(6423) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 65) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6459 (x y : ℤ) : y^2 ≠ x^3+(6459) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6530 (x y : ℤ) : y^2 ≠ x^3+(6530) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6542 (x y : ℤ) : y^2 ≠ x^3+(6542) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 27) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6543 (x y : ℤ) : y^2 ≠ x^3+(6543) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 34) (b := 181) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 181) (u := 19) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6557 (x y : ℤ) : y^2 ≠ x^3+(6557) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6603 (x y : ℤ) : y^2 ≠ x^3+(6603) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6650 (x y : ℤ) : y^2 ≠ x^3+(6650) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -18) (b := 79) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 79) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6691 (x y : ℤ) : y^2 ≠ x^3+(6691) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6759 (x y : ℤ) : y^2 ≠ x^3+(6759) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6795 (x y : ℤ) : y^2 ≠ x^3+(6795) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6843 (x y : ℤ) : y^2 ≠ x^3+(6843) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6855 (x y : ℤ) : y^2 ≠ x^3+(6855) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6902 (x y : ℤ) : y^2 ≠ x^3+(6902) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 50) (b := 243) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 243) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6918 (x y : ℤ) : y^2 ≠ x^3+(6918) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 26) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6927 (x y : ℤ) : y^2 ≠ x^3+(6927) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 61) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7024 (x y : ℤ) : y^2 ≠ x^3+(7024) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -22) (b := 94) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 47) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p7037 (x y : ℤ) : y^2 ≠ x^3+(7037) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 33) (b := 170) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7098 (x y : ℤ) : y^2 ≠ x^3+(7098) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -50) (b := 257) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 257) (u := 60) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7136 (x y : ℤ) : y^2 ≠ x^3+(7136) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -36) (b := 164) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p7162 (x y : ℤ) : y^2 ≠ x^3+(7162) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 14) (b := 47) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 47) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7278 (x y : ℤ) : y^2 ≠ x^3+(7278) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 19) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 19) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7284 (x y : ℤ) : y^2 ≠ x^3+(7284) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p7348 (x y : ℤ) : y^2 ≠ x^3+(7348) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 38) (b := 218) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 109) (u := 33) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p7375 (x y : ℤ) : y^2 ≠ x^3+(7375) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 26) (b := 101) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 101) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7389 (x y : ℤ) : y^2 ≠ x^3+(7389) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 37) (b := 208) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7422 (x y : ℤ) : y^2 ≠ x^3+(7422) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7472 (x y : ℤ) : y^2 ≠ x^3+(7472) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -6) (b := 62) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p7520 (x y : ℤ) : y^2 ≠ x^3+(7520) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p7543 (x y : ℤ) : y^2 ≠ x^3+(7543) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p7546 (x y : ℤ) : y^2 ≠ x^3+(7546) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 14) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6421
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6423
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6459
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6530
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6542
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6543
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6557
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6603
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6650
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6691
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6759
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6795
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6843
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6855
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6902
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6918
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6927
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7024
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7037
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7098
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7136
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7162
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7278
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7284
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7348
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7375
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7389
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7422
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7472
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7520
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7543
#print axioms PerfectPower.MordellDescentAtlas.no_points_p7546
