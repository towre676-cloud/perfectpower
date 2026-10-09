import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p2740 (x y : ℤ) : y^2 ≠ x^3+(2740) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p2743 (x y : ℤ) : y^2 ≠ x^3+(2743) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2746 (x y : ℤ) : y^2 ≠ x^3+(2746) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 14) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2763 (x y : ℤ) : y^2 ≠ x^3+(2763) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 64) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 6 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2783 (x y : ℤ) : y^2 ≠ x^3+(2783) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 130) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2786 (x y : ℤ) : y^2 ≠ x^3+(2786) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 23) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2798 (x y : ℤ) : y^2 ≠ x^3+(2798) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 51) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 51) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2800 (x y : ℤ) : y^2 ≠ x^3+(2800) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -22) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p2842 (x y : ℤ) : y^2 ≠ x^3+(2842) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 14) (b := 7) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2861 (x y : ℤ) : y^2 ≠ x^3+(2861) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2875 (x y : ℤ) : y^2 ≠ x^3+(2875) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 35) (b := 200) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2895 (x y : ℤ) : y^2 ≠ x^3+(2895) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 31) (b := 164) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2975 (x y : ℤ) : y^2 ≠ x^3+(2975) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3023 (x y : ℤ) : y^2 ≠ x^3+(3023) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 53) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3074 (x y : ℤ) : y^2 ≠ x^3+(3074) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3119 (x y : ℤ) : y^2 ≠ x^3+(3119) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3134 (x y : ℤ) : y^2 ≠ x^3+(3134) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 28) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3199 (x y : ℤ) : y^2 ≠ x^3+(3199) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 50) (b := 349) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 349) (u := 136) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3275 (x y : ℤ) : y^2 ≠ x^3+(3275) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3296 (x y : ℤ) : y^2 ≠ x^3+(3296) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 28) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p3298 (x y : ℤ) : y^2 ≠ x^3+(3298) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3299 (x y : ℤ) : y^2 ≠ x^3+(3299) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 128) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 7 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3311 (x y : ℤ) : y^2 ≠ x^3+(3311) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3312 (x y : ℤ) : y^2 ≠ x^3+(3312) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 10) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p3322 (x y : ℤ) : y^2 ≠ x^3+(3322) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 14) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3354 (x y : ℤ) : y^2 ≠ x^3+(3354) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -2) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3359 (x y : ℤ) : y^2 ≠ x^3+(3359) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3371 (x y : ℤ) : y^2 ≠ x^3+(3371) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3405 (x y : ℤ) : y^2 ≠ x^3+(3405) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 49) (b := 338) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 169) (u := 70) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3418 (x y : ℤ) : y^2 ≠ x^3+(3418) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -10) (b := 47) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 47) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3423 (x y : ℤ) : y^2 ≠ x^3+(3423) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p3426 (x y : ℤ) : y^2 ≠ x^3+(3426) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 4) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2740
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2743
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2746
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2763
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2783
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2786
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2798
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2800
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2842
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2861
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2875
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2895
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2975
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3023
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3074
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3119
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3134
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3199
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3275
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3296
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3298
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3299
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3311
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3312
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3322
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3354
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3359
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3371
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3405
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3418
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3423
#print axioms PerfectPower.MordellDescentAtlas.no_points_p3426
