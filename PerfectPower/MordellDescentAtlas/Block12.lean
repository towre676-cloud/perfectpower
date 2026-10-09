import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m2732 (x y : ℤ) : y^2 ≠ x^3+(-2732) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m2731 (x y : ℤ) : y^2 ≠ x^3+(-2731) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -3) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2721 (x y : ℤ) : y^2 ≠ x^3+(-2721) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 61) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2717 (x y : ℤ) : y^2 ≠ x^3+(-2717) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 122) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2705 (x y : ℤ) : y^2 ≠ x^3+(-2705) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2698 (x y : ℤ) : y^2 ≠ x^3+(-2698) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 43) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 43) (u := 16) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2681 (x y : ℤ) : y^2 ≠ x^3+(-2681) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2677 (x y : ℤ) : y^2 ≠ x^3+(-2677) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2658 (x y : ℤ) : y^2 ≠ x^3+(-2658) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2656 (x y : ℤ) : y^2 ≠ x^3+(-2656) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 36) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m2641 (x y : ℤ) : y^2 ≠ x^3+(-2641) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 42) (b := 277) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 277) (u := 60) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2635 (x y : ℤ) : y^2 ≠ x^3+(-2635) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 9) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2625 (x y : ℤ) : y^2 ≠ x^3+(-2625) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2597 (x y : ℤ) : y^2 ≠ x^3+(-2597) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2593 (x y : ℤ) : y^2 ≠ x^3+(-2593) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 53) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2585 (x y : ℤ) : y^2 ≠ x^3+(-2585) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2579 (x y : ℤ) : y^2 ≠ x^3+(-2579) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 5) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2528 (x y : ℤ) : y^2 ≠ x^3+(-2528) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 4) (b := 36) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m2508 (x y : ℤ) : y^2 ≠ x^3+(-2508) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m2507 (x y : ℤ) : y^2 ≠ x^3+(-2507) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 29) (b := 164) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2501 (x y : ℤ) : y^2 ≠ x^3+(-2501) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2499 (x y : ℤ) : y^2 ≠ x^3+(-2499) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 1) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2473 (x y : ℤ) : y^2 ≠ x^3+(-2473) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2470 (x y : ℤ) : y^2 ≠ x^3+(-2470) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -18) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2453 (x y : ℤ) : y^2 ≠ x^3+(-2453) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2450 (x y : ℤ) : y^2 ≠ x^3+(-2450) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 19) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 19) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2427 (x y : ℤ) : y^2 ≠ x^3+(-2427) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 13) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2394 (x y : ℤ) : y^2 ≠ x^3+(-2394) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -6) (b := 33) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 33) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2369 (x y : ℤ) : y^2 ≠ x^3+(-2369) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2362 (x y : ℤ) : y^2 ≠ x^3+(-2362) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2361 (x y : ℤ) : y^2 ≠ x^3+(-2361) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2355 (x y : ℤ) : y^2 ≠ x^3+(-2355) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -11) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2732
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2731
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2721
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2717
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2705
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2698
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2681
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2677
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2658
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2656
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2641
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2635
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2625
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2597
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2593
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2585
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2579
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2528
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2508
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2507
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2501
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2499
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2473
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2470
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2453
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2450
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2427
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2394
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2369
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2362
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2361
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2355
