import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p2055 (x y : ℤ) : y^2 ≠ x^3+(2055) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 34) (b := 193) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 193) (u := 81) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2068 (x y : ℤ) : y^2 ≠ x^3+(2068) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p2071 (x y : ℤ) : y^2 ≠ x^3+(2071) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 35) (b := 202) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 101) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2082 (x y : ℤ) : y^2 ≠ x^3+(2082) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 71) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 71) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2096 (x y : ℤ) : y^2 ≠ x^3+(2096) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 14) (b := 18) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p2111 (x y : ℤ) : y^2 ≠ x^3+(2111) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 61) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2119 (x y : ℤ) : y^2 ≠ x^3+(2119) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 25) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2133 (x y : ℤ) : y^2 ≠ x^3+(2133) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 13) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2134 (x y : ℤ) : y^2 ≠ x^3+(2134) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 43) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 43) (u := 16) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2138 (x y : ℤ) : y^2 ≠ x^3+(2138) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 6) (b := 31) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2167 (x y : ℤ) : y^2 ≠ x^3+(2167) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 100) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2181 (x y : ℤ) : y^2 ≠ x^3+(2181) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 13) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2219 (x y : ℤ) : y^2 ≠ x^3+(2219) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2235 (x y : ℤ) : y^2 ≠ x^3+(2235) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2306 (x y : ℤ) : y^2 ≠ x^3+(2306) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2350 (x y : ℤ) : y^2 ≠ x^3+(2350) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 28) (b := 99) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 99) (u := 14) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2351 (x y : ℤ) : y^2 ≠ x^3+(2351) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2362 (x y : ℤ) : y^2 ≠ x^3+(2362) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -10) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2413 (x y : ℤ) : y^2 ≠ x^3+(2413) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 17) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2431 (x y : ℤ) : y^2 ≠ x^3+(2431) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 38) (b := 229) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 229) (u := 107) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2455 (x y : ℤ) : y^2 ≠ x^3+(2455) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2470 (x y : ℤ) : y^2 ≠ x^3+(2470) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2485 (x y : ℤ) : y^2 ≠ x^3+(2485) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 29) (b := 148) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2575 (x y : ℤ) : y^2 ≠ x^3+(2575) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 13) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2644 (x y : ℤ) : y^2 ≠ x^3+(2644) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p2658 (x y : ℤ) : y^2 ≠ x^3+(2658) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 32) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2672 (x y : ℤ) : y^2 ≠ x^3+(2672) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 14) (b := 6) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p2690 (x y : ℤ) : y^2 ≠ x^3+(2690) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 47) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 47) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2699 (x y : ℤ) : y^2 ≠ x^3+(2699) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2719 (x y : ℤ) : y^2 ≠ x^3+(2719) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 5) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2727 (x y : ℤ) : y^2 ≠ x^3+(2727) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p2736 (x y : ℤ) : y^2 ≠ x^3+(2736) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 14) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2055
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2068
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2071
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2082
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2096
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2111
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2119
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2133
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2134
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2138
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2167
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2181
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2219
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2235
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2306
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2350
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2351
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2362
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2413
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2431
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2455
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2470
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2485
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2575
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2644
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2658
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2672
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2690
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2699
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2719
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2727
#print axioms PerfectPower.MordellDescentAtlas.no_points_p2736
