import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m3221 (x y : ℤ) : y^2 ≠ x^3+(-3221) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3209 (x y : ℤ) : y^2 ≠ x^3+(-3209) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 38) (b := 241) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 241) (u := 64) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3198 (x y : ℤ) : y^2 ≠ x^3+(-3198) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 49) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 49) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3186 (x y : ℤ) : y^2 ≠ x^3+(-3186) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 27) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3181 (x y : ℤ) : y^2 ≠ x^3+(-3181) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 39) (b := 250) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 125) (u := 57) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3171 (x y : ℤ) : y^2 ≠ x^3+(-3171) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 37) (b := 232) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3153 (x y : ℤ) : y^2 ≠ x^3+(-3153) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 46) (b := 317) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 317) (u := 114) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3148 (x y : ℤ) : y^2 ≠ x^3+(-3148) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m3146 (x y : ℤ) : y^2 ≠ x^3+(-3146) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 67) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 67) (u := 20) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3141 (x y : ℤ) : y^2 ≠ x^3+(-3141) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 100) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3134 (x y : ℤ) : y^2 ≠ x^3+(-3134) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -28) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 14) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3088 (x y : ℤ) : y^2 ≠ x^3+(-3088) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 14) (b := 54) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m3033 (x y : ℤ) : y^2 ≠ x^3+(-3033) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3025 (x y : ℤ) : y^2 ≠ x^3+(-3025) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 53) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m3021 (x y : ℤ) : y^2 ≠ x^3+(-3021) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2986 (x y : ℤ) : y^2 ≠ x^3+(-2986) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -14) (b := 11) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2960 (x y : ℤ) : y^2 ≠ x^3+(-2960) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -22) (b := 62) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m2931 (x y : ℤ) : y^2 ≠ x^3+(-2931) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -11) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2929 (x y : ℤ) : y^2 ≠ x^3+(-2929) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 30) (b := 173) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 173) (u := 80) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2913 (x y : ℤ) : y^2 ≠ x^3+(-2913) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 13) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2906 (x y : ℤ) : y^2 ≠ x^3+(-2906) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -14) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2896 (x y : ℤ) : y^2 ≠ x^3+(-2896) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -2) (b := 38) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 19) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m2873 (x y : ℤ) : y^2 ≠ x^3+(-2873) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2843 (x y : ℤ) : y^2 ≠ x^3+(-2843) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -7) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2829 (x y : ℤ) : y^2 ≠ x^3+(-2829) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2817 (x y : ℤ) : y^2 ≠ x^3+(-2817) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 53) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2801 (x y : ℤ) : y^2 ≠ x^3+(-2801) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 2) (b := 53) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2769 (x y : ℤ) : y^2 ≠ x^3+(-2769) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 5) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2765 (x y : ℤ) : y^2 ≠ x^3+(-2765) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 64) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 6 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2762 (x y : ℤ) : y^2 ≠ x^3+(-2762) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -14) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2746 (x y : ℤ) : y^2 ≠ x^3+(-2746) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -14) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2745 (x y : ℤ) : y^2 ≠ x^3+(-2745) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -14) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3221
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3209
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3198
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3186
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3181
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3171
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3153
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3148
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3146
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3141
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3134
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3088
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3033
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3025
#print axioms PerfectPower.MordellDescentAtlas.no_points_m3021
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2986
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2960
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2931
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2929
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2913
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2906
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2896
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2873
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2843
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2829
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2817
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2801
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2769
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2765
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2762
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2746
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2745
