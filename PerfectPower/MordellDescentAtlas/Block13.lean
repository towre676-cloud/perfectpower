import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m2329 (x y : ℤ) : y^2 ≠ x^3+(-2329) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2320 (x y : ℤ) : y^2 ≠ x^3+(-2320) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -2) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m2306 (x y : ℤ) : y^2 ≠ x^3+(-2306) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2297 (x y : ℤ) : y^2 ≠ x^3+(-2297) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2284 (x y : ℤ) : y^2 ≠ x^3+(-2284) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m2261 (x y : ℤ) : y^2 ≠ x^3+(-2261) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2242 (x y : ℤ) : y^2 ≠ x^3+(-2242) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 33) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 33) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2221 (x y : ℤ) : y^2 ≠ x^3+(-2221) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 148) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2213 (x y : ℤ) : y^2 ≠ x^3+(-2213) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2201 (x y : ℤ) : y^2 ≠ x^3+(-2201) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2178 (x y : ℤ) : y^2 ≠ x^3+(-2178) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 44) (b := 209) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 209) (u := 25) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2170 (x y : ℤ) : y^2 ≠ x^3+(-2170) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 2) (b := 33) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 33) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2157 (x y : ℤ) : y^2 ≠ x^3+(-2157) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2156 (x y : ℤ) : y^2 ≠ x^3+(-2156) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m2144 (x y : ℤ) : y^2 ≠ x^3+(-2144) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 44) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m2121 (x y : ℤ) : y^2 ≠ x^3+(-2121) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 113) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 113) (u := 15) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2114 (x y : ℤ) : y^2 ≠ x^3+(-2114) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 4) (b := 33) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 33) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2101 (x y : ℤ) : y^2 ≠ x^3+(-2101) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2089 (x y : ℤ) : y^2 ≠ x^3+(-2089) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2069 (x y : ℤ) : y^2 ≠ x^3+(-2069) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 35) (b := 212) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2067 (x y : ℤ) : y^2 ≠ x^3+(-2067) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 49) (b := 346) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 173) (u := 80) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2033 (x y : ℤ) : y^2 ≠ x^3+(-2033) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2026 (x y : ℤ) : y^2 ≠ x^3+(-2026) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 26) (b := 99) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 99) (u := 14) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m2016 (x y : ℤ) : y^2 ≠ x^3+(-2016) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 12) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m1970 (x y : ℤ) : y^2 ≠ x^3+(-1970) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 11) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1900 (x y : ℤ) : y^2 ≠ x^3+(-1900) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 30) (b := 170) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m1899 (x y : ℤ) : y^2 ≠ x^3+(-1899) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 13) (b := 64) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 6 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1897 (x y : ℤ) : y^2 ≠ x^3+(-1897) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1893 (x y : ℤ) : y^2 ≠ x^3+(-1893) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 31) (b := 178) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1890 (x y : ℤ) : y^2 ≠ x^3+(-1890) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1885 (x y : ℤ) : y^2 ≠ x^3+(-1885) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1841 (x y : ℤ) : y^2 ≠ x^3+(-1841) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 29) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2329
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2320
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2306
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2297
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2284
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2261
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2242
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2221
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2213
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2201
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2178
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2170
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2157
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2156
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2144
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2121
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2114
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2101
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2089
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2069
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2067
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2033
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2026
#print axioms PerfectPower.MordellDescentAtlas.no_points_m2016
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1970
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1900
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1899
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1897
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1893
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1890
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1885
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1841
