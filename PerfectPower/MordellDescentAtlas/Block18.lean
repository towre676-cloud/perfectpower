import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m450 (x y : ℤ) : y^2 ≠ x^3+(-450) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 33) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 33) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m443 (x y : ℤ) : y^2 ≠ x^3+(-443) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -7) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m427 (x y : ℤ) : y^2 ≠ x^3+(-427) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -3) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m422 (x y : ℤ) : y^2 ≠ x^3+(-422) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -10) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m410 (x y : ℤ) : y^2 ≠ x^3+(-410) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 42) (b := 193) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 193) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m409 (x y : ℤ) : y^2 ≠ x^3+(-409) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 25) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m401 (x y : ℤ) : y^2 ≠ x^3+(-401) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m389 (x y : ℤ) : y^2 ≠ x^3+(-389) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 35) (b := 208) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m385 (x y : ℤ) : y^2 ≠ x^3+(-385) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 13) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m381 (x y : ℤ) : y^2 ≠ x^3+(-381) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m378 (x y : ℤ) : y^2 ≠ x^3+(-378) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -6) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m373 (x y : ℤ) : y^2 ≠ x^3+(-373) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m369 (x y : ℤ) : y^2 ≠ x^3+(-369) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m352 (x y : ℤ) : y^2 ≠ x^3+(-352) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 12) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m347 (x y : ℤ) : y^2 ≠ x^3+(-347) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -7) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m333 (x y : ℤ) : y^2 ≠ x^3+(-333) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m306 (x y : ℤ) : y^2 ≠ x^3+(-306) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 11) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m297 (x y : ℤ) : y^2 ≠ x^3+(-297) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m283 (x y : ℤ) : y^2 ≠ x^3+(-283) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -3) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m281 (x y : ℤ) : y^2 ≠ x^3+(-281) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 2) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m275 (x y : ℤ) : y^2 ≠ x^3+(-275) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 5) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m269 (x y : ℤ) : y^2 ≠ x^3+(-269) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m257 (x y : ℤ) : y^2 ≠ x^3+(-257) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m241 (x y : ℤ) : y^2 ≠ x^3+(-241) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 5) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m234 (x y : ℤ) : y^2 ≠ x^3+(-234) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -6) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m229 (x y : ℤ) : y^2 ≠ x^3+(-229) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m226 (x y : ℤ) : y^2 ≠ x^3+(-226) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m225 (x y : ℤ) : y^2 ≠ x^3+(-225) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m224 (x y : ℤ) : y^2 ≠ x^3+(-224) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 4) (b := 12) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m218 (x y : ℤ) : y^2 ≠ x^3+(-218) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -6) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m217 (x y : ℤ) : y^2 ≠ x^3+(-217) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m208 (x y : ℤ) : y^2 ≠ x^3+(-208) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -6) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m450
#print axioms PerfectPower.MordellDescentAtlas.no_points_m443
#print axioms PerfectPower.MordellDescentAtlas.no_points_m427
#print axioms PerfectPower.MordellDescentAtlas.no_points_m422
#print axioms PerfectPower.MordellDescentAtlas.no_points_m410
#print axioms PerfectPower.MordellDescentAtlas.no_points_m409
#print axioms PerfectPower.MordellDescentAtlas.no_points_m401
#print axioms PerfectPower.MordellDescentAtlas.no_points_m389
#print axioms PerfectPower.MordellDescentAtlas.no_points_m385
#print axioms PerfectPower.MordellDescentAtlas.no_points_m381
#print axioms PerfectPower.MordellDescentAtlas.no_points_m378
#print axioms PerfectPower.MordellDescentAtlas.no_points_m373
#print axioms PerfectPower.MordellDescentAtlas.no_points_m369
#print axioms PerfectPower.MordellDescentAtlas.no_points_m352
#print axioms PerfectPower.MordellDescentAtlas.no_points_m347
#print axioms PerfectPower.MordellDescentAtlas.no_points_m333
#print axioms PerfectPower.MordellDescentAtlas.no_points_m306
#print axioms PerfectPower.MordellDescentAtlas.no_points_m297
#print axioms PerfectPower.MordellDescentAtlas.no_points_m283
#print axioms PerfectPower.MordellDescentAtlas.no_points_m281
#print axioms PerfectPower.MordellDescentAtlas.no_points_m275
#print axioms PerfectPower.MordellDescentAtlas.no_points_m269
#print axioms PerfectPower.MordellDescentAtlas.no_points_m257
#print axioms PerfectPower.MordellDescentAtlas.no_points_m241
#print axioms PerfectPower.MordellDescentAtlas.no_points_m234
#print axioms PerfectPower.MordellDescentAtlas.no_points_m229
#print axioms PerfectPower.MordellDescentAtlas.no_points_m226
#print axioms PerfectPower.MordellDescentAtlas.no_points_m225
#print axioms PerfectPower.MordellDescentAtlas.no_points_m224
#print axioms PerfectPower.MordellDescentAtlas.no_points_m218
#print axioms PerfectPower.MordellDescentAtlas.no_points_m217
#print axioms PerfectPower.MordellDescentAtlas.no_points_m208
