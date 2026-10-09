import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m7845 (x y : ℤ) : y^2 ≠ x^3+(-7845) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 31) (b := 194) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 97) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7842 (x y : ℤ) : y^2 ≠ x^3+(-7842) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 40) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7803 (x y : ℤ) : y^2 ≠ x^3+(-7803) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 13) (b := 100) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7731 (x y : ℤ) : y^2 ≠ x^3+(-7731) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -11) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7724 (x y : ℤ) : y^2 ≠ x^3+(-7724) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m7705 (x y : ℤ) : y^2 ≠ x^3+(-7705) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 34) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7673 (x y : ℤ) : y^2 ≠ x^3+(-7673) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -13) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7628 (x y : ℤ) : y^2 ≠ x^3+(-7628) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 38) (b := 250) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 125) (u := 57) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m7617 (x y : ℤ) : y^2 ≠ x^3+(-7617) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -17) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7520 (x y : ℤ) : y^2 ≠ x^3+(-7520) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m7514 (x y : ℤ) : y^2 ≠ x^3+(-7514) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 34) (b := 153) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 153) (u := 41) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7513 (x y : ℤ) : y^2 ≠ x^3+(-7513) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7494 (x y : ℤ) : y^2 ≠ x^3+(-7494) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -26) (b := 71) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 71) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7457 (x y : ℤ) : y^2 ≠ x^3+(-7457) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 101) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 101) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7453 (x y : ℤ) : y^2 ≠ x^3+(-7453) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7441 (x y : ℤ) : y^2 ≠ x^3+(-7441) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7422 (x y : ℤ) : y^2 ≠ x^3+(-7422) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7413 (x y : ℤ) : y^2 ≠ x^3+(-7413) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -17) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7330 (x y : ℤ) : y^2 ≠ x^3+(-7330) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 28) (b := 121) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 121) (u := 19) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7290 (x y : ℤ) : y^2 ≠ x^3+(-7290) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 81) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 81) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7259 (x y : ℤ) : y^2 ≠ x^3+(-7259) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -19) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7250 (x y : ℤ) : y^2 ≠ x^3+(-7250) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 67) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 67) (u := 20) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7233 (x y : ℤ) : y^2 ≠ x^3+(-7233) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7225 (x y : ℤ) : y^2 ≠ x^3+(-7225) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 30) (b := 185) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 185) (u := 43) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7217 (x y : ℤ) : y^2 ≠ x^3+(-7217) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 2) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7213 (x y : ℤ) : y^2 ≠ x^3+(-7213) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 164) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7201 (x y : ℤ) : y^2 ≠ x^3+(-7201) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -18) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7178 (x y : ℤ) : y^2 ≠ x^3+(-7178) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -6) (b := 59) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 59) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7136 (x y : ℤ) : y^2 ≠ x^3+(-7136) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 36) (b := 164) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 41) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m7129 (x y : ℤ) : y^2 ≠ x^3+(-7129) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7123 (x y : ℤ) : y^2 ≠ x^3+(-7123) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 128) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 7 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m7115 (x y : ℤ) : y^2 ≠ x^3+(-7115) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -19) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7845
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7842
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7803
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7731
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7724
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7705
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7673
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7628
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7617
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7520
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7514
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7513
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7494
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7457
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7453
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7441
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7422
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7413
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7330
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7290
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7259
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7250
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7233
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7225
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7217
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7213
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7201
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7178
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7136
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7129
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7123
#print axioms PerfectPower.MordellDescentAtlas.no_points_m7115
