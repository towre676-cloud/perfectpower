import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m189 (x y : ℤ) : y^2 ≠ x^3+(-189) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m178 (x y : ℤ) : y^2 ≠ x^3+(-178) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 4) (b := 11) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m177 (x y : ℤ) : y^2 ≠ x^3+(-177) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 13) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m162 (x y : ℤ) : y^2 ≠ x^3+(-162) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 36) (b := 153) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 153) (u := 41) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m161 (x y : ℤ) : y^2 ≠ x^3+(-161) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 2) (b := 13) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m160 (x y : ℤ) : y^2 ≠ x^3+(-160) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 28) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m154 (x y : ℤ) : y^2 ≠ x^3+(-154) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 2) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m144 (x y : ℤ) : y^2 ≠ x^3+(-144) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 14) (b := 38) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 19) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m141 (x y : ℤ) : y^2 ≠ x^3+(-141) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m131 (x y : ℤ) : y^2 ≠ x^3+(-131) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 5) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m129 (x y : ℤ) : y^2 ≠ x^3+(-129) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m108 (x y : ℤ) : y^2 ≠ x^3+(-108) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m101 (x y : ℤ) : y^2 ≠ x^3+(-101) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m99 (x y : ℤ) : y^2 ≠ x^3+(-99) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 1) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m98 (x y : ℤ) : y^2 ≠ x^3+(-98) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 4) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m96 (x y : ℤ) : y^2 ≠ x^3+(-96) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m91 (x y : ℤ) : y^2 ≠ x^3+(-91) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -3) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m82 (x y : ℤ) : y^2 ≠ x^3+(-82) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m80 (x y : ℤ) : y^2 ≠ x^3+(-80) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -2) (b := 6) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m73 (x y : ℤ) : y^2 ≠ x^3+(-73) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m66 (x y : ℤ) : y^2 ≠ x^3+(-66) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m65 (x y : ℤ) : y^2 ≠ x^3+(-65) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m62 (x y : ℤ) : y^2 ≠ x^3+(-62) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m57 (x y : ℤ) : y^2 ≠ x^3+(-57) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m43 (x y : ℤ) : y^2 ≠ x^3+(-43) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -3) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m37 (x y : ℤ) : y^2 ≠ x^3+(-37) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m33 (x y : ℤ) : y^2 ≠ x^3+(-33) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 5) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m32 (x y : ℤ) : y^2 ≠ x^3+(-32) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m17 (x y : ℤ) : y^2 ≠ x^3+(-17) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m16 (x y : ℤ) : y^2 ≠ x^3+(-16) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -2) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m12 (x y : ℤ) : y^2 ≠ x^3+(-12) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m10 (x y : ℤ) : y^2 ≠ x^3+(-10) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 2) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m189
#print axioms PerfectPower.MordellDescentAtlas.no_points_m178
#print axioms PerfectPower.MordellDescentAtlas.no_points_m177
#print axioms PerfectPower.MordellDescentAtlas.no_points_m162
#print axioms PerfectPower.MordellDescentAtlas.no_points_m161
#print axioms PerfectPower.MordellDescentAtlas.no_points_m160
#print axioms PerfectPower.MordellDescentAtlas.no_points_m154
#print axioms PerfectPower.MordellDescentAtlas.no_points_m144
#print axioms PerfectPower.MordellDescentAtlas.no_points_m141
#print axioms PerfectPower.MordellDescentAtlas.no_points_m131
#print axioms PerfectPower.MordellDescentAtlas.no_points_m129
#print axioms PerfectPower.MordellDescentAtlas.no_points_m108
#print axioms PerfectPower.MordellDescentAtlas.no_points_m101
#print axioms PerfectPower.MordellDescentAtlas.no_points_m99
#print axioms PerfectPower.MordellDescentAtlas.no_points_m98
#print axioms PerfectPower.MordellDescentAtlas.no_points_m96
#print axioms PerfectPower.MordellDescentAtlas.no_points_m91
#print axioms PerfectPower.MordellDescentAtlas.no_points_m82
#print axioms PerfectPower.MordellDescentAtlas.no_points_m80
#print axioms PerfectPower.MordellDescentAtlas.no_points_m73
#print axioms PerfectPower.MordellDescentAtlas.no_points_m66
#print axioms PerfectPower.MordellDescentAtlas.no_points_m65
#print axioms PerfectPower.MordellDescentAtlas.no_points_m62
#print axioms PerfectPower.MordellDescentAtlas.no_points_m57
#print axioms PerfectPower.MordellDescentAtlas.no_points_m43
#print axioms PerfectPower.MordellDescentAtlas.no_points_m37
#print axioms PerfectPower.MordellDescentAtlas.no_points_m33
#print axioms PerfectPower.MordellDescentAtlas.no_points_m32
#print axioms PerfectPower.MordellDescentAtlas.no_points_m17
#print axioms PerfectPower.MordellDescentAtlas.no_points_m16
#print axioms PerfectPower.MordellDescentAtlas.no_points_m12
#print axioms PerfectPower.MordellDescentAtlas.no_points_m10
