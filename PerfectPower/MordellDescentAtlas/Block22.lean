import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p794 (x y : ℤ) : y^2 ≠ x^3+(794) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 6) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p831 (x y : ℤ) : y^2 ≠ x^3+(831) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 13) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p838 (x y : ℤ) : y^2 ≠ x^3+(838) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p875 (x y : ℤ) : y^2 ≠ x^3+(875) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p891 (x y : ℤ) : y^2 ≠ x^3+(891) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 31) (b := 170) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p922 (x y : ℤ) : y^2 ≠ x^3+(922) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -10) (b := 31) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p931 (x y : ℤ) : y^2 ≠ x^3+(931) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p975 (x y : ℤ) : y^2 ≠ x^3+(975) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 5) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p982 (x y : ℤ) : y^2 ≠ x^3+(982) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p994 (x y : ℤ) : y^2 ≠ x^3+(994) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 23) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p998 (x y : ℤ) : y^2 ≠ x^3+(998) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p999 (x y : ℤ) : y^2 ≠ x^3+(999) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1006 (x y : ℤ) : y^2 ≠ x^3+(1006) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 19) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 19) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1008 (x y : ℤ) : y^2 ≠ x^3+(1008) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 30) (b := 114) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 57) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1038 (x y : ℤ) : y^2 ≠ x^3+(1038) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 59) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 59) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1050 (x y : ℤ) : y^2 ≠ x^3+(1050) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -2) (b := 23) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1063 (x y : ℤ) : y^2 ≠ x^3+(1063) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1075 (x y : ℤ) : y^2 ≠ x^3+(1075) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1122 (x y : ℤ) : y^2 ≠ x^3+(1122) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 4) (b := 23) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1150 (x y : ℤ) : y^2 ≠ x^3+(1150) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1173 (x y : ℤ) : y^2 ≠ x^3+(1173) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 13) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1187 (x y : ℤ) : y^2 ≠ x^3+(1187) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 136) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1231 (x y : ℤ) : y^2 ≠ x^3+(1231) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1239 (x y : ℤ) : y^2 ≠ x^3+(1239) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1242 (x y : ℤ) : y^2 ≠ x^3+(1242) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -26) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 14) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1248 (x y : ℤ) : y^2 ≠ x^3+(1248) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -20) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1267 (x y : ℤ) : y^2 ≠ x^3+(1267) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1274 (x y : ℤ) : y^2 ≠ x^3+(1274) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 6) (b := 23) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 23) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1315 (x y : ℤ) : y^2 ≠ x^3+(1315) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1327 (x y : ℤ) : y^2 ≠ x^3+(1327) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1351 (x y : ℤ) : y^2 ≠ x^3+(1351) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 104) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1375 (x y : ℤ) : y^2 ≠ x^3+(1375) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p794
#print axioms PerfectPower.MordellDescentAtlas.no_points_p831
#print axioms PerfectPower.MordellDescentAtlas.no_points_p838
#print axioms PerfectPower.MordellDescentAtlas.no_points_p875
#print axioms PerfectPower.MordellDescentAtlas.no_points_p891
#print axioms PerfectPower.MordellDescentAtlas.no_points_p922
#print axioms PerfectPower.MordellDescentAtlas.no_points_p931
#print axioms PerfectPower.MordellDescentAtlas.no_points_p975
#print axioms PerfectPower.MordellDescentAtlas.no_points_p982
#print axioms PerfectPower.MordellDescentAtlas.no_points_p994
#print axioms PerfectPower.MordellDescentAtlas.no_points_p998
#print axioms PerfectPower.MordellDescentAtlas.no_points_p999
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1006
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1008
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1038
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1050
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1063
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1075
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1122
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1150
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1173
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1187
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1231
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1239
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1242
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1248
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1267
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1274
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1315
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1327
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1351
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1375
