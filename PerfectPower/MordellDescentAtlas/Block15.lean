import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m1475 (x y : ℤ) : y^2 ≠ x^3+(-1475) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 5) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1465 (x y : ℤ) : y^2 ≠ x^3+(-1465) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1450 (x y : ℤ) : y^2 ≠ x^3+(-1450) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 2) (b := 27) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1414 (x y : ℤ) : y^2 ≠ x^3+(-1414) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -18) (b := 47) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 47) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1405 (x y : ℤ) : y^2 ≠ x^3+(-1405) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1395 (x y : ℤ) : y^2 ≠ x^3+(-1395) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -11) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1394 (x y : ℤ) : y^2 ≠ x^3+(-1394) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 4) (b := 27) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1393 (x y : ℤ) : y^2 ≠ x^3+(-1393) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 85) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 85) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1377 (x y : ℤ) : y^2 ≠ x^3+(-1377) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1376 (x y : ℤ) : y^2 ≠ x^3+(-1376) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 28) (b := 108) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m1373 (x y : ℤ) : y^2 ≠ x^3+(-1373) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1361 (x y : ℤ) : y^2 ≠ x^3+(-1361) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 2) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1347 (x y : ℤ) : y^2 ≠ x^3+(-1347) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -11) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1289 (x y : ℤ) : y^2 ≠ x^3+(-1289) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1281 (x y : ℤ) : y^2 ≠ x^3+(-1281) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1275 (x y : ℤ) : y^2 ≠ x^3+(-1275) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 25) (b := 130) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1260 (x y : ℤ) : y^2 ≠ x^3+(-1260) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 46) (b := 314) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 157) (u := 28) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m1257 (x y : ℤ) : y^2 ≠ x^3+(-1257) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1249 (x y : ℤ) : y^2 ≠ x^3+(-1249) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1248 (x y : ℤ) : y^2 ≠ x^3+(-1248) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 68) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m1242 (x y : ℤ) : y^2 ≠ x^3+(-1242) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 26) (b := 97) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 97) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1233 (x y : ℤ) : y^2 ≠ x^3+(-1233) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 109) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 109) (u := 33) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1211 (x y : ℤ) : y^2 ≠ x^3+(-1211) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 29) (b := 160) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1193 (x y : ℤ) : y^2 ≠ x^3+(-1193) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 26) (b := 137) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 137) (u := 37) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1178 (x y : ℤ) : y^2 ≠ x^3+(-1178) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 33) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 33) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1169 (x y : ℤ) : y^2 ≠ x^3+(-1169) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 13) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1164 (x y : ℤ) : y^2 ≠ x^3+(-1164) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m1157 (x y : ℤ) : y^2 ≠ x^3+(-1157) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1155 (x y : ℤ) : y^2 ≠ x^3+(-1155) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 1) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1153 (x y : ℤ) : y^2 ≠ x^3+(-1153) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 6) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1150 (x y : ℤ) : y^2 ≠ x^3+(-1150) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1149 (x y : ℤ) : y^2 ≠ x^3+(-1149) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1475
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1465
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1450
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1414
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1405
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1395
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1394
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1393
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1377
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1376
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1373
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1361
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1347
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1289
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1281
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1275
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1260
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1257
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1249
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1248
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1242
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1233
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1211
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1193
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1178
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1169
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1164
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1157
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1155
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1153
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1150
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1149
