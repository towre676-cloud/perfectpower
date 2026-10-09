import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p243 (x y : ℤ) : y^2 ≠ x^3+(243) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p244 (x y : ℤ) : y^2 ≠ x^3+(244) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p270 (x y : ℤ) : y^2 ≠ x^3+(270) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 27) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p278 (x y : ℤ) : y^2 ≠ x^3+(278) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 19) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 19) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p279 (x y : ℤ) : y^2 ≠ x^3+(279) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 8) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p307 (x y : ℤ) : y^2 ≠ x^3+(307) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p314 (x y : ℤ) : y^2 ≠ x^3+(314) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 6) (b := 7) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p327 (x y : ℤ) : y^2 ≠ x^3+(327) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p339 (x y : ℤ) : y^2 ≠ x^3+(339) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 7) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p375 (x y : ℤ) : y^2 ≠ x^3+(375) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 25) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p391 (x y : ℤ) : y^2 ≠ x^3+(391) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 50) (b := 353) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 353) (u := 42) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p410 (x y : ℤ) : y^2 ≠ x^3+(410) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -42) (b := 193) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 193) (u := 52) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p422 (x y : ℤ) : y^2 ≠ x^3+(422) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p432 (x y : ℤ) : y^2 ≠ x^3+(432) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 14) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p447 (x y : ℤ) : y^2 ≠ x^3+(447) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 22) (b := 101) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 101) (u := 10) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p459 (x y : ℤ) : y^2 ≠ x^3+(459) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p495 (x y : ℤ) : y^2 ≠ x^3+(495) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 34) (b := 197) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 197) (u := 14) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p503 (x y : ℤ) : y^2 ≠ x^3+(503) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 73) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p514 (x y : ℤ) : y^2 ≠ x^3+(514) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p570 (x y : ℤ) : y^2 ≠ x^3+(570) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -2) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p583 (x y : ℤ) : y^2 ≠ x^3+(583) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 38) (b := 233) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 233) (u := 89) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p597 (x y : ℤ) : y^2 ≠ x^3+(597) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 13) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p629 (x y : ℤ) : y^2 ≠ x^3+(629) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 9) (b := 10) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p630 (x y : ℤ) : y^2 ≠ x^3+(630) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 51) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 51) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p642 (x y : ℤ) : y^2 ≠ x^3+(642) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 4) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p655 (x y : ℤ) : y^2 ≠ x^3+(655) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 11) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p662 (x y : ℤ) : y^2 ≠ x^3+(662) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 34) (b := 139) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 139) (u := 50) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p671 (x y : ℤ) : y^2 ≠ x^3+(671) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 52) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p711 (x y : ℤ) : y^2 ≠ x^3+(711) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p725 (x y : ℤ) : y^2 ≠ x^3+(725) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 9) (b := 2) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p741 (x y : ℤ) : y^2 ≠ x^3+(741) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 25) (b := 122) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 61) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p758 (x y : ℤ) : y^2 ≠ x^3+(758) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 10) (b := 11) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p243
#print axioms PerfectPower.MordellDescentAtlas.no_points_p244
#print axioms PerfectPower.MordellDescentAtlas.no_points_p270
#print axioms PerfectPower.MordellDescentAtlas.no_points_p278
#print axioms PerfectPower.MordellDescentAtlas.no_points_p279
#print axioms PerfectPower.MordellDescentAtlas.no_points_p307
#print axioms PerfectPower.MordellDescentAtlas.no_points_p314
#print axioms PerfectPower.MordellDescentAtlas.no_points_p327
#print axioms PerfectPower.MordellDescentAtlas.no_points_p339
#print axioms PerfectPower.MordellDescentAtlas.no_points_p375
#print axioms PerfectPower.MordellDescentAtlas.no_points_p391
#print axioms PerfectPower.MordellDescentAtlas.no_points_p410
#print axioms PerfectPower.MordellDescentAtlas.no_points_p422
#print axioms PerfectPower.MordellDescentAtlas.no_points_p432
#print axioms PerfectPower.MordellDescentAtlas.no_points_p447
#print axioms PerfectPower.MordellDescentAtlas.no_points_p459
#print axioms PerfectPower.MordellDescentAtlas.no_points_p495
#print axioms PerfectPower.MordellDescentAtlas.no_points_p503
#print axioms PerfectPower.MordellDescentAtlas.no_points_p514
#print axioms PerfectPower.MordellDescentAtlas.no_points_p570
#print axioms PerfectPower.MordellDescentAtlas.no_points_p583
#print axioms PerfectPower.MordellDescentAtlas.no_points_p597
#print axioms PerfectPower.MordellDescentAtlas.no_points_p629
#print axioms PerfectPower.MordellDescentAtlas.no_points_p630
#print axioms PerfectPower.MordellDescentAtlas.no_points_p642
#print axioms PerfectPower.MordellDescentAtlas.no_points_p655
#print axioms PerfectPower.MordellDescentAtlas.no_points_p662
#print axioms PerfectPower.MordellDescentAtlas.no_points_p671
#print axioms PerfectPower.MordellDescentAtlas.no_points_p711
#print axioms PerfectPower.MordellDescentAtlas.no_points_p725
#print axioms PerfectPower.MordellDescentAtlas.no_points_p741
#print axioms PerfectPower.MordellDescentAtlas.no_points_p758
