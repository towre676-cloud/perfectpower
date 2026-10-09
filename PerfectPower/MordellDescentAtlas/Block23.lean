import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p1383 (x y : ℤ) : y^2 ≠ x^3+(1383) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 74) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1392 (x y : ℤ) : y^2 ≠ x^3+(1392) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 10) (b := 14) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1423 (x y : ℤ) : y^2 ≠ x^3+(1423) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 47) (b := 320) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 6 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1440 (x y : ℤ) : y^2 ≠ x^3+(1440) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 12) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1486 (x y : ℤ) : y^2 ≠ x^3+(1486) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 11) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1502 (x y : ℤ) : y^2 ≠ x^3+(1502) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 57) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 57) (u := 13) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1504 (x y : ℤ) : y^2 ≠ x^3+(1504) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 28) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1549 (x y : ℤ) : y^2 ≠ x^3+(1549) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 17) (b := 58) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1566 (x y : ℤ) : y^2 ≠ x^3+(1566) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1588 (x y : ℤ) : y^2 ≠ x^3+(1588) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p1607 (x y : ℤ) : y^2 ≠ x^3+(1607) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 65) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1632 (x y : ℤ) : y^2 ≠ x^3+(1632) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 4) (b := 28) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1634 (x y : ℤ) : y^2 ≠ x^3+(1634) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1696 (x y : ℤ) : y^2 ≠ x^3+(1696) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1710 (x y : ℤ) : y^2 ≠ x^3+(1710) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1726 (x y : ℤ) : y^2 ≠ x^3+(1726) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1727 (x y : ℤ) : y^2 ≠ x^3+(1727) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 42) (b := 269) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 269) (u := 82) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1730 (x y : ℤ) : y^2 ≠ x^3+(1730) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1734 (x y : ℤ) : y^2 ≠ x^3+(1734) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 26) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 40) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1760 (x y : ℤ) : y^2 ≠ x^3+(1760) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1766 (x y : ℤ) : y^2 ≠ x^3+(1766) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 34) (b := 137) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 137) (u := 51) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1775 (x y : ℤ) : y^2 ≠ x^3+(1775) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 15) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1776 (x y : ℤ) : y^2 ≠ x^3+(1776) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 14) (b := 22) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1797 (x y : ℤ) : y^2 ≠ x^3+(1797) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 13) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1826 (x y : ℤ) : y^2 ≠ x^3+(1826) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 7) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1858 (x y : ℤ) : y^2 ≠ x^3+(1858) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -4) (b := 31) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1903 (x y : ℤ) : y^2 ≠ x^3+(1903) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 29) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1914 (x y : ℤ) : y^2 ≠ x^3+(1914) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -2) (b := 31) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1941 (x y : ℤ) : y^2 ≠ x^3+(1941) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 13) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1951 (x y : ℤ) : y^2 ≠ x^3+(1951) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 26) (b := 125) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 125) (u := 57) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p1952 (x y : ℤ) : y^2 ≠ x^3+(1952) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 44) (b := 204) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 51) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p1986 (x y : ℤ) : y^2 ≠ x^3+(1986) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 4) (b := 31) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 31) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1383
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1392
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1423
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1440
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1486
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1502
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1504
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1549
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1566
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1588
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1607
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1632
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1634
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1696
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1710
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1726
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1727
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1730
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1734
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1760
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1766
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1775
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1776
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1797
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1826
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1858
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1903
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1914
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1941
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1951
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1952
#print axioms PerfectPower.MordellDescentAtlas.no_points_p1986
