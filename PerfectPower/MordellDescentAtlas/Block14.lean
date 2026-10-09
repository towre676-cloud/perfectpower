import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_m1811 (x y : ℤ) : y^2 ≠ x^3+(-1811) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 17) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1809 (x y : ℤ) : y^2 ≠ x^3+(-1809) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 10) (b := 53) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1771 (x y : ℤ) : y^2 ≠ x^3+(-1771) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 9) (b := 50) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1766 (x y : ℤ) : y^2 ≠ x^3+(-1766) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -34) (b := 137) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 137) (u := 31) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1760 (x y : ℤ) : y^2 ≠ x^3+(-1760) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m1753 (x y : ℤ) : y^2 ≠ x^3+(-1753) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -9) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1746 (x y : ℤ) : y^2 ≠ x^3+(-1746) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1734 (x y : ℤ) : y^2 ≠ x^3+(-1734) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -26) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 25) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1731 (x y : ℤ) : y^2 ≠ x^3+(-1731) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -11) (b := 20) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1730 (x y : ℤ) : y^2 ≠ x^3+(-1730) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -12) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1726 (x y : ℤ) : y^2 ≠ x^3+(-1726) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1725 (x y : ℤ) : y^2 ≠ x^3+(-1725) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -5) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1699 (x y : ℤ) : y^2 ≠ x^3+(-1699) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 33) (b := 194) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 97) (u := 22) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1696 (x y : ℤ) : y^2 ≠ x^3+(-1696) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 4) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_m1689 (x y : ℤ) : y^2 ≠ x^3+(-1689) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -2) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1676 (x y : ℤ) : y^2 ≠ x^3+(-1676) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_m1674 (x y : ℤ) : y^2 ≠ x^3+(-1674) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -6) (b := 27) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1673 (x y : ℤ) : y^2 ≠ x^3+(-1673) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 2) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1634 (x y : ℤ) : y^2 ≠ x^3+(-1634) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 12) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1633 (x y : ℤ) : y^2 ≠ x^3+(-1633) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 146) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1630 (x y : ℤ) : y^2 ≠ x^3+(-1630) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -12) (b := 7) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 7) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1627 (x y : ℤ) : y^2 ≠ x^3+(-1627) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -3) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1625 (x y : ℤ) : y^2 ≠ x^3+(-1625) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -10) (b := 25) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 25) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1601 (x y : ℤ) : y^2 ≠ x^3+(-1601) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -1) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1587 (x y : ℤ) : y^2 ≠ x^3+(-1587) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -11) (b := 16) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1585 (x y : ℤ) : y^2 ≠ x^3+(-1585) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -6) (b := 37) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 37) (u := 6) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1573 (x y : ℤ) : y^2 ≠ x^3+(-1573) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 3) (b := 40) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1561 (x y : ℤ) : y^2 ≠ x^3+(-1561) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 30) (b := 169) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 169) (u := 70) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1555 (x y : ℤ) : y^2 ≠ x^3+(-1555) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 21) (b := 104) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1522 (x y : ℤ) : y^2 ≠ x^3+(-1522) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := -4) (b := 27) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 27) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1499 (x y : ℤ) : y^2 ≠ x^3+(-1499) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := -7) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_m1481 (x y : ℤ) : y^2 ≠ x^3+(-1481) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 14) (b := 65) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 65) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1811
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1809
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1771
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1766
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1760
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1753
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1746
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1734
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1731
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1730
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1726
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1725
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1699
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1696
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1689
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1676
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1674
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1673
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1634
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1633
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1630
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1627
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1625
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1601
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1587
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1585
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1573
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1561
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1555
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1522
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1499
#print axioms PerfectPower.MordellDescentAtlas.no_points_m1481
