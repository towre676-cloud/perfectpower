import PerfectPower.MordellDescentMask

set_option maxRecDepth 4096
namespace PerfectPower.MordellDescentAtlas

theorem no_points_p5443 (x y : ℤ) : y^2 ≠ x^3+(5443) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 82) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 41) (u := 9) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5495 (x y : ℤ) : y^2 ≠ x^3+(5495) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 39) (b := 232) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5523 (x y : ℤ) : y^2 ≠ x^3+(5523) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 43) (b := 272) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5543 (x y : ℤ) : y^2 ≠ x^3+(5543) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 17) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5590 (x y : ℤ) : y^2 ≠ x^3+(5590) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 11) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 11) (u := 3) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5663 (x y : ℤ) : y^2 ≠ x^3+(5663) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 13) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5670 (x y : ℤ) : y^2 ≠ x^3+(5670) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 9) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 9) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5684 (x y : ℤ) : y^2 ≠ x^3+(5684) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 30) (b := 146) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 32) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 32 PerfectPower.MordellDescentMask.mask32 PerfectPower.MordellDescentMask.square32 (by decide +kernel)) x y
  exact h

theorem no_points_p5695 (x y : ℤ) : y^2 ≠ x^3+(5695) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 26) (b := 109) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 109) (u := 33) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5703 (x y : ℤ) : y^2 ≠ x^3+(5703) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 34) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5709 (x y : ℤ) : y^2 ≠ x^3+(5709) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 37) (b := 212) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 53) (u := 23) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5744 (x y : ℤ) : y^2 ≠ x^3+(5744) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 46) (b := 214) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 107) (u := 31) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p5767 (x y : ℤ) : y^2 ≠ x^3+(5767) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 23) (b := 80) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 4 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5807 (x y : ℤ) : y^2 ≠ x^3+(5807) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 5) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 5) (u := 2) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5814 (x y : ℤ) : y^2 ≠ x^3+(5814) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 3) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 3) (u := 1) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5822 (x y : ℤ) : y^2 ≠ x^3+(5822) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 20) (b := 33) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 33) (u := 8) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5830 (x y : ℤ) : y^2 ≠ x^3+(5830) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 18) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5831 (x y : ℤ) : y^2 ≠ x^3+(5831) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 18) (b := 1) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5835 (x y : ℤ) : y^2 ≠ x^3+(5835) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 32) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 5 (b₁ := 1) (u := 0) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5861 (x y : ℤ) : y^2 ≠ x^3+(5861) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 45) (b := 292) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 73) (u := 27) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5893 (x y : ℤ) : y^2 ≠ x^3+(5893) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 29) (b := 136) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 3 (b₁ := 17) (u := 4) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p5975 (x y : ℤ) : y^2 ≠ x^3+(5975) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 30) (b := 145) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 145) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6022 (x y : ℤ) : y^2 ≠ x^3+(6022) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 34) (b := 129) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 129) (u := 16) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6031 (x y : ℤ) : y^2 ≠ x^3+(6031) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 38) (b := 221) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 221) (u := 21) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6106 (x y : ℤ) : y^2 ≠ x^3+(6106) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 14) (b := 41) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 41) (u := 17) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6110 (x y : ℤ) : y^2 ≠ x^3+(6110) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 28) (b := 89) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 89) (u := 40) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6146 (x y : ℤ) : y^2 ≠ x^3+(6146) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := 12) (b := 47) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 47) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6183 (x y : ℤ) : y^2 ≠ x^3+(6183) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 19) (b := 26) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 13) (u := 5) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6192 (x y : ℤ) : y^2 ≠ x^3+(6192) := by
  have h := PerfectPower.MordellDescent.no_points (D := 2) (c := 30) (b := 102) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 1 (b₁ := 51) (u := 7) (by decide +kernel) (by decide +kernel))
    (M := 64) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 64 PerfectPower.MordellDescentMask.mask64 PerfectPower.MordellDescentMask.square64 (by decide +kernel)) x y
  exact h

theorem no_points_p6227 (x y : ℤ) : y^2 ≠ x^3+(6227) := by
  have h := PerfectPower.MordellDescent.no_points (D := 1) (c := 27) (b := 116) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 2 (b₁ := 29) (u := 12) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6298 (x y : ℤ) : y^2 ≠ x^3+(6298) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -34) (b := 151) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 151) (u := 46) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

theorem no_points_p6370 (x y : ℤ) : y^2 ≠ x^3+(6370) := by
  have h := PerfectPower.MordellDescent.no_points (D := -2) (c := -28) (b := 119) (by decide +kernel)
    (PerfectPower.MordellDescent.goodDivisors_of_cert (by decide +kernel) 0 (b₁ := 119) (u := 11) (by decide +kernel) (by decide +kernel))
    (M := 8) (by decide +kernel) (by decide +kernel)
    (PerfectPower.MordellDescentMask.congr_ok _ _ _ 8 PerfectPower.MordellDescentMask.mask8 PerfectPower.MordellDescentMask.square8 (by decide +kernel)) x y
  exact h

end PerfectPower.MordellDescentAtlas
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5443
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5495
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5523
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5543
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5590
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5663
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5670
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5684
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5695
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5703
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5709
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5744
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5767
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5807
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5814
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5822
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5830
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5831
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5835
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5861
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5893
#print axioms PerfectPower.MordellDescentAtlas.no_points_p5975
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6022
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6031
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6106
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6110
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6146
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6183
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6192
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6227
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6298
#print axioms PerfectPower.MordellDescentAtlas.no_points_p6370
