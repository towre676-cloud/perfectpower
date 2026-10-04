import PerfectPower.AffinePowerComposition
import PerfectPower.Generated.QuarticPowerRegistry
namespace PerfectPower.AffineQuarticAtlas
open QuarticPowerAtlas

/-- Every registered curve has complete enumeration after any nondegenerate integral affine power substitution. -/
theorem complete (C : Case) (hc : C ∈ Generated.QuarticPowerRegistry.cases)
    (q : ℕ) (hq : q ≠ 0) (a b : ℤ) (ha : a ≠ 0) (x y : ℤ) :
    y^2=value C ((a*x+b)^q) ↔
      (x,y) ∈ AffinePowerComposition.lift (outer C) q a b 1 := by
  have hv : valid C := of_decide_eq_true
    ((List.all_eq_true.mp Generated.QuarticPowerRegistry.all_valid) C hc)
  exact AffinePowerComposition.complete (fun x => value C ((a*x+b)^q)) (value C)
    (outer C) q 2 a b 1 hq ha (by norm_num) (by intro x;simp)
    (outer_complete C hv) x y

end PerfectPower.AffineQuarticAtlas
