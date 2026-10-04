import PerfectPower.IntegralPullback
import PerfectPower.CoveringMaps
import PerfectPower.TargetDecoder

#print axioms PerfectPower.IntegralPullback.pullback
#print axioms PerfectPower.IntegralPullback.image_iff
#print axioms PerfectPower.IntegralPullback.orbit_residue_iff
#print axioms PerfectPower.CoveringMaps.covering
#print axioms PerfectPower.CoveringMaps.isogeny
#print axioms PerfectPower.TargetDecoder.decoder_iff
#print axioms PerfectPower.TargetDecoder.separation_iff
#print axioms PerfectPower.TargetDecoder.collision_no_decoder

example : PerfectPower.CoveringMaps.curve (-1) 1 1 1 := by norm_num [PerfectPower.CoveringMaps.curve]
example : PerfectPower.CoveringMaps.curve 2 (-3) 1 0 := by norm_num [PerfectPower.CoveringMaps.curve]
example : ¬ ∃ d : ℕ → ℕ, ∀ s : ℕ, d (s % 2)=s := by
  apply PerfectPower.TargetDecoder.collision_no_decoder (fun s : ℕ => s%2) id 0 2
  · decide
  · decide

open Matrix

-- Preserve the index-three image restriction; the rational inverse alone is insufficient.
def indexThree : Matrix (Fin 3) (Fin 3) ℤ := Matrix.diagonal ![3,1,1]
example : indexThree.det ≠ 0 := by decide
example : ¬ (∀ i, indexThree.det ∣ (indexThree.adjugate *ᵥ ![1,0,0]) i) := by decide
example : ∀ i, indexThree.det ∣ (indexThree.adjugate *ᵥ ![3,0,0]) i := by decide
example : ¬ ∃ x : Fin 3 → ℤ, indexThree *ᵥ x = ![1,0,0] := by
  rw [PerfectPower.IntegralPullback.image_iff indexThree (by decide)]
  decide
