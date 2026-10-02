import PerfectPower.NormRepProof

/-!
# Residue certificates in slices

`NormRepProof.resRepB` checks all `m³` residues in one kernel evaluation; for `m = 49` (`117,649`
residues) that runs out of memory.  `resSliceB … a` checks the residues with first coordinate `a`,
and `resRepB_of_slices` assembles the `m` slices into the original certificate, so the consumer
(`NormRepProof.normRep_of_res`) is unchanged.
-/

namespace PerfectPower.NormRepSlices

open PerfectPower UnitBox UnitPremises NormRepProof

/-- The residues `(a, b, c)` with the first coordinate `a` fixed. -/
def resSliceB (P Q N : ℤ) (m : ℕ) (reps : List Z3) (a : ℕ) : Bool :=
  (List.range m).all fun b => (List.range m).all fun c =>
    decide (nrm P Q ((a : ℤ), (b : ℤ), (c : ℤ)) % m ≠ N % m) || reps.any fun γ =>
      decide ((mul P Q ((a : ℤ), (b : ℤ), (c : ℤ)) (adj P Q γ)).1 % nrm P Q γ = 0 ∧
        (mul P Q ((a : ℤ), (b : ℤ), (c : ℤ)) (adj P Q γ)).2.1 % nrm P Q γ = 0 ∧
        (mul P Q ((a : ℤ), (b : ℤ), (c : ℤ)) (adj P Q γ)).2.2 % nrm P Q γ = 0)

/-- The header of the certificate: `m > 0`, `N ∣ m`, and the norms of the representatives. -/
def resHeadB (P Q N : ℤ) (m : ℕ) (reps : List Z3) : Bool :=
  decide (0 < m) && decide ((m : ℤ) % N = 0) &&
  reps.all (fun γ => decide (nrm P Q γ = N ∨ nrm P Q γ = -N))

/-- **The slices make the certificate.** -/
theorem resRepB_of_slices {P Q N : ℤ} {m : ℕ} {reps : List Z3} (hh : resHeadB P Q N m reps = true)
    (hs : ∀ a : ℕ, a < m → resSliceB P Q N m reps a = true) : resRepB P Q N m reps = true := by
  simp only [resHeadB, Bool.and_eq_true] at hh
  simp only [resRepB, Bool.and_eq_true, hh, true_and, List.all_eq_true, List.mem_range]
  exact fun a ha => by simpa [resSliceB, List.all_eq_true] using hs a ha

end PerfectPower.NormRepSlices
