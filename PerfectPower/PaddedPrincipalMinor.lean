import PerfectPower.DeterminantalEvents
noncomputable section
namespace PerfectPower.PaddedPrincipalMinor
open Matrix
variable {e : Type*} [Fintype e] [DecidableEq e]
variable {R : Type*} [CommRing R]

def principal (K : Matrix e e R) (S : Finset e) : Matrix S S R :=
  K.submatrix Subtype.val Subtype.val

/-- Identity padding has exactly the determinant of the principal submatrix. -/
theorem padded_det (K : Matrix e e R) (S : Finset e) :
    det (DeterminantalEvents.padded K S)=det (principal K S) := by
  classical
  let eqv := Equiv.Set.sumCompl (S : Set e)
  let A := DeterminantalEvents.padded K S
  have he : A.submatrix eqv eqv =
      fromBlocks (principal K S)
        (K.submatrix (fun i : {i : e // i ∈ S} => i.val)
          (fun j : {j : e // j ∈ (S : Set e)ᶜ} => j.val)) 0 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change (if i.val ∈ S then K i.val else (1 : Matrix e e R) i.val) j.val = K i.val j.val
        have hi : i.val ∈ S := Finset.mem_coe.mp i.property
        rw [if_pos hi]
      | inr j =>
        change (if i.val ∈ S then K i.val else (1 : Matrix e e R) i.val) j.val = K i.val j.val
        have hi : i.val ∈ S := Finset.mem_coe.mp i.property
        rw [if_pos hi]
    | inr i =>
      cases j with
      | inl j =>
        have hne : i.val ≠ j.val := by
          intro h
          exact i.property (h ▸ j.property)
        change (if i.val ∈ S then K i.val else (1 : Matrix e e R) i.val) j.val = 0
        have hi : i.val ∉ S := fun h => i.property (Finset.mem_coe.mpr h)
        rw [if_neg hi]
        simp [one_apply,hne]
      | inr j =>
        change (if i.val ∈ S then K i.val else (1 : Matrix e e R) i.val) j.val =
          (1 : Matrix {j : e // j ∈ (S : Set e)ᶜ} {j : e // j ∈ (S : Set e)ᶜ} R) i j
        have hi : i.val ∉ S := fun h => i.property (Finset.mem_coe.mpr h)
        rw [if_neg hi]
        simp [one_apply,Subtype.ext_iff]
  change det A = det (principal K S)
  rw [← det_submatrix_equiv_self eqv A,he,det_fromBlocks_zero₂₁,det_one,mul_one]

def shifted (K : Matrix e e R) (J : Finset e) : Matrix e e R :=
  K - diagonal (fun i => if i ∈ J then 1 else 0)

/-- The finite-submatrix determinant used by the event implementation equals the padded formula. -/
theorem mixed_principal (K : Matrix e e R) (I J : Finset e) :
    DeterminantalEvents.mixed K I J =
      (-1 : R)^J.card * det (principal (shifted K J) (I ∪ J)) := by
  have he : J.piecewise
      (DeterminantalEvents.padded K (I ∪ J) - (1 : Matrix e e R))
      (DeterminantalEvents.padded K (I ∪ J)) =
        DeterminantalEvents.padded (shifted K J) (I ∪ J) := by
    ext i j
    by_cases hj : i ∈ J
    · have hu : i ∈ I ∪ J := Finset.mem_union_right I hj
      simp [DeterminantalEvents.padded,shifted,Finset.piecewise,hj,hu,one_apply,diagonal_apply]
    · by_cases hu : i ∈ I ∪ J <;>
        simp [DeterminantalEvents.padded,shifted,Finset.piecewise,hj,hu,one_apply,diagonal_apply]
  unfold DeterminantalEvents.mixed
  rw [he,padded_det]

end PerfectPower.PaddedPrincipalMinor
