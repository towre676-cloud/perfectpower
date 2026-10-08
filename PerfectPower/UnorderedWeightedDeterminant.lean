import PerfectPower.ResidueDeterminantCertificate

namespace PerfectPower.UnorderedWeightedDeterminant
open Matrix
open scoped BigOperators

variable {ι τ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]
  [DecidableEq τ] [CommRing R]

/-- Unordered selections of the local vector labels. -/
noncomputable def selections : Finset (ι → τ) :=
  Finset.univ.filter Function.Injective

noncomputable def labels (r : ι → τ) : Finset τ := Finset.univ.image r

/-- The alternating coefficient of one unordered label set.
Any chosen ordering turns this into the product of the coefficient minor
and the local-vector minor; no ordering is part of this definition. -/
noncomputable def coefficient (c : ι → τ → R) (v : τ → ι → R) (s : Finset τ) : R :=
  ∑ r ∈ (selections (ι:=ι) (τ:=τ)).filter (fun r => labels r=s),
    (∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det

/-- Weighted multilinearity before grouping equal unordered label sets. -/
theorem ordered_expansion (q : R) (w : τ → ℕ) (c : ι → τ → R) (v : τ → ι → R) :
    (Matrix.of (fun i j => ∑ a, c i a * (q^w a * v a j))).det =
      ∑ r : ι → τ, q^(∑ i, w (r i)) *
        ((∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det) := by
  classical
  let L := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R)
  have hexpand : (Matrix.of (fun i j => ∑ a, c i a * (q^w a*v a j))).det =
      ∑ r : ι → τ, (∏ i, c i (r i)) *
        (Matrix.of (fun i j => q^w (r i)*v (r i) j)).det := by
    change L (fun i j => ∑ a, c i a*(q^w a*v a j)) = _
    have h := L.toMultilinearMap.map_sum (fun i a => c i a • (fun j => q^w a*v a j))
    simp only [AlternatingMap.coe_multilinearMap] at h
    have hfun : (fun i => ∑ a, c i a • (fun j => q^w a*v a j)) =
        (fun i j => ∑ a, c i a*(q^w a*v a j)) := by
      funext i j
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [hfun] at h
    have hs (r : ι → τ) : L (fun i => c i (r i) • (fun j => q^w (r i)*v (r i) j)) =
        (∏ i, c i (r i)) * L (fun i j => q^w (r i)*v (r i) j) :=
      L.toMultilinearMap.map_smul_univ _ _
    simpa only [hs] using h
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro r _
  rw [Matrix.det_mul_column,Finset.prod_pow_eq_pow_sum]
  change (∏ i, c i (r i)) * (q^(∑ i, w (r i)) *
    Matrix.det (fun i => v (r i))) =
    q^(∑ i, w (r i)) * ((∏ i, c i (r i)) *
    Matrix.det (fun i => v (r i)))
  ring

/-- Repeated vector labels vanish; only injective selections contribute. -/
theorem injective_expansion (q : R) (w : τ → ℕ) (c : ι → τ → R) (v : τ → ι → R) :
    (Matrix.of (fun i j => ∑ a, c i a * (q^w a*v a j))).det =
      ∑ r ∈ selections, q^(∑ i, w (r i)) *
        ((∏ i, c i (r i)) * (Matrix.of (fun i => v (r i))).det) := by
  classical
  rw [ordered_expansion]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r _ hr
  have hn : ¬ Function.Injective r := by simpa [selections] using hr
  obtain ⟨a,b,hab,hne⟩ := Function.not_injective_iff.mp hn
  have hz : (Matrix.of (fun i => v (r i))).det=0 :=
    Matrix.detRowAlternating.map_eq_zero_of_eq _ (congrArg v hab) hne
  simp [hz]

/-- The weighted determinant identity over unordered sets, with no factorial
and no arbitrary ordering of the local vector labels. -/
theorem unordered_expansion (q : R) (w : τ → ℕ) (c : ι → τ → R) (v : τ → ι → R) :
    (Matrix.of (fun i j => ∑ a, c i a * (q^w a*v a j))).det =
      ∑ s ∈ (selections (ι:=ι) (τ:=τ)).image labels,
        q^(∑ a ∈ s, w a)*coefficient c v s := by
  classical
  rw [injective_expansion]
  symm
  apply Finset.sum_image'
  intro r hr
  have hinj : Function.Injective r := (Finset.mem_filter.mp hr).2
  unfold coefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hti : Function.Injective t := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
  have he : labels t=labels r := (Finset.mem_filter.mp ht).2
  have hw : (∑ a ∈ labels r,w a) = ∑ i,w (t i) := by
    rw [← he,labels,Finset.sum_image]
    intro a _ b _ h
    exact hti h
  rw [hw]

/-- The image labels are exactly the subsets of size equal to the matrix order. -/
theorem labels_mem_iff (s : Finset τ) :
    s ∈ (selections (ι:=ι) (τ:=τ)).image labels ↔ s.card=Fintype.card ι := by
  classical
  constructor
  · intro hs
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
    have hi := (Finset.mem_filter.mp hr).2
    rw [labels,Finset.card_image_of_injective _ hi,Finset.card_univ]
  · intro hs
    let e : ι ≃ s := Fintype.equivOfCardEq (by simpa using hs.symm)
    let r : ι → τ := fun i => (e i).val
    have hi : Function.Injective r := Subtype.val_injective.comp e.injective
    refine Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,?_⟩
    ext a
    constructor
    · intro ha
      obtain ⟨i,_,he⟩ := Finset.mem_image.mp ha
      exact he ▸ (e i).property
    · intro ha
      refine Finset.mem_image.mpr ⟨e.symm ⟨a,ha⟩,Finset.mem_univ _,?_⟩
      simp [r]

/-- A standard powerset-indexed form of the unordered weighted identity. -/
theorem powerset_expansion (q : R) (w : τ → ℕ) (c : ι → τ → R) (v : τ → ι → R) :
    (Matrix.of (fun i j => ∑ a,c i a*(q^w a*v a j))).det =
      ∑ s ∈ Finset.univ.powersetCard (Fintype.card ι),
        q^(∑ a ∈ s,w a)*coefficient c v s := by
  classical
  have he : (selections (ι:=ι) (τ:=τ)).image labels =
      Finset.univ.powersetCard (Fintype.card ι) := by
    ext s
    simp only [labels_mem_iff,Finset.mem_powersetCard,Finset.subset_univ,true_and]
  simpa only [he] using unordered_expansion q w c v

/-- A weight lower bound on unordered selections is enough for divisibility. -/
theorem unordered_divisibility (q : R) (w : τ → ℕ) (c : ι → τ → R) (v : τ → ι → R)
    (m : ℕ) (hm : ∀ s ∈ (selections (ι:=ι) (τ:=τ)).image labels,
      coefficient c v s ≠ 0 → m ≤ ∑ a ∈ s,w a) :
    q^m ∣ (Matrix.of (fun i j => ∑ a, c i a*(q^w a*v a j))).det := by
  classical
  rw [unordered_expansion]
  apply Finset.dvd_sum
  intro s hs
  by_cases hc : coefficient c v s=0
  · simp [hc]
  · exact dvd_mul_of_dvd_left (pow_dvd_pow q (hm s hs hc)) _

end PerfectPower.UnorderedWeightedDeterminant
