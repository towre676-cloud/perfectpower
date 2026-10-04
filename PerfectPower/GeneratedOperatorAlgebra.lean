import Mathlib
noncomputable section
namespace PerfectPower.GeneratedOperatorAlgebra
open Matrix
variable {K R ι : Type*} [Field K] [Ring R] [Algebra K R]
def word (G : ι → R) : List ι → R
  | [] => 1
  | i::is => G i*word G is
def wordSpan (G : ι → R) : Submodule K R := Submodule.span K (Set.range (word G))

/-- A unital span closed under left multiplication by generators contains every word. -/
theorem word_mem (G : ι → R) (W : Submodule K R) (h1 : (1:R) ∈ W)
    (hG : ∀ i x,x ∈ W → G i*x ∈ W) (is : List ι) : word G is ∈ W := by
  induction is with
  | nil => exact h1
  | cons i is ih => exact hG i _ ih

theorem minimal (G : ι → R) (W : Submodule K R) (h1 : (1:R) ∈ W)
    (hG : ∀ i x,x ∈ W → G i*x ∈ W) : wordSpan G ≤ W := by
  apply Submodule.span_le.mpr
  rintro x ⟨is,rfl⟩
  exact word_mem G W h1 hG is

/-- Recorded word membership and generator closure prove exact span completeness. -/
theorem complete (G : ι → R) (W : Submodule K R) (h1 : (1:R) ∈ W)
    (hG : ∀ i x,x ∈ W → G i*x ∈ W) (hwords : W ≤ wordSpan G) : W=wordSpan G :=
  le_antisymm hwords (minimal G W h1 hG)

/-- A separating linear functional certifies genuine nonmembership. -/
theorem separator (W : Submodule K R) (f : R →ₗ[K] K) (hW : ∀ x,x ∈ W → f x=0)
    (t : R) (ht : f t ≠ 0) : t ∉ W := by
  intro h
  exact ht (hW t h)

/-- Commutation propagates from generators through every word. -/
theorem commutes_word (G : ι → R) (C : R) (h : ∀ i,C*G i=G i*C) (is : List ι) :
    C*word G is=word G is*C := by
  induction is with
  | nil => simp [word]
  | cons i is ih => simp only [word,← mul_assoc,h i];rw [mul_assoc,ih,← mul_assoc]
/-- Finite word and generator-product certificates suffice for complete generated spans. -/
theorem finite_complete {j : Type*} (G : ι → R) (B : j → R)
    (h1 : ∃ k,B k=1) (hwords : ∀ k,∃ is,word G is=B k)
    (hproducts : ∀ i k,G i*B k ∈ Submodule.span K (Set.range B)) :
    Submodule.span K (Set.range B)=wordSpan G := by
  let W := Submodule.span K (Set.range B)
  apply complete G W
  · obtain ⟨k,hk⟩ := h1
    rw [← hk]
    exact Submodule.subset_span ⟨k,rfl⟩
  · intro i x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨k,rfl⟩ := hx;exact hproducts i k
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [mul_add] using W.add_mem ihx ihy
    | smul a x hx ih => simpa only [mul_smul_comm] using W.smul_mem a ih
  · apply Submodule.span_le.mpr
    rintro x ⟨k,rfl⟩
    obtain ⟨is,his⟩ := hwords k
    exact Submodule.subset_span ⟨is,his⟩

/-- A two-sided coordinate test is unnecessary: a left decoder already proves uniqueness. -/
theorem decoder_injective {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    (X : Matrix n m K) (D : Matrix m n K) (h : D*X=1) :
    Function.Injective (fun u : m → K => X*ᵥ u) := by
  intro u v huv
  have he := congrArg (fun z => D*ᵥ z) huv
  simpa only [Matrix.mulVec_mulVec,h,Matrix.one_mulVec] using he

end PerfectPower.GeneratedOperatorAlgebra
