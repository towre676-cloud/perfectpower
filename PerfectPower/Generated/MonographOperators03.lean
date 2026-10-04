import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_30_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,14]]
def recurrence_30_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,14]]
def recurrence_30_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_30_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,14]]]
def recurrence_30_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,14]
def recurrence_30_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_30_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_30_G (recurrence_30_words j)=recurrence_30_B j := by decide +kernel
theorem recurrence_30_products_checked : ∀ j i, recurrence_30_G i*recurrence_30_B j=∑ t,(recurrence_30_C j i t) • recurrence_30_B t := by decide +kernel
theorem recurrence_30_decoder_checked : recurrence_30_D*recurrence_30_X=1 := by decide +kernel
theorem recurrence_30_complete : Submodule.span ℚ (Set.range recurrence_30_B)=GeneratedOperatorAlgebra.wordSpan recurrence_30_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_30_words j,recurrence_30_words_checked j⟩
  · intro i j
    rw [recurrence_30_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_31_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;-1,-1,3],!![0,0,1;-1,-1,3;-3,-4,8]]
def recurrence_31_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;-1,-1,3]]
def recurrence_31_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_31_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![-1,-1,3]]]
def recurrence_31_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,-1;1,0,-1;0,1,3;0,-1,-3;0,-1,-4;1,3,8]
def recurrence_31_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_31_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_31_G (recurrence_31_words j)=recurrence_31_B j := by decide +kernel
theorem recurrence_31_products_checked : ∀ j i, recurrence_31_G i*recurrence_31_B j=∑ t,(recurrence_31_C j i t) • recurrence_31_B t := by decide +kernel
theorem recurrence_31_decoder_checked : recurrence_31_D*recurrence_31_X=1 := by decide +kernel
theorem recurrence_31_complete : Submodule.span ℚ (Set.range recurrence_31_B)=GeneratedOperatorAlgebra.wordSpan recurrence_31_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_31_words j,recurrence_31_words_checked j⟩
  · intro i j
    rw [recurrence_31_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_32_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_32_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_32_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_32_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_32_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_32_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_32_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_32_G (recurrence_32_words j)=recurrence_32_B j := by decide +kernel
theorem recurrence_32_products_checked : ∀ j i, recurrence_32_G i*recurrence_32_B j=∑ t,(recurrence_32_C j i t) • recurrence_32_B t := by decide +kernel
theorem recurrence_32_decoder_checked : recurrence_32_D*recurrence_32_X=1 := by decide +kernel
theorem recurrence_32_complete : Submodule.span ℚ (Set.range recurrence_32_B)=GeneratedOperatorAlgebra.wordSpan recurrence_32_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_32_words j,recurrence_32_words_checked j⟩
  · intro i j
    rw [recurrence_32_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_33_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_33_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_33_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_33_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_33_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_33_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_33_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_33_G (recurrence_33_words j)=recurrence_33_B j := by decide +kernel
theorem recurrence_33_products_checked : ∀ j i, recurrence_33_G i*recurrence_33_B j=∑ t,(recurrence_33_C j i t) • recurrence_33_B t := by decide +kernel
theorem recurrence_33_decoder_checked : recurrence_33_D*recurrence_33_X=1 := by decide +kernel
theorem recurrence_33_complete : Submodule.span ℚ (Set.range recurrence_33_B)=GeneratedOperatorAlgebra.wordSpan recurrence_33_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_33_words j,recurrence_33_words_checked j⟩
  · intro i j
    rw [recurrence_33_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_34_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_34_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_34_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_34_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_34_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_34_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_34_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_34_G (recurrence_34_words j)=recurrence_34_B j := by decide +kernel
theorem recurrence_34_products_checked : ∀ j i, recurrence_34_G i*recurrence_34_B j=∑ t,(recurrence_34_C j i t) • recurrence_34_B t := by decide +kernel
theorem recurrence_34_decoder_checked : recurrence_34_D*recurrence_34_X=1 := by decide +kernel
theorem recurrence_34_complete : Submodule.span ℚ (Set.range recurrence_34_B)=GeneratedOperatorAlgebra.wordSpan recurrence_34_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_34_words j,recurrence_34_words_checked j⟩
  · intro i j
    rw [recurrence_34_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_35_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;-1,-1,3],!![0,0,1;-1,-1,3;-3,-4,8]]
def recurrence_35_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;-1,-1,3]]
def recurrence_35_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_35_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![-1,-1,3]]]
def recurrence_35_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,-1;1,0,-1;0,1,3;0,-1,-3;0,-1,-4;1,3,8]
def recurrence_35_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_35_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_35_G (recurrence_35_words j)=recurrence_35_B j := by decide +kernel
theorem recurrence_35_products_checked : ∀ j i, recurrence_35_G i*recurrence_35_B j=∑ t,(recurrence_35_C j i t) • recurrence_35_B t := by decide +kernel
theorem recurrence_35_decoder_checked : recurrence_35_D*recurrence_35_X=1 := by decide +kernel
theorem recurrence_35_complete : Submodule.span ℚ (Set.range recurrence_35_B)=GeneratedOperatorAlgebra.wordSpan recurrence_35_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_35_words j,recurrence_35_words_checked j⟩
  · intro i j
    rw [recurrence_35_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_36_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,3]]
def recurrence_36_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,3]]
def recurrence_36_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_36_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,3]]]
def recurrence_36_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,3]
def recurrence_36_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_36_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_36_G (recurrence_36_words j)=recurrence_36_B j := by decide +kernel
theorem recurrence_36_products_checked : ∀ j i, recurrence_36_G i*recurrence_36_B j=∑ t,(recurrence_36_C j i t) • recurrence_36_B t := by decide +kernel
theorem recurrence_36_decoder_checked : recurrence_36_D*recurrence_36_X=1 := by decide +kernel
theorem recurrence_36_complete : Submodule.span ℚ (Set.range recurrence_36_B)=GeneratedOperatorAlgebra.wordSpan recurrence_36_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_36_words j,recurrence_36_words_checked j⟩
  · intro i j
    rw [recurrence_36_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_37_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,14]]
def recurrence_37_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,14]]
def recurrence_37_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_37_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,14]]]
def recurrence_37_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,14]
def recurrence_37_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_37_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_37_G (recurrence_37_words j)=recurrence_37_B j := by decide +kernel
theorem recurrence_37_products_checked : ∀ j i, recurrence_37_G i*recurrence_37_B j=∑ t,(recurrence_37_C j i t) • recurrence_37_B t := by decide +kernel
theorem recurrence_37_decoder_checked : recurrence_37_D*recurrence_37_X=1 := by decide +kernel
theorem recurrence_37_complete : Submodule.span ℚ (Set.range recurrence_37_B)=GeneratedOperatorAlgebra.wordSpan recurrence_37_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_37_words j,recurrence_37_words_checked j⟩
  · intro i j
    rw [recurrence_37_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_38_B : Fin 5 → Matrix (Fin 5) (Fin 5) ℚ := ![!![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1],!![0,1,0,0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1;1,-1,-5,1,3],!![0,0,1,0,0;0,0,0,1,0;0,0,0,0,1;1,-1,-5,1,3;3,-2,-16,-2,10],!![0,0,0,1,0;0,0,0,0,1;1,-1,-5,1,3;3,-2,-16,-2,10;10,-7,-52,-6,28],!![0,0,0,0,1;1,-1,-5,1,3;3,-2,-16,-2,10;10,-7,-52,-6,28;28,-18,-147,-24,78]]
def recurrence_38_G : Fin 1 → Matrix (Fin 5) (Fin 5) ℚ := ![!![0,1,0,0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1;1,-1,-5,1,3]]
def recurrence_38_words : Fin 5 → List (Fin 1) := ![[],[0],[0,0],[0,0,0],[0,0,0,0]]
def recurrence_38_C : Fin 5 → Fin 1 → Fin 5 → ℚ := ![![![0,1,0,0,0]],![![0,0,1,0,0]],![![0,0,0,1,0]],![![0,0,0,0,1]],![![1,-1,-5,1,3]]]
def recurrence_38_X : Matrix (Fin 25) (Fin 5) ℚ := !![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1;0,0,0,0,1;1,0,0,0,-1;0,1,0,0,-5;0,0,1,0,1;0,0,0,1,3;0,0,0,1,3;0,0,0,-1,-2;1,0,0,-5,-16;0,1,0,1,-2;0,0,1,3,10;0,0,1,3,10;0,0,-1,-2,-7;0,0,-5,-16,-52;1,0,1,-2,-6;0,1,3,10,28;0,1,3,10,28;0,-1,-2,-7,-18;0,-5,-16,-52,-147;0,1,-2,-6,-24;1,3,10,28,78]
def recurrence_38_D : Matrix (Fin 5) (Fin 25) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_38_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_38_G (recurrence_38_words j)=recurrence_38_B j := by decide +kernel
theorem recurrence_38_products_checked : ∀ j i, recurrence_38_G i*recurrence_38_B j=∑ t,(recurrence_38_C j i t) • recurrence_38_B t := by decide +kernel
theorem recurrence_38_decoder_checked : recurrence_38_D*recurrence_38_X=1 := by decide +kernel
theorem recurrence_38_complete : Submodule.span ℚ (Set.range recurrence_38_B)=GeneratedOperatorAlgebra.wordSpan recurrence_38_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_38_words j,recurrence_38_words_checked j⟩
  · intro i j
    rw [recurrence_38_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_39_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,7]]
def recurrence_39_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,7]]
def recurrence_39_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_39_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,7]]]
def recurrence_39_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,7]
def recurrence_39_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_39_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_39_G (recurrence_39_words j)=recurrence_39_B j := by decide +kernel
theorem recurrence_39_products_checked : ∀ j i, recurrence_39_G i*recurrence_39_B j=∑ t,(recurrence_39_C j i t) • recurrence_39_B t := by decide +kernel
theorem recurrence_39_decoder_checked : recurrence_39_D*recurrence_39_X=1 := by decide +kernel
theorem recurrence_39_complete : Submodule.span ℚ (Set.range recurrence_39_B)=GeneratedOperatorAlgebra.wordSpan recurrence_39_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_39_words j,recurrence_39_words_checked j⟩
  · intro i j
    rw [recurrence_39_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
