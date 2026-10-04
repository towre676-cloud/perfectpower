import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_10_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,4]]
def recurrence_10_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,4]]
def recurrence_10_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_10_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,4]]]
def recurrence_10_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,4]
def recurrence_10_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_10_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_10_G (recurrence_10_words j)=recurrence_10_B j := by decide +kernel
theorem recurrence_10_products_checked : ∀ j i, recurrence_10_G i*recurrence_10_B j=∑ t,(recurrence_10_C j i t) • recurrence_10_B t := by decide +kernel
theorem recurrence_10_decoder_checked : recurrence_10_D*recurrence_10_X=1 := by decide +kernel
theorem recurrence_10_complete : Submodule.span ℚ (Set.range recurrence_10_B)=GeneratedOperatorAlgebra.wordSpan recurrence_10_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_10_words j,recurrence_10_words_checked j⟩
  · intro i j
    rw [recurrence_10_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_11_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,3]]
def recurrence_11_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,3]]
def recurrence_11_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_11_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,3]]]
def recurrence_11_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,3]
def recurrence_11_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_11_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_11_G (recurrence_11_words j)=recurrence_11_B j := by decide +kernel
theorem recurrence_11_products_checked : ∀ j i, recurrence_11_G i*recurrence_11_B j=∑ t,(recurrence_11_C j i t) • recurrence_11_B t := by decide +kernel
theorem recurrence_11_decoder_checked : recurrence_11_D*recurrence_11_X=1 := by decide +kernel
theorem recurrence_11_complete : Submodule.span ℚ (Set.range recurrence_11_B)=GeneratedOperatorAlgebra.wordSpan recurrence_11_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_11_words j,recurrence_11_words_checked j⟩
  · intro i j
    rw [recurrence_11_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_12_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,6]]
def recurrence_12_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,6]]
def recurrence_12_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_12_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,6]]]
def recurrence_12_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,6]
def recurrence_12_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_12_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_12_G (recurrence_12_words j)=recurrence_12_B j := by decide +kernel
theorem recurrence_12_products_checked : ∀ j i, recurrence_12_G i*recurrence_12_B j=∑ t,(recurrence_12_C j i t) • recurrence_12_B t := by decide +kernel
theorem recurrence_12_decoder_checked : recurrence_12_D*recurrence_12_X=1 := by decide +kernel
theorem recurrence_12_complete : Submodule.span ℚ (Set.range recurrence_12_B)=GeneratedOperatorAlgebra.wordSpan recurrence_12_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_12_words j,recurrence_12_words_checked j⟩
  · intro i j
    rw [recurrence_12_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_13_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,6]]
def recurrence_13_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,6]]
def recurrence_13_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_13_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,6]]]
def recurrence_13_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,6]
def recurrence_13_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_13_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_13_G (recurrence_13_words j)=recurrence_13_B j := by decide +kernel
theorem recurrence_13_products_checked : ∀ j i, recurrence_13_G i*recurrence_13_B j=∑ t,(recurrence_13_C j i t) • recurrence_13_B t := by decide +kernel
theorem recurrence_13_decoder_checked : recurrence_13_D*recurrence_13_X=1 := by decide +kernel
theorem recurrence_13_complete : Submodule.span ℚ (Set.range recurrence_13_B)=GeneratedOperatorAlgebra.wordSpan recurrence_13_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_13_words j,recurrence_13_words_checked j⟩
  · intro i j
    rw [recurrence_13_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_14_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-7,7],!![0,0,1;1,-7,7;7,-48,42]]
def recurrence_14_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-7,7]]
def recurrence_14_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_14_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-7,7]]]
def recurrence_14_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-7;0,1,7;0,1,7;0,-7,-48;1,7,42]
def recurrence_14_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_14_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_14_G (recurrence_14_words j)=recurrence_14_B j := by decide +kernel
theorem recurrence_14_products_checked : ∀ j i, recurrence_14_G i*recurrence_14_B j=∑ t,(recurrence_14_C j i t) • recurrence_14_B t := by decide +kernel
theorem recurrence_14_decoder_checked : recurrence_14_D*recurrence_14_X=1 := by decide +kernel
theorem recurrence_14_complete : Submodule.span ℚ (Set.range recurrence_14_B)=GeneratedOperatorAlgebra.wordSpan recurrence_14_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_14_words j,recurrence_14_words_checked j⟩
  · intro i j
    rw [recurrence_14_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_15_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,6]]
def recurrence_15_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,6]]
def recurrence_15_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_15_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,6]]]
def recurrence_15_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,6]
def recurrence_15_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_15_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_15_G (recurrence_15_words j)=recurrence_15_B j := by decide +kernel
theorem recurrence_15_products_checked : ∀ j i, recurrence_15_G i*recurrence_15_B j=∑ t,(recurrence_15_C j i t) • recurrence_15_B t := by decide +kernel
theorem recurrence_15_decoder_checked : recurrence_15_D*recurrence_15_X=1 := by decide +kernel
theorem recurrence_15_complete : Submodule.span ℚ (Set.range recurrence_15_B)=GeneratedOperatorAlgebra.wordSpan recurrence_15_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_15_words j,recurrence_15_words_checked j⟩
  · intro i j
    rw [recurrence_15_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_16_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,4]]
def recurrence_16_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,4]]
def recurrence_16_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_16_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,4]]]
def recurrence_16_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,4]
def recurrence_16_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_16_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_16_G (recurrence_16_words j)=recurrence_16_B j := by decide +kernel
theorem recurrence_16_products_checked : ∀ j i, recurrence_16_G i*recurrence_16_B j=∑ t,(recurrence_16_C j i t) • recurrence_16_B t := by decide +kernel
theorem recurrence_16_decoder_checked : recurrence_16_D*recurrence_16_X=1 := by decide +kernel
theorem recurrence_16_complete : Submodule.span ℚ (Set.range recurrence_16_B)=GeneratedOperatorAlgebra.wordSpan recurrence_16_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_16_words j,recurrence_16_words_checked j⟩
  · intro i j
    rw [recurrence_16_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_17_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,3]]
def recurrence_17_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,3]]
def recurrence_17_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_17_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,3]]]
def recurrence_17_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,3]
def recurrence_17_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_17_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_17_G (recurrence_17_words j)=recurrence_17_B j := by decide +kernel
theorem recurrence_17_products_checked : ∀ j i, recurrence_17_G i*recurrence_17_B j=∑ t,(recurrence_17_C j i t) • recurrence_17_B t := by decide +kernel
theorem recurrence_17_decoder_checked : recurrence_17_D*recurrence_17_X=1 := by decide +kernel
theorem recurrence_17_complete : Submodule.span ℚ (Set.range recurrence_17_B)=GeneratedOperatorAlgebra.wordSpan recurrence_17_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_17_words j,recurrence_17_words_checked j⟩
  · intro i j
    rw [recurrence_17_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_18_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,6]]
def recurrence_18_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,6]]
def recurrence_18_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_18_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,6]]]
def recurrence_18_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,6]
def recurrence_18_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_18_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_18_G (recurrence_18_words j)=recurrence_18_B j := by decide +kernel
theorem recurrence_18_products_checked : ∀ j i, recurrence_18_G i*recurrence_18_B j=∑ t,(recurrence_18_C j i t) • recurrence_18_B t := by decide +kernel
theorem recurrence_18_decoder_checked : recurrence_18_D*recurrence_18_X=1 := by decide +kernel
theorem recurrence_18_complete : Submodule.span ℚ (Set.range recurrence_18_B)=GeneratedOperatorAlgebra.wordSpan recurrence_18_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_18_words j,recurrence_18_words_checked j⟩
  · intro i j
    rw [recurrence_18_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_19_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,3]]
def recurrence_19_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,3]]
def recurrence_19_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_19_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,3]]]
def recurrence_19_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,3]
def recurrence_19_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_19_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_19_G (recurrence_19_words j)=recurrence_19_B j := by decide +kernel
theorem recurrence_19_products_checked : ∀ j i, recurrence_19_G i*recurrence_19_B j=∑ t,(recurrence_19_C j i t) • recurrence_19_B t := by decide +kernel
theorem recurrence_19_decoder_checked : recurrence_19_D*recurrence_19_X=1 := by decide +kernel
theorem recurrence_19_complete : Submodule.span ℚ (Set.range recurrence_19_B)=GeneratedOperatorAlgebra.wordSpan recurrence_19_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_19_words j,recurrence_19_words_checked j⟩
  · intro i j
    rw [recurrence_19_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
