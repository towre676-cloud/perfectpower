import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_20_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,3]]
def recurrence_20_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,3]]
def recurrence_20_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_20_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,3]]]
def recurrence_20_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,3]
def recurrence_20_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_20_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_20_G (recurrence_20_words j)=recurrence_20_B j := by decide +kernel
theorem recurrence_20_products_checked : ∀ j i, recurrence_20_G i*recurrence_20_B j=∑ t,(recurrence_20_C j i t) • recurrence_20_B t := by decide +kernel
theorem recurrence_20_decoder_checked : recurrence_20_D*recurrence_20_X=1 := by decide +kernel
theorem recurrence_20_complete : Submodule.span ℚ (Set.range recurrence_20_B)=GeneratedOperatorAlgebra.wordSpan recurrence_20_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_20_words j,recurrence_20_words_checked j⟩
  · intro i j
    rw [recurrence_20_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_21_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,6]]
def recurrence_21_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,6]]
def recurrence_21_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_21_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,6]]]
def recurrence_21_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,6]
def recurrence_21_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_21_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_21_G (recurrence_21_words j)=recurrence_21_B j := by decide +kernel
theorem recurrence_21_products_checked : ∀ j i, recurrence_21_G i*recurrence_21_B j=∑ t,(recurrence_21_C j i t) • recurrence_21_B t := by decide +kernel
theorem recurrence_21_decoder_checked : recurrence_21_D*recurrence_21_X=1 := by decide +kernel
theorem recurrence_21_complete : Submodule.span ℚ (Set.range recurrence_21_B)=GeneratedOperatorAlgebra.wordSpan recurrence_21_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_21_words j,recurrence_21_words_checked j⟩
  · intro i j
    rw [recurrence_21_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_22_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,1],!![0,0,1;0,1,1;0,1,2]]
def recurrence_22_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,1]]
def recurrence_22_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_22_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,1]]]
def recurrence_22_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,1;0,0,0;0,1,1;1,1,2]
def recurrence_22_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_22_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_22_G (recurrence_22_words j)=recurrence_22_B j := by decide +kernel
theorem recurrence_22_products_checked : ∀ j i, recurrence_22_G i*recurrence_22_B j=∑ t,(recurrence_22_C j i t) • recurrence_22_B t := by decide +kernel
theorem recurrence_22_decoder_checked : recurrence_22_D*recurrence_22_X=1 := by decide +kernel
theorem recurrence_22_complete : Submodule.span ℚ (Set.range recurrence_22_B)=GeneratedOperatorAlgebra.wordSpan recurrence_22_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_22_words j,recurrence_22_words_checked j⟩
  · intro i j
    rw [recurrence_22_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_23_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;-1,2,2],!![0,0,1;-1,2,2;-2,3,6]]
def recurrence_23_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;-1,2,2]]
def recurrence_23_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_23_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![-1,2,2]]]
def recurrence_23_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,-1;1,0,2;0,1,2;0,-1,-2;0,2,3;1,2,6]
def recurrence_23_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_23_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_23_G (recurrence_23_words j)=recurrence_23_B j := by decide +kernel
theorem recurrence_23_products_checked : ∀ j i, recurrence_23_G i*recurrence_23_B j=∑ t,(recurrence_23_C j i t) • recurrence_23_B t := by decide +kernel
theorem recurrence_23_decoder_checked : recurrence_23_D*recurrence_23_X=1 := by decide +kernel
theorem recurrence_23_complete : Submodule.span ℚ (Set.range recurrence_23_B)=GeneratedOperatorAlgebra.wordSpan recurrence_23_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_23_words j,recurrence_23_words_checked j⟩
  · intro i j
    rw [recurrence_23_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_24_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-15,15],!![0,0,1;1,-15,15;15,-224,210]]
def recurrence_24_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-15,15]]
def recurrence_24_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_24_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-15,15]]]
def recurrence_24_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-15;0,1,15;0,1,15;0,-15,-224;1,15,210]
def recurrence_24_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_24_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_24_G (recurrence_24_words j)=recurrence_24_B j := by decide +kernel
theorem recurrence_24_products_checked : ∀ j i, recurrence_24_G i*recurrence_24_B j=∑ t,(recurrence_24_C j i t) • recurrence_24_B t := by decide +kernel
theorem recurrence_24_decoder_checked : recurrence_24_D*recurrence_24_X=1 := by decide +kernel
theorem recurrence_24_complete : Submodule.span ℚ (Set.range recurrence_24_B)=GeneratedOperatorAlgebra.wordSpan recurrence_24_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_24_words j,recurrence_24_words_checked j⟩
  · intro i j
    rw [recurrence_24_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_25_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-35,35],!![0,0,1;1,-35,35;35,-1224,1190]]
def recurrence_25_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-35,35]]
def recurrence_25_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_25_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-35,35]]]
def recurrence_25_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-35;0,1,35;0,1,35;0,-35,-1224;1,35,1190]
def recurrence_25_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_25_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_25_G (recurrence_25_words j)=recurrence_25_B j := by decide +kernel
theorem recurrence_25_products_checked : ∀ j i, recurrence_25_G i*recurrence_25_B j=∑ t,(recurrence_25_C j i t) • recurrence_25_B t := by decide +kernel
theorem recurrence_25_decoder_checked : recurrence_25_D*recurrence_25_X=1 := by decide +kernel
theorem recurrence_25_complete : Submodule.span ℚ (Set.range recurrence_25_B)=GeneratedOperatorAlgebra.wordSpan recurrence_25_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_25_words j,recurrence_25_words_checked j⟩
  · intro i j
    rw [recurrence_25_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_26_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-35,35],!![0,0,1;1,-35,35;35,-1224,1190]]
def recurrence_26_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-35,35]]
def recurrence_26_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_26_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-35,35]]]
def recurrence_26_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-35;0,1,35;0,1,35;0,-35,-1224;1,35,1190]
def recurrence_26_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_26_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_26_G (recurrence_26_words j)=recurrence_26_B j := by decide +kernel
theorem recurrence_26_products_checked : ∀ j i, recurrence_26_G i*recurrence_26_B j=∑ t,(recurrence_26_C j i t) • recurrence_26_B t := by decide +kernel
theorem recurrence_26_decoder_checked : recurrence_26_D*recurrence_26_X=1 := by decide +kernel
theorem recurrence_26_complete : Submodule.span ℚ (Set.range recurrence_26_B)=GeneratedOperatorAlgebra.wordSpan recurrence_26_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_26_words j,recurrence_26_words_checked j⟩
  · intro i j
    rw [recurrence_26_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_27_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,4]]
def recurrence_27_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,4]]
def recurrence_27_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_27_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,4]]]
def recurrence_27_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,4]
def recurrence_27_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_27_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_27_G (recurrence_27_words j)=recurrence_27_B j := by decide +kernel
theorem recurrence_27_products_checked : ∀ j i, recurrence_27_G i*recurrence_27_B j=∑ t,(recurrence_27_C j i t) • recurrence_27_B t := by decide +kernel
theorem recurrence_27_decoder_checked : recurrence_27_D*recurrence_27_X=1 := by decide +kernel
theorem recurrence_27_complete : Submodule.span ℚ (Set.range recurrence_27_B)=GeneratedOperatorAlgebra.wordSpan recurrence_27_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_27_words j,recurrence_27_words_checked j⟩
  · intro i j
    rw [recurrence_27_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_28_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,3]]
def recurrence_28_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,3]]
def recurrence_28_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_28_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,3]]]
def recurrence_28_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,3]
def recurrence_28_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_28_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_28_G (recurrence_28_words j)=recurrence_28_B j := by decide +kernel
theorem recurrence_28_products_checked : ∀ j i, recurrence_28_G i*recurrence_28_B j=∑ t,(recurrence_28_C j i t) • recurrence_28_B t := by decide +kernel
theorem recurrence_28_decoder_checked : recurrence_28_D*recurrence_28_X=1 := by decide +kernel
theorem recurrence_28_complete : Submodule.span ℚ (Set.range recurrence_28_B)=GeneratedOperatorAlgebra.wordSpan recurrence_28_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_28_words j,recurrence_28_words_checked j⟩
  · intro i j
    rw [recurrence_28_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_29_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,14]]
def recurrence_29_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,14]]
def recurrence_29_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_29_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,14]]]
def recurrence_29_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,14]
def recurrence_29_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_29_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_29_G (recurrence_29_words j)=recurrence_29_B j := by decide +kernel
theorem recurrence_29_products_checked : ∀ j i, recurrence_29_G i*recurrence_29_B j=∑ t,(recurrence_29_C j i t) • recurrence_29_B t := by decide +kernel
theorem recurrence_29_decoder_checked : recurrence_29_D*recurrence_29_X=1 := by decide +kernel
theorem recurrence_29_complete : Submodule.span ℚ (Set.range recurrence_29_B)=GeneratedOperatorAlgebra.wordSpan recurrence_29_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_29_words j,recurrence_29_words_checked j⟩
  · intro i j
    rw [recurrence_29_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
