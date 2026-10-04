import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_0_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_0_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_0_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_0_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_0_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_0_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_0_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_0_G (recurrence_0_words j)=recurrence_0_B j := by decide +kernel
theorem recurrence_0_products_checked : ∀ j i, recurrence_0_G i*recurrence_0_B j=∑ t,(recurrence_0_C j i t) • recurrence_0_B t := by decide +kernel
theorem recurrence_0_decoder_checked : recurrence_0_D*recurrence_0_X=1 := by decide +kernel
theorem recurrence_0_complete : Submodule.span ℚ (Set.range recurrence_0_B)=GeneratedOperatorAlgebra.wordSpan recurrence_0_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_0_words j,recurrence_0_words_checked j⟩
  · intro i j
    rw [recurrence_0_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_1_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_1_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_1_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_1_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_1_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_1_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_1_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_1_G (recurrence_1_words j)=recurrence_1_B j := by decide +kernel
theorem recurrence_1_products_checked : ∀ j i, recurrence_1_G i*recurrence_1_B j=∑ t,(recurrence_1_C j i t) • recurrence_1_B t := by decide +kernel
theorem recurrence_1_decoder_checked : recurrence_1_D*recurrence_1_X=1 := by decide +kernel
theorem recurrence_1_complete : Submodule.span ℚ (Set.range recurrence_1_B)=GeneratedOperatorAlgebra.wordSpan recurrence_1_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_1_words j,recurrence_1_words_checked j⟩
  · intro i j
    rw [recurrence_1_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_2_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,2]]
def recurrence_2_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,2]]
def recurrence_2_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_2_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,2]]]
def recurrence_2_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,2]
def recurrence_2_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_2_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_2_G (recurrence_2_words j)=recurrence_2_B j := by decide +kernel
theorem recurrence_2_products_checked : ∀ j i, recurrence_2_G i*recurrence_2_B j=∑ t,(recurrence_2_C j i t) • recurrence_2_B t := by decide +kernel
theorem recurrence_2_decoder_checked : recurrence_2_D*recurrence_2_X=1 := by decide +kernel
theorem recurrence_2_complete : Submodule.span ℚ (Set.range recurrence_2_B)=GeneratedOperatorAlgebra.wordSpan recurrence_2_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_2_words j,recurrence_2_words_checked j⟩
  · intro i j
    rw [recurrence_2_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_3_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_3_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_3_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_3_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_3_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_3_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_3_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_3_G (recurrence_3_words j)=recurrence_3_B j := by decide +kernel
theorem recurrence_3_products_checked : ∀ j i, recurrence_3_G i*recurrence_3_B j=∑ t,(recurrence_3_C j i t) • recurrence_3_B t := by decide +kernel
theorem recurrence_3_decoder_checked : recurrence_3_D*recurrence_3_X=1 := by decide +kernel
theorem recurrence_3_complete : Submodule.span ℚ (Set.range recurrence_3_B)=GeneratedOperatorAlgebra.wordSpan recurrence_3_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_3_words j,recurrence_3_words_checked j⟩
  · intro i j
    rw [recurrence_3_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_4_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,4]]
def recurrence_4_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,4]]
def recurrence_4_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_4_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,4]]]
def recurrence_4_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,4]
def recurrence_4_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_4_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_4_G (recurrence_4_words j)=recurrence_4_B j := by decide +kernel
theorem recurrence_4_products_checked : ∀ j i, recurrence_4_G i*recurrence_4_B j=∑ t,(recurrence_4_C j i t) • recurrence_4_B t := by decide +kernel
theorem recurrence_4_decoder_checked : recurrence_4_D*recurrence_4_X=1 := by decide +kernel
theorem recurrence_4_complete : Submodule.span ℚ (Set.range recurrence_4_B)=GeneratedOperatorAlgebra.wordSpan recurrence_4_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_4_words j,recurrence_4_words_checked j⟩
  · intro i j
    rw [recurrence_4_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_5_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-7,7],!![0,0,1;1,-7,7;7,-48,42]]
def recurrence_5_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-7,7]]
def recurrence_5_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_5_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-7,7]]]
def recurrence_5_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-7;0,1,7;0,1,7;0,-7,-48;1,7,42]
def recurrence_5_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_5_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_5_G (recurrence_5_words j)=recurrence_5_B j := by decide +kernel
theorem recurrence_5_products_checked : ∀ j i, recurrence_5_G i*recurrence_5_B j=∑ t,(recurrence_5_C j i t) • recurrence_5_B t := by decide +kernel
theorem recurrence_5_decoder_checked : recurrence_5_D*recurrence_5_X=1 := by decide +kernel
theorem recurrence_5_complete : Submodule.span ℚ (Set.range recurrence_5_B)=GeneratedOperatorAlgebra.wordSpan recurrence_5_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_5_words j,recurrence_5_words_checked j⟩
  · intro i j
    rw [recurrence_5_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_6_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,6]]
def recurrence_6_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,6]]
def recurrence_6_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_6_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,6]]]
def recurrence_6_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,6]
def recurrence_6_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_6_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_6_G (recurrence_6_words j)=recurrence_6_B j := by decide +kernel
theorem recurrence_6_products_checked : ∀ j i, recurrence_6_G i*recurrence_6_B j=∑ t,(recurrence_6_C j i t) • recurrence_6_B t := by decide +kernel
theorem recurrence_6_decoder_checked : recurrence_6_D*recurrence_6_X=1 := by decide +kernel
theorem recurrence_6_complete : Submodule.span ℚ (Set.range recurrence_6_B)=GeneratedOperatorAlgebra.wordSpan recurrence_6_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_6_words j,recurrence_6_words_checked j⟩
  · intro i j
    rw [recurrence_6_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_7_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-35,35],!![0,0,1;1,-35,35;35,-1224,1190]]
def recurrence_7_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-35,35]]
def recurrence_7_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_7_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-35,35]]]
def recurrence_7_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-35;0,1,35;0,1,35;0,-35,-1224;1,35,1190]
def recurrence_7_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_7_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_7_G (recurrence_7_words j)=recurrence_7_B j := by decide +kernel
theorem recurrence_7_products_checked : ∀ j i, recurrence_7_G i*recurrence_7_B j=∑ t,(recurrence_7_C j i t) • recurrence_7_B t := by decide +kernel
theorem recurrence_7_decoder_checked : recurrence_7_D*recurrence_7_X=1 := by decide +kernel
theorem recurrence_7_complete : Submodule.span ℚ (Set.range recurrence_7_B)=GeneratedOperatorAlgebra.wordSpan recurrence_7_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_7_words j,recurrence_7_words_checked j⟩
  · intro i j
    rw [recurrence_7_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_8_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;-1,2,2],!![0,0,1;-1,2,2;-2,3,6]]
def recurrence_8_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;-1,2,2]]
def recurrence_8_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_8_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![-1,2,2]]]
def recurrence_8_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,-1;1,0,2;0,1,2;0,-1,-2;0,2,3;1,2,6]
def recurrence_8_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_8_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_8_G (recurrence_8_words j)=recurrence_8_B j := by decide +kernel
theorem recurrence_8_products_checked : ∀ j i, recurrence_8_G i*recurrence_8_B j=∑ t,(recurrence_8_C j i t) • recurrence_8_B t := by decide +kernel
theorem recurrence_8_decoder_checked : recurrence_8_D*recurrence_8_X=1 := by decide +kernel
theorem recurrence_8_complete : Submodule.span ℚ (Set.range recurrence_8_B)=GeneratedOperatorAlgebra.wordSpan recurrence_8_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_8_words j,recurrence_8_words_checked j⟩
  · intro i j
    rw [recurrence_8_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_9_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,2]]
def recurrence_9_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,2]]
def recurrence_9_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_9_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,2]]]
def recurrence_9_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,2]
def recurrence_9_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_9_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_9_G (recurrence_9_words j)=recurrence_9_B j := by decide +kernel
theorem recurrence_9_products_checked : ∀ j i, recurrence_9_G i*recurrence_9_B j=∑ t,(recurrence_9_C j i t) • recurrence_9_B t := by decide +kernel
theorem recurrence_9_decoder_checked : recurrence_9_D*recurrence_9_X=1 := by decide +kernel
theorem recurrence_9_complete : Submodule.span ℚ (Set.range recurrence_9_B)=GeneratedOperatorAlgebra.wordSpan recurrence_9_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_9_words j,recurrence_9_words_checked j⟩
  · intro i j
    rw [recurrence_9_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
