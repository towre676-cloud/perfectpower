import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_40_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,7]]
def recurrence_40_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,7]]
def recurrence_40_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_40_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,7]]]
def recurrence_40_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,7]
def recurrence_40_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_40_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_40_G (recurrence_40_words j)=recurrence_40_B j := by decide +kernel
theorem recurrence_40_products_checked : ∀ j i, recurrence_40_G i*recurrence_40_B j=∑ t,(recurrence_40_C j i t) • recurrence_40_B t := by decide +kernel
theorem recurrence_40_decoder_checked : recurrence_40_D*recurrence_40_X=1 := by decide +kernel
theorem recurrence_40_complete : Submodule.span ℚ (Set.range recurrence_40_B)=GeneratedOperatorAlgebra.wordSpan recurrence_40_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_40_words j,recurrence_40_words_checked j⟩
  · intro i j
    rw [recurrence_40_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_41_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-7,7],!![0,0,1;1,-7,7;7,-48,42]]
def recurrence_41_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-7,7]]
def recurrence_41_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_41_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-7,7]]]
def recurrence_41_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-7;0,1,7;0,1,7;0,-7,-48;1,7,42]
def recurrence_41_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_41_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_41_G (recurrence_41_words j)=recurrence_41_B j := by decide +kernel
theorem recurrence_41_products_checked : ∀ j i, recurrence_41_G i*recurrence_41_B j=∑ t,(recurrence_41_C j i t) • recurrence_41_B t := by decide +kernel
theorem recurrence_41_decoder_checked : recurrence_41_D*recurrence_41_X=1 := by decide +kernel
theorem recurrence_41_complete : Submodule.span ℚ (Set.range recurrence_41_B)=GeneratedOperatorAlgebra.wordSpan recurrence_41_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_41_words j,recurrence_41_words_checked j⟩
  · intro i j
    rw [recurrence_41_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_42_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,34]]
def recurrence_42_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,34]]
def recurrence_42_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_42_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,34]]]
def recurrence_42_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,34]
def recurrence_42_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_42_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_42_G (recurrence_42_words j)=recurrence_42_B j := by decide +kernel
theorem recurrence_42_products_checked : ∀ j i, recurrence_42_G i*recurrence_42_B j=∑ t,(recurrence_42_C j i t) • recurrence_42_B t := by decide +kernel
theorem recurrence_42_decoder_checked : recurrence_42_D*recurrence_42_X=1 := by decide +kernel
theorem recurrence_42_complete : Submodule.span ℚ (Set.range recurrence_42_B)=GeneratedOperatorAlgebra.wordSpan recurrence_42_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_42_words j,recurrence_42_words_checked j⟩
  · intro i j
    rw [recurrence_42_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_43_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,3]]
def recurrence_43_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,3]]
def recurrence_43_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_43_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,3]]]
def recurrence_43_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,3]
def recurrence_43_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_43_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_43_G (recurrence_43_words j)=recurrence_43_B j := by decide +kernel
theorem recurrence_43_products_checked : ∀ j i, recurrence_43_G i*recurrence_43_B j=∑ t,(recurrence_43_C j i t) • recurrence_43_B t := by decide +kernel
theorem recurrence_43_decoder_checked : recurrence_43_D*recurrence_43_X=1 := by decide +kernel
theorem recurrence_43_complete : Submodule.span ℚ (Set.range recurrence_43_B)=GeneratedOperatorAlgebra.wordSpan recurrence_43_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_43_words j,recurrence_43_words_checked j⟩
  · intro i j
    rw [recurrence_43_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_44_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,2]]
def recurrence_44_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,2]]
def recurrence_44_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_44_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,2]]]
def recurrence_44_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,2]
def recurrence_44_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_44_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_44_G (recurrence_44_words j)=recurrence_44_B j := by decide +kernel
theorem recurrence_44_products_checked : ∀ j i, recurrence_44_G i*recurrence_44_B j=∑ t,(recurrence_44_C j i t) • recurrence_44_B t := by decide +kernel
theorem recurrence_44_decoder_checked : recurrence_44_D*recurrence_44_X=1 := by decide +kernel
theorem recurrence_44_complete : Submodule.span ℚ (Set.range recurrence_44_B)=GeneratedOperatorAlgebra.wordSpan recurrence_44_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_44_words j,recurrence_44_words_checked j⟩
  · intro i j
    rw [recurrence_44_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_45_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;-1,-1,3],!![0,0,1;-1,-1,3;-3,-4,8]]
def recurrence_45_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;-1,-1,3]]
def recurrence_45_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_45_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![-1,-1,3]]]
def recurrence_45_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,-1;1,0,-1;0,1,3;0,-1,-3;0,-1,-4;1,3,8]
def recurrence_45_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_45_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_45_G (recurrence_45_words j)=recurrence_45_B j := by decide +kernel
theorem recurrence_45_products_checked : ∀ j i, recurrence_45_G i*recurrence_45_B j=∑ t,(recurrence_45_C j i t) • recurrence_45_B t := by decide +kernel
theorem recurrence_45_decoder_checked : recurrence_45_D*recurrence_45_X=1 := by decide +kernel
theorem recurrence_45_complete : Submodule.span ℚ (Set.range recurrence_45_B)=GeneratedOperatorAlgebra.wordSpan recurrence_45_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_45_words j,recurrence_45_words_checked j⟩
  · intro i j
    rw [recurrence_45_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_46_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-8,8],!![0,0,1;1,-8,8;8,-63,56]]
def recurrence_46_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-8,8]]
def recurrence_46_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_46_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-8,8]]]
def recurrence_46_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-8;0,1,8;0,1,8;0,-8,-63;1,8,56]
def recurrence_46_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_46_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_46_G (recurrence_46_words j)=recurrence_46_B j := by decide +kernel
theorem recurrence_46_products_checked : ∀ j i, recurrence_46_G i*recurrence_46_B j=∑ t,(recurrence_46_C j i t) • recurrence_46_B t := by decide +kernel
theorem recurrence_46_decoder_checked : recurrence_46_D*recurrence_46_X=1 := by decide +kernel
theorem recurrence_46_complete : Submodule.span ℚ (Set.range recurrence_46_B)=GeneratedOperatorAlgebra.wordSpan recurrence_46_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_46_words j,recurrence_46_words_checked j⟩
  · intro i j
    rw [recurrence_46_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_47_B : Fin 6 → Matrix (Fin 6) (Fin 6) ℚ := ![!![1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1],!![0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0],!![0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0;0,-1,0,0,38,0],!![0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0;0,-1,0,0,38,0;0,0,-1,0,0,38],!![0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0;0,-1,0,0,38,0;0,0,-1,0,0,38;-38,0,0,1443,0,0],!![0,0,0,0,0,1;-1,0,0,38,0,0;0,-1,0,0,38,0;0,0,-1,0,0,38;-38,0,0,1443,0,0;0,-38,0,0,1443,0]]
def recurrence_47_G : Fin 1 → Matrix (Fin 6) (Fin 6) ℚ := ![!![0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0]]
def recurrence_47_words : Fin 6 → List (Fin 1) := ![[],[0],[0,0],[0,0,0],[0,0,0,0],[0,0,0,0,0]]
def recurrence_47_C : Fin 6 → Fin 1 → Fin 6 → ℚ := ![![![0,1,0,0,0,0]],![![0,0,1,0,0,0]],![![0,0,0,1,0,0]],![![0,0,0,0,1,0]],![![0,0,0,0,0,1]],![![-1,0,0,38,0,0]]]
def recurrence_47_X : Matrix (Fin 36) (Fin 6) ℚ := !![1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;0,0,0,0,0,-1;1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,38;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,-1,0;0,0,0,0,0,-1;1,0,0,0,0,0;0,1,0,0,38,0;0,0,1,0,0,38;0,0,0,1,0,0;0,0,0,-1,0,0;0,0,0,0,-1,0;0,0,0,0,0,-1;1,0,0,38,0,0;0,1,0,0,38,0;0,0,1,0,0,38;0,0,-1,0,0,-38;0,0,0,-1,0,0;0,0,0,0,-1,0;0,0,38,0,0,1443;1,0,0,38,0,0;0,1,0,0,38,0;0,-1,0,0,-38,0;0,0,-1,0,0,-38;0,0,0,-1,0,0;0,38,0,0,1443,0;0,0,38,0,0,1443;1,0,0,38,0,0]
def recurrence_47_D : Matrix (Fin 6) (Fin 36) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_47_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_47_G (recurrence_47_words j)=recurrence_47_B j := by decide +kernel
theorem recurrence_47_products_checked : ∀ j i, recurrence_47_G i*recurrence_47_B j=∑ t,(recurrence_47_C j i t) • recurrence_47_B t := by decide +kernel
theorem recurrence_47_decoder_checked : recurrence_47_D*recurrence_47_X=1 := by decide +kernel
theorem recurrence_47_complete : Submodule.span ℚ (Set.range recurrence_47_B)=GeneratedOperatorAlgebra.wordSpan recurrence_47_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_47_words j,recurrence_47_words_checked j⟩
  · intro i j
    rw [recurrence_47_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_48_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,4]]
def recurrence_48_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,4]]
def recurrence_48_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_48_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,4]]]
def recurrence_48_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,4]
def recurrence_48_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_48_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_48_G (recurrence_48_words j)=recurrence_48_B j := by decide +kernel
theorem recurrence_48_products_checked : ∀ j i, recurrence_48_G i*recurrence_48_B j=∑ t,(recurrence_48_C j i t) • recurrence_48_B t := by decide +kernel
theorem recurrence_48_decoder_checked : recurrence_48_D*recurrence_48_X=1 := by decide +kernel
theorem recurrence_48_complete : Submodule.span ℚ (Set.range recurrence_48_B)=GeneratedOperatorAlgebra.wordSpan recurrence_48_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_48_words j,recurrence_48_words_checked j⟩
  · intro i j
    rw [recurrence_48_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_49_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,2],!![0,0,1;0,1,2;0,2,5]]
def recurrence_49_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,2]]
def recurrence_49_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_49_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,2]]]
def recurrence_49_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,2;0,0,0;0,1,2;1,2,5]
def recurrence_49_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_49_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_49_G (recurrence_49_words j)=recurrence_49_B j := by decide +kernel
theorem recurrence_49_products_checked : ∀ j i, recurrence_49_G i*recurrence_49_B j=∑ t,(recurrence_49_C j i t) • recurrence_49_B t := by decide +kernel
theorem recurrence_49_decoder_checked : recurrence_49_D*recurrence_49_X=1 := by decide +kernel
theorem recurrence_49_complete : Submodule.span ℚ (Set.range recurrence_49_B)=GeneratedOperatorAlgebra.wordSpan recurrence_49_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_49_words j,recurrence_49_words_checked j⟩
  · intro i j
    rw [recurrence_49_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
