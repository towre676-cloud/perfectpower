import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_60_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,1],!![0,0,1;0,1,1;0,1,2]]
def recurrence_60_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,1]]
def recurrence_60_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_60_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,1]]]
def recurrence_60_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,1;0,0,0;0,1,1;1,1,2]
def recurrence_60_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_60_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_60_G (recurrence_60_words j)=recurrence_60_B j := by decide +kernel
theorem recurrence_60_products_checked : ∀ j i, recurrence_60_G i*recurrence_60_B j=∑ t,(recurrence_60_C j i t) • recurrence_60_B t := by decide +kernel
theorem recurrence_60_decoder_checked : recurrence_60_D*recurrence_60_X=1 := by decide +kernel
theorem recurrence_60_complete : Submodule.span ℚ (Set.range recurrence_60_B)=GeneratedOperatorAlgebra.wordSpan recurrence_60_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_60_words j,recurrence_60_words_checked j⟩
  · intro i j
    rw [recurrence_60_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_61_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,10,0],!![0,0,1,0;0,0,0,1;-1,0,10,0;0,-1,0,10],!![0,0,0,1;-1,0,10,0;0,-1,0,10;-10,0,99,0]]
def recurrence_61_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,10,0]]
def recurrence_61_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_61_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![-1,0,10,0]]]
def recurrence_61_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,-1;1,0,0,0;0,1,0,10;0,0,1,0;0,0,-1,0;0,0,0,-1;1,0,10,0;0,1,0,10;0,-1,0,-10;0,0,-1,0;0,10,0,99;1,0,10,0]
def recurrence_61_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_61_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_61_G (recurrence_61_words j)=recurrence_61_B j := by decide +kernel
theorem recurrence_61_products_checked : ∀ j i, recurrence_61_G i*recurrence_61_B j=∑ t,(recurrence_61_C j i t) • recurrence_61_B t := by decide +kernel
theorem recurrence_61_decoder_checked : recurrence_61_D*recurrence_61_X=1 := by decide +kernel
theorem recurrence_61_complete : Submodule.span ℚ (Set.range recurrence_61_B)=GeneratedOperatorAlgebra.wordSpan recurrence_61_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_61_words j,recurrence_61_words_checked j⟩
  · intro i j
    rw [recurrence_61_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_62_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,18]]
def recurrence_62_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,18]]
def recurrence_62_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_62_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,18]]]
def recurrence_62_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,18]
def recurrence_62_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_62_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_62_G (recurrence_62_words j)=recurrence_62_B j := by decide +kernel
theorem recurrence_62_products_checked : ∀ j i, recurrence_62_G i*recurrence_62_B j=∑ t,(recurrence_62_C j i t) • recurrence_62_B t := by decide +kernel
theorem recurrence_62_decoder_checked : recurrence_62_D*recurrence_62_X=1 := by decide +kernel
theorem recurrence_62_complete : Submodule.span ℚ (Set.range recurrence_62_B)=GeneratedOperatorAlgebra.wordSpan recurrence_62_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_62_words j,recurrence_62_words_checked j⟩
  · intro i j
    rw [recurrence_62_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_63_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,11]]
def recurrence_63_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,11]]
def recurrence_63_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_63_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,11]]]
def recurrence_63_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,11]
def recurrence_63_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_63_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_63_G (recurrence_63_words j)=recurrence_63_B j := by decide +kernel
theorem recurrence_63_products_checked : ∀ j i, recurrence_63_G i*recurrence_63_B j=∑ t,(recurrence_63_C j i t) • recurrence_63_B t := by decide +kernel
theorem recurrence_63_decoder_checked : recurrence_63_D*recurrence_63_X=1 := by decide +kernel
theorem recurrence_63_complete : Submodule.span ℚ (Set.range recurrence_63_B)=GeneratedOperatorAlgebra.wordSpan recurrence_63_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_63_words j,recurrence_63_words_checked j⟩
  · intro i j
    rw [recurrence_63_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_64_B : Fin 6 → Matrix (Fin 6) (Fin 6) ℚ := ![!![1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1],!![0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0],!![0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0;0,-1,0,0,38,0],!![0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0;0,-1,0,0,38,0;0,0,-1,0,0,38],!![0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0;0,-1,0,0,38,0;0,0,-1,0,0,38;-38,0,0,1443,0,0],!![0,0,0,0,0,1;-1,0,0,38,0,0;0,-1,0,0,38,0;0,0,-1,0,0,38;-38,0,0,1443,0,0;0,-38,0,0,1443,0]]
def recurrence_64_G : Fin 1 → Matrix (Fin 6) (Fin 6) ℚ := ![!![0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;-1,0,0,38,0,0]]
def recurrence_64_words : Fin 6 → List (Fin 1) := ![[],[0],[0,0],[0,0,0],[0,0,0,0],[0,0,0,0,0]]
def recurrence_64_C : Fin 6 → Fin 1 → Fin 6 → ℚ := ![![![0,1,0,0,0,0]],![![0,0,1,0,0,0]],![![0,0,0,1,0,0]],![![0,0,0,0,1,0]],![![0,0,0,0,0,1]],![![-1,0,0,38,0,0]]]
def recurrence_64_X : Matrix (Fin 36) (Fin 6) ℚ := !![1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,0;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,0,1;0,0,0,0,0,-1;1,0,0,0,0,0;0,1,0,0,0,0;0,0,1,0,0,38;0,0,0,1,0,0;0,0,0,0,1,0;0,0,0,0,-1,0;0,0,0,0,0,-1;1,0,0,0,0,0;0,1,0,0,38,0;0,0,1,0,0,38;0,0,0,1,0,0;0,0,0,-1,0,0;0,0,0,0,-1,0;0,0,0,0,0,-1;1,0,0,38,0,0;0,1,0,0,38,0;0,0,1,0,0,38;0,0,-1,0,0,-38;0,0,0,-1,0,0;0,0,0,0,-1,0;0,0,38,0,0,1443;1,0,0,38,0,0;0,1,0,0,38,0;0,-1,0,0,-38,0;0,0,-1,0,0,-38;0,0,0,-1,0,0;0,38,0,0,1443,0;0,0,38,0,0,1443;1,0,0,38,0,0]
def recurrence_64_D : Matrix (Fin 6) (Fin 36) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_64_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_64_G (recurrence_64_words j)=recurrence_64_B j := by decide +kernel
theorem recurrence_64_products_checked : ∀ j i, recurrence_64_G i*recurrence_64_B j=∑ t,(recurrence_64_C j i t) • recurrence_64_B t := by decide +kernel
theorem recurrence_64_decoder_checked : recurrence_64_D*recurrence_64_X=1 := by decide +kernel
theorem recurrence_64_complete : Submodule.span ℚ (Set.range recurrence_64_B)=GeneratedOperatorAlgebra.wordSpan recurrence_64_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_64_words j,recurrence_64_words_checked j⟩
  · intro i j
    rw [recurrence_64_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_65_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,20]]
def recurrence_65_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,20]]
def recurrence_65_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_65_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,20]]]
def recurrence_65_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,20]
def recurrence_65_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_65_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_65_G (recurrence_65_words j)=recurrence_65_B j := by decide +kernel
theorem recurrence_65_products_checked : ∀ j i, recurrence_65_G i*recurrence_65_B j=∑ t,(recurrence_65_C j i t) • recurrence_65_B t := by decide +kernel
theorem recurrence_65_decoder_checked : recurrence_65_D*recurrence_65_X=1 := by decide +kernel
theorem recurrence_65_complete : Submodule.span ℚ (Set.range recurrence_65_B)=GeneratedOperatorAlgebra.wordSpan recurrence_65_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_65_words j,recurrence_65_words_checked j⟩
  · intro i j
    rw [recurrence_65_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_66_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,6]]
def recurrence_66_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,6]]
def recurrence_66_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_66_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,6]]]
def recurrence_66_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,6]
def recurrence_66_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_66_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_66_G (recurrence_66_words j)=recurrence_66_B j := by decide +kernel
theorem recurrence_66_products_checked : ∀ j i, recurrence_66_G i*recurrence_66_B j=∑ t,(recurrence_66_C j i t) • recurrence_66_B t := by decide +kernel
theorem recurrence_66_decoder_checked : recurrence_66_D*recurrence_66_X=1 := by decide +kernel
theorem recurrence_66_complete : Submodule.span ℚ (Set.range recurrence_66_B)=GeneratedOperatorAlgebra.wordSpan recurrence_66_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_66_words j,recurrence_66_words_checked j⟩
  · intro i j
    rw [recurrence_66_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_67_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,20]]
def recurrence_67_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,20]]
def recurrence_67_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_67_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,20]]]
def recurrence_67_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,20]
def recurrence_67_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_67_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_67_G (recurrence_67_words j)=recurrence_67_B j := by decide +kernel
theorem recurrence_67_products_checked : ∀ j i, recurrence_67_G i*recurrence_67_B j=∑ t,(recurrence_67_C j i t) • recurrence_67_B t := by decide +kernel
theorem recurrence_67_decoder_checked : recurrence_67_D*recurrence_67_X=1 := by decide +kernel
theorem recurrence_67_complete : Submodule.span ℚ (Set.range recurrence_67_B)=GeneratedOperatorAlgebra.wordSpan recurrence_67_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_67_words j,recurrence_67_words_checked j⟩
  · intro i j
    rw [recurrence_67_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_68_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,20]]
def recurrence_68_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,20]]
def recurrence_68_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_68_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,20]]]
def recurrence_68_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,20]
def recurrence_68_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_68_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_68_G (recurrence_68_words j)=recurrence_68_B j := by decide +kernel
theorem recurrence_68_products_checked : ∀ j i, recurrence_68_G i*recurrence_68_B j=∑ t,(recurrence_68_C j i t) • recurrence_68_B t := by decide +kernel
theorem recurrence_68_decoder_checked : recurrence_68_D*recurrence_68_X=1 := by decide +kernel
theorem recurrence_68_complete : Submodule.span ℚ (Set.range recurrence_68_B)=GeneratedOperatorAlgebra.wordSpan recurrence_68_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_68_words j,recurrence_68_words_checked j⟩
  · intro i j
    rw [recurrence_68_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_69_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,6]]
def recurrence_69_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,6]]
def recurrence_69_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_69_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,6]]]
def recurrence_69_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,6]
def recurrence_69_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_69_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_69_G (recurrence_69_words j)=recurrence_69_B j := by decide +kernel
theorem recurrence_69_products_checked : ∀ j i, recurrence_69_G i*recurrence_69_B j=∑ t,(recurrence_69_C j i t) • recurrence_69_B t := by decide +kernel
theorem recurrence_69_decoder_checked : recurrence_69_D*recurrence_69_X=1 := by decide +kernel
theorem recurrence_69_complete : Submodule.span ℚ (Set.range recurrence_69_B)=GeneratedOperatorAlgebra.wordSpan recurrence_69_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_69_words j,recurrence_69_words_checked j⟩
  · intro i j
    rw [recurrence_69_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
