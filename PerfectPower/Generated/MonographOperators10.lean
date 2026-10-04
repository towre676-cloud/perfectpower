import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_100_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-7,7],!![0,0,1;1,-7,7;7,-48,42]]
def recurrence_100_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-7,7]]
def recurrence_100_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_100_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-7,7]]]
def recurrence_100_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-7;0,1,7;0,1,7;0,-7,-48;1,7,42]
def recurrence_100_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_100_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_100_G (recurrence_100_words j)=recurrence_100_B j := by decide +kernel
theorem recurrence_100_products_checked : ∀ j i, recurrence_100_G i*recurrence_100_B j=∑ t,(recurrence_100_C j i t) • recurrence_100_B t := by decide +kernel
theorem recurrence_100_decoder_checked : recurrence_100_D*recurrence_100_X=1 := by decide +kernel
theorem recurrence_100_complete : Submodule.span ℚ (Set.range recurrence_100_B)=GeneratedOperatorAlgebra.wordSpan recurrence_100_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_100_words j,recurrence_100_words_checked j⟩
  · intro i j
    rw [recurrence_100_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_101_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-7,7],!![0,0,1;1,-7,7;7,-48,42]]
def recurrence_101_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-7,7]]
def recurrence_101_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_101_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-7,7]]]
def recurrence_101_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-7;0,1,7;0,1,7;0,-7,-48;1,7,42]
def recurrence_101_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_101_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_101_G (recurrence_101_words j)=recurrence_101_B j := by decide +kernel
theorem recurrence_101_products_checked : ∀ j i, recurrence_101_G i*recurrence_101_B j=∑ t,(recurrence_101_C j i t) • recurrence_101_B t := by decide +kernel
theorem recurrence_101_decoder_checked : recurrence_101_D*recurrence_101_X=1 := by decide +kernel
theorem recurrence_101_complete : Submodule.span ℚ (Set.range recurrence_101_B)=GeneratedOperatorAlgebra.wordSpan recurrence_101_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_101_words j,recurrence_101_words_checked j⟩
  · intro i j
    rw [recurrence_101_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_102_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_102_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_102_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_102_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_102_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_102_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_102_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_102_G (recurrence_102_words j)=recurrence_102_B j := by decide +kernel
theorem recurrence_102_products_checked : ∀ j i, recurrence_102_G i*recurrence_102_B j=∑ t,(recurrence_102_C j i t) • recurrence_102_B t := by decide +kernel
theorem recurrence_102_decoder_checked : recurrence_102_D*recurrence_102_X=1 := by decide +kernel
theorem recurrence_102_complete : Submodule.span ℚ (Set.range recurrence_102_B)=GeneratedOperatorAlgebra.wordSpan recurrence_102_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_102_words j,recurrence_102_words_checked j⟩
  · intro i j
    rw [recurrence_102_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_103_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,3]]
def recurrence_103_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,3]]
def recurrence_103_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_103_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,3]]]
def recurrence_103_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,3]
def recurrence_103_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_103_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_103_G (recurrence_103_words j)=recurrence_103_B j := by decide +kernel
theorem recurrence_103_products_checked : ∀ j i, recurrence_103_G i*recurrence_103_B j=∑ t,(recurrence_103_C j i t) • recurrence_103_B t := by decide +kernel
theorem recurrence_103_decoder_checked : recurrence_103_D*recurrence_103_X=1 := by decide +kernel
theorem recurrence_103_complete : Submodule.span ℚ (Set.range recurrence_103_B)=GeneratedOperatorAlgebra.wordSpan recurrence_103_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_103_words j,recurrence_103_words_checked j⟩
  · intro i j
    rw [recurrence_103_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_104_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,14]]
def recurrence_104_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,14]]
def recurrence_104_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_104_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,14]]]
def recurrence_104_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,14]
def recurrence_104_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_104_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_104_G (recurrence_104_words j)=recurrence_104_B j := by decide +kernel
theorem recurrence_104_products_checked : ∀ j i, recurrence_104_G i*recurrence_104_B j=∑ t,(recurrence_104_C j i t) • recurrence_104_B t := by decide +kernel
theorem recurrence_104_decoder_checked : recurrence_104_D*recurrence_104_X=1 := by decide +kernel
theorem recurrence_104_complete : Submodule.span ℚ (Set.range recurrence_104_B)=GeneratedOperatorAlgebra.wordSpan recurrence_104_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_104_words j,recurrence_104_words_checked j⟩
  · intro i j
    rw [recurrence_104_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_105_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,-1,3],!![0,0,1;0,-1,3;0,-3,8]]
def recurrence_105_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,-1,3]]
def recurrence_105_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_105_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,-1,3]]]
def recurrence_105_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,-1;0,1,3;0,0,0;0,-1,-3;1,3,8]
def recurrence_105_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_105_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_105_G (recurrence_105_words j)=recurrence_105_B j := by decide +kernel
theorem recurrence_105_products_checked : ∀ j i, recurrence_105_G i*recurrence_105_B j=∑ t,(recurrence_105_C j i t) • recurrence_105_B t := by decide +kernel
theorem recurrence_105_decoder_checked : recurrence_105_D*recurrence_105_X=1 := by decide +kernel
theorem recurrence_105_complete : Submodule.span ℚ (Set.range recurrence_105_B)=GeneratedOperatorAlgebra.wordSpan recurrence_105_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_105_words j,recurrence_105_words_checked j⟩
  · intro i j
    rw [recurrence_105_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_106_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,1],!![0,0,1;0,1,1;0,1,2]]
def recurrence_106_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,1]]
def recurrence_106_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_106_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,1]]]
def recurrence_106_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,1;0,0,0;0,1,1;1,1,2]
def recurrence_106_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_106_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_106_G (recurrence_106_words j)=recurrence_106_B j := by decide +kernel
theorem recurrence_106_products_checked : ∀ j i, recurrence_106_G i*recurrence_106_B j=∑ t,(recurrence_106_C j i t) • recurrence_106_B t := by decide +kernel
theorem recurrence_106_decoder_checked : recurrence_106_D*recurrence_106_X=1 := by decide +kernel
theorem recurrence_106_complete : Submodule.span ℚ (Set.range recurrence_106_B)=GeneratedOperatorAlgebra.wordSpan recurrence_106_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_106_words j,recurrence_106_words_checked j⟩
  · intro i j
    rw [recurrence_106_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_107_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,22]]
def recurrence_107_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,22]]
def recurrence_107_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_107_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,22]]]
def recurrence_107_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,22]
def recurrence_107_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_107_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_107_G (recurrence_107_words j)=recurrence_107_B j := by decide +kernel
theorem recurrence_107_products_checked : ∀ j i, recurrence_107_G i*recurrence_107_B j=∑ t,(recurrence_107_C j i t) • recurrence_107_B t := by decide +kernel
theorem recurrence_107_decoder_checked : recurrence_107_D*recurrence_107_X=1 := by decide +kernel
theorem recurrence_107_complete : Submodule.span ℚ (Set.range recurrence_107_B)=GeneratedOperatorAlgebra.wordSpan recurrence_107_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_107_words j,recurrence_107_words_checked j⟩
  · intro i j
    rw [recurrence_107_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_108_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,6,0],!![0,0,1,0;0,0,0,1;-1,0,6,0;0,-1,0,6],!![0,0,0,1;-1,0,6,0;0,-1,0,6;-6,0,35,0]]
def recurrence_108_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,6,0]]
def recurrence_108_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_108_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![-1,0,6,0]]]
def recurrence_108_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,-1;1,0,0,0;0,1,0,6;0,0,1,0;0,0,-1,0;0,0,0,-1;1,0,6,0;0,1,0,6;0,-1,0,-6;0,0,-1,0;0,6,0,35;1,0,6,0]
def recurrence_108_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_108_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_108_G (recurrence_108_words j)=recurrence_108_B j := by decide +kernel
theorem recurrence_108_products_checked : ∀ j i, recurrence_108_G i*recurrence_108_B j=∑ t,(recurrence_108_C j i t) • recurrence_108_B t := by decide +kernel
theorem recurrence_108_decoder_checked : recurrence_108_D*recurrence_108_X=1 := by decide +kernel
theorem recurrence_108_complete : Submodule.span ℚ (Set.range recurrence_108_B)=GeneratedOperatorAlgebra.wordSpan recurrence_108_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_108_words j,recurrence_108_words_checked j⟩
  · intro i j
    rw [recurrence_108_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_109_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,-1,3],!![0,0,1;0,-1,3;0,-3,8]]
def recurrence_109_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,-1,3]]
def recurrence_109_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_109_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,-1,3]]]
def recurrence_109_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,-1;0,1,3;0,0,0;0,-1,-3;1,3,8]
def recurrence_109_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_109_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_109_G (recurrence_109_words j)=recurrence_109_B j := by decide +kernel
theorem recurrence_109_products_checked : ∀ j i, recurrence_109_G i*recurrence_109_B j=∑ t,(recurrence_109_C j i t) • recurrence_109_B t := by decide +kernel
theorem recurrence_109_decoder_checked : recurrence_109_D*recurrence_109_X=1 := by decide +kernel
theorem recurrence_109_complete : Submodule.span ℚ (Set.range recurrence_109_B)=GeneratedOperatorAlgebra.wordSpan recurrence_109_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_109_words j,recurrence_109_words_checked j⟩
  · intro i j
    rw [recurrence_109_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
