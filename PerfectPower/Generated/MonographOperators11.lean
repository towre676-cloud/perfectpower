import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_110_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,6,0],!![0,0,1,0;0,0,0,1;-1,0,6,0;0,-1,0,6],!![0,0,0,1;-1,0,6,0;0,-1,0,6;-6,0,35,0]]
def recurrence_110_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,6,0]]
def recurrence_110_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_110_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![-1,0,6,0]]]
def recurrence_110_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,-1;1,0,0,0;0,1,0,6;0,0,1,0;0,0,-1,0;0,0,0,-1;1,0,6,0;0,1,0,6;0,-1,0,-6;0,0,-1,0;0,6,0,35;1,0,6,0]
def recurrence_110_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_110_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_110_G (recurrence_110_words j)=recurrence_110_B j := by decide +kernel
theorem recurrence_110_products_checked : ∀ j i, recurrence_110_G i*recurrence_110_B j=∑ t,(recurrence_110_C j i t) • recurrence_110_B t := by decide +kernel
theorem recurrence_110_decoder_checked : recurrence_110_D*recurrence_110_X=1 := by decide +kernel
theorem recurrence_110_complete : Submodule.span ℚ (Set.range recurrence_110_B)=GeneratedOperatorAlgebra.wordSpan recurrence_110_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_110_words j,recurrence_110_words_checked j⟩
  · intro i j
    rw [recurrence_110_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_111_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,2]]
def recurrence_111_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,2]]
def recurrence_111_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_111_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,2]]]
def recurrence_111_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,2]
def recurrence_111_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_111_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_111_G (recurrence_111_words j)=recurrence_111_B j := by decide +kernel
theorem recurrence_111_products_checked : ∀ j i, recurrence_111_G i*recurrence_111_B j=∑ t,(recurrence_111_C j i t) • recurrence_111_B t := by decide +kernel
theorem recurrence_111_decoder_checked : recurrence_111_D*recurrence_111_X=1 := by decide +kernel
theorem recurrence_111_complete : Submodule.span ℚ (Set.range recurrence_111_B)=GeneratedOperatorAlgebra.wordSpan recurrence_111_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_111_words j,recurrence_111_words_checked j⟩
  · intro i j
    rw [recurrence_111_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_112_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1],!![0,0,1,0;0,0,0,1;0,0,1,1;0,0,1,2],!![0,0,0,1;0,0,1,1;0,0,1,2;0,0,2,3]]
def recurrence_112_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1]]
def recurrence_112_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_112_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,0,1,1]]]
def recurrence_112_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,0;0,1,0,1;0,0,1,1;0,0,0,0;0,0,0,0;1,0,1,1;0,1,1,2;0,0,0,0;0,0,0,0;0,1,1,2;1,1,2,3]
def recurrence_112_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_112_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_112_G (recurrence_112_words j)=recurrence_112_B j := by decide +kernel
theorem recurrence_112_products_checked : ∀ j i, recurrence_112_G i*recurrence_112_B j=∑ t,(recurrence_112_C j i t) • recurrence_112_B t := by decide +kernel
theorem recurrence_112_decoder_checked : recurrence_112_D*recurrence_112_X=1 := by decide +kernel
theorem recurrence_112_complete : Submodule.span ℚ (Set.range recurrence_112_B)=GeneratedOperatorAlgebra.wordSpan recurrence_112_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_112_words j,recurrence_112_words_checked j⟩
  · intro i j
    rw [recurrence_112_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_113_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1],!![0,0,1,0;0,0,0,1;0,0,1,1;0,0,1,2],!![0,0,0,1;0,0,1,1;0,0,1,2;0,0,2,3]]
def recurrence_113_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1]]
def recurrence_113_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_113_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,0,1,1]]]
def recurrence_113_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,0;0,1,0,1;0,0,1,1;0,0,0,0;0,0,0,0;1,0,1,1;0,1,1,2;0,0,0,0;0,0,0,0;0,1,1,2;1,1,2,3]
def recurrence_113_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_113_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_113_G (recurrence_113_words j)=recurrence_113_B j := by decide +kernel
theorem recurrence_113_products_checked : ∀ j i, recurrence_113_G i*recurrence_113_B j=∑ t,(recurrence_113_C j i t) • recurrence_113_B t := by decide +kernel
theorem recurrence_113_decoder_checked : recurrence_113_D*recurrence_113_X=1 := by decide +kernel
theorem recurrence_113_complete : Submodule.span ℚ (Set.range recurrence_113_B)=GeneratedOperatorAlgebra.wordSpan recurrence_113_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_113_words j,recurrence_113_words_checked j⟩
  · intro i j
    rw [recurrence_113_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_114_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;-1,-1,3],!![0,0,1;-1,-1,3;-3,-4,8]]
def recurrence_114_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;-1,-1,3]]
def recurrence_114_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_114_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![-1,-1,3]]]
def recurrence_114_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,-1;1,0,-1;0,1,3;0,-1,-3;0,-1,-4;1,3,8]
def recurrence_114_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_114_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_114_G (recurrence_114_words j)=recurrence_114_B j := by decide +kernel
theorem recurrence_114_products_checked : ∀ j i, recurrence_114_G i*recurrence_114_B j=∑ t,(recurrence_114_C j i t) • recurrence_114_B t := by decide +kernel
theorem recurrence_114_decoder_checked : recurrence_114_D*recurrence_114_X=1 := by decide +kernel
theorem recurrence_114_complete : Submodule.span ℚ (Set.range recurrence_114_B)=GeneratedOperatorAlgebra.wordSpan recurrence_114_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_114_words j,recurrence_114_words_checked j⟩
  · intro i j
    rw [recurrence_114_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_115_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,2],!![0,0,1;0,1,2;0,2,5]]
def recurrence_115_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,2]]
def recurrence_115_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_115_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,2]]]
def recurrence_115_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,2;0,0,0;0,1,2;1,2,5]
def recurrence_115_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_115_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_115_G (recurrence_115_words j)=recurrence_115_B j := by decide +kernel
theorem recurrence_115_products_checked : ∀ j i, recurrence_115_G i*recurrence_115_B j=∑ t,(recurrence_115_C j i t) • recurrence_115_B t := by decide +kernel
theorem recurrence_115_decoder_checked : recurrence_115_D*recurrence_115_X=1 := by decide +kernel
theorem recurrence_115_complete : Submodule.span ℚ (Set.range recurrence_115_B)=GeneratedOperatorAlgebra.wordSpan recurrence_115_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_115_words j,recurrence_115_words_checked j⟩
  · intro i j
    rw [recurrence_115_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_116_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-7,7],!![0,0,1;1,-7,7;7,-48,42]]
def recurrence_116_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-7,7]]
def recurrence_116_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_116_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-7,7]]]
def recurrence_116_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-7;0,1,7;0,1,7;0,-7,-48;1,7,42]
def recurrence_116_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_116_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_116_G (recurrence_116_words j)=recurrence_116_B j := by decide +kernel
theorem recurrence_116_products_checked : ∀ j i, recurrence_116_G i*recurrence_116_B j=∑ t,(recurrence_116_C j i t) • recurrence_116_B t := by decide +kernel
theorem recurrence_116_decoder_checked : recurrence_116_D*recurrence_116_X=1 := by decide +kernel
theorem recurrence_116_complete : Submodule.span ℚ (Set.range recurrence_116_B)=GeneratedOperatorAlgebra.wordSpan recurrence_116_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_116_words j,recurrence_116_words_checked j⟩
  · intro i j
    rw [recurrence_116_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_117_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,14]]
def recurrence_117_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,14]]
def recurrence_117_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_117_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,14]]]
def recurrence_117_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,14]
def recurrence_117_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_117_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_117_G (recurrence_117_words j)=recurrence_117_B j := by decide +kernel
theorem recurrence_117_products_checked : ∀ j i, recurrence_117_G i*recurrence_117_B j=∑ t,(recurrence_117_C j i t) • recurrence_117_B t := by decide +kernel
theorem recurrence_117_decoder_checked : recurrence_117_D*recurrence_117_X=1 := by decide +kernel
theorem recurrence_117_complete : Submodule.span ℚ (Set.range recurrence_117_B)=GeneratedOperatorAlgebra.wordSpan recurrence_117_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_117_words j,recurrence_117_words_checked j⟩
  · intro i j
    rw [recurrence_117_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_118_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,4]]
def recurrence_118_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,4]]
def recurrence_118_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_118_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,4]]]
def recurrence_118_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,4]
def recurrence_118_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_118_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_118_G (recurrence_118_words j)=recurrence_118_B j := by decide +kernel
theorem recurrence_118_products_checked : ∀ j i, recurrence_118_G i*recurrence_118_B j=∑ t,(recurrence_118_C j i t) • recurrence_118_B t := by decide +kernel
theorem recurrence_118_decoder_checked : recurrence_118_D*recurrence_118_X=1 := by decide +kernel
theorem recurrence_118_complete : Submodule.span ℚ (Set.range recurrence_118_B)=GeneratedOperatorAlgebra.wordSpan recurrence_118_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_118_words j,recurrence_118_words_checked j⟩
  · intro i j
    rw [recurrence_118_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_119_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,1],!![0,0,1;0,1,1;0,1,2]]
def recurrence_119_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,1]]
def recurrence_119_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_119_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,1]]]
def recurrence_119_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,1;0,0,0;0,1,1;1,1,2]
def recurrence_119_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_119_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_119_G (recurrence_119_words j)=recurrence_119_B j := by decide +kernel
theorem recurrence_119_products_checked : ∀ j i, recurrence_119_G i*recurrence_119_B j=∑ t,(recurrence_119_C j i t) • recurrence_119_B t := by decide +kernel
theorem recurrence_119_decoder_checked : recurrence_119_D*recurrence_119_X=1 := by decide +kernel
theorem recurrence_119_complete : Submodule.span ℚ (Set.range recurrence_119_B)=GeneratedOperatorAlgebra.wordSpan recurrence_119_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_119_words j,recurrence_119_words_checked j⟩
  · intro i j
    rw [recurrence_119_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
