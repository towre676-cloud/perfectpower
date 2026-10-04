import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_90_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;-1,-1,3],!![0,0,1;-1,-1,3;-3,-4,8]]
def recurrence_90_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;-1,-1,3]]
def recurrence_90_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_90_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![-1,-1,3]]]
def recurrence_90_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,-1;1,0,-1;0,1,3;0,-1,-3;0,-1,-4;1,3,8]
def recurrence_90_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_90_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_90_G (recurrence_90_words j)=recurrence_90_B j := by decide +kernel
theorem recurrence_90_products_checked : ∀ j i, recurrence_90_G i*recurrence_90_B j=∑ t,(recurrence_90_C j i t) • recurrence_90_B t := by decide +kernel
theorem recurrence_90_decoder_checked : recurrence_90_D*recurrence_90_X=1 := by decide +kernel
theorem recurrence_90_complete : Submodule.span ℚ (Set.range recurrence_90_B)=GeneratedOperatorAlgebra.wordSpan recurrence_90_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_90_words j,recurrence_90_words_checked j⟩
  · intro i j
    rw [recurrence_90_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_91_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_91_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_91_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_91_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_91_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_91_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_91_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_91_G (recurrence_91_words j)=recurrence_91_B j := by decide +kernel
theorem recurrence_91_products_checked : ∀ j i, recurrence_91_G i*recurrence_91_B j=∑ t,(recurrence_91_C j i t) • recurrence_91_B t := by decide +kernel
theorem recurrence_91_decoder_checked : recurrence_91_D*recurrence_91_X=1 := by decide +kernel
theorem recurrence_91_complete : Submodule.span ℚ (Set.range recurrence_91_B)=GeneratedOperatorAlgebra.wordSpan recurrence_91_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_91_words j,recurrence_91_words_checked j⟩
  · intro i j
    rw [recurrence_91_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_92_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,-1,3],!![0,0,1,0;0,0,0,1;0,0,-1,3;0,0,-3,8],!![0,0,0,1;0,0,-1,3;0,0,-3,8;0,0,-8,21]]
def recurrence_92_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,-1,3]]
def recurrence_92_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_92_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,0,-1,3]]]
def recurrence_92_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,0;0,1,0,-1;0,0,1,3;0,0,0,0;0,0,0,0;1,0,-1,-3;0,1,3,8;0,0,0,0;0,0,0,0;0,-1,-3,-8;1,3,8,21]
def recurrence_92_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_92_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_92_G (recurrence_92_words j)=recurrence_92_B j := by decide +kernel
theorem recurrence_92_products_checked : ∀ j i, recurrence_92_G i*recurrence_92_B j=∑ t,(recurrence_92_C j i t) • recurrence_92_B t := by decide +kernel
theorem recurrence_92_decoder_checked : recurrence_92_D*recurrence_92_X=1 := by decide +kernel
theorem recurrence_92_complete : Submodule.span ℚ (Set.range recurrence_92_B)=GeneratedOperatorAlgebra.wordSpan recurrence_92_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_92_words j,recurrence_92_words_checked j⟩
  · intro i j
    rw [recurrence_92_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_93_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,14]]
def recurrence_93_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,14]]
def recurrence_93_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_93_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,14]]]
def recurrence_93_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,14]
def recurrence_93_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_93_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_93_G (recurrence_93_words j)=recurrence_93_B j := by decide +kernel
theorem recurrence_93_products_checked : ∀ j i, recurrence_93_G i*recurrence_93_B j=∑ t,(recurrence_93_C j i t) • recurrence_93_B t := by decide +kernel
theorem recurrence_93_decoder_checked : recurrence_93_D*recurrence_93_X=1 := by decide +kernel
theorem recurrence_93_complete : Submodule.span ℚ (Set.range recurrence_93_B)=GeneratedOperatorAlgebra.wordSpan recurrence_93_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_93_words j,recurrence_93_words_checked j⟩
  · intro i j
    rw [recurrence_93_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_94_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-15,15],!![0,0,1;1,-15,15;15,-224,210]]
def recurrence_94_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-15,15]]
def recurrence_94_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_94_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-15,15]]]
def recurrence_94_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-15;0,1,15;0,1,15;0,-15,-224;1,15,210]
def recurrence_94_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_94_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_94_G (recurrence_94_words j)=recurrence_94_B j := by decide +kernel
theorem recurrence_94_products_checked : ∀ j i, recurrence_94_G i*recurrence_94_B j=∑ t,(recurrence_94_C j i t) • recurrence_94_B t := by decide +kernel
theorem recurrence_94_decoder_checked : recurrence_94_D*recurrence_94_X=1 := by decide +kernel
theorem recurrence_94_complete : Submodule.span ℚ (Set.range recurrence_94_B)=GeneratedOperatorAlgebra.wordSpan recurrence_94_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_94_words j,recurrence_94_words_checked j⟩
  · intro i j
    rw [recurrence_94_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_95_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-35,35],!![0,0,1;1,-35,35;35,-1224,1190]]
def recurrence_95_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-35,35]]
def recurrence_95_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_95_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-35,35]]]
def recurrence_95_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-35;0,1,35;0,1,35;0,-35,-1224;1,35,1190]
def recurrence_95_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_95_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_95_G (recurrence_95_words j)=recurrence_95_B j := by decide +kernel
theorem recurrence_95_products_checked : ∀ j i, recurrence_95_G i*recurrence_95_B j=∑ t,(recurrence_95_C j i t) • recurrence_95_B t := by decide +kernel
theorem recurrence_95_decoder_checked : recurrence_95_D*recurrence_95_X=1 := by decide +kernel
theorem recurrence_95_complete : Submodule.span ℚ (Set.range recurrence_95_B)=GeneratedOperatorAlgebra.wordSpan recurrence_95_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_95_words j,recurrence_95_words_checked j⟩
  · intro i j
    rw [recurrence_95_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_96_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,-1,14],!![0,0,1;0,-1,14;0,-14,195]]
def recurrence_96_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,-1,14]]
def recurrence_96_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_96_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,-1,14]]]
def recurrence_96_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,-1;0,1,14;0,0,0;0,-1,-14;1,14,195]
def recurrence_96_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_96_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_96_G (recurrence_96_words j)=recurrence_96_B j := by decide +kernel
theorem recurrence_96_products_checked : ∀ j i, recurrence_96_G i*recurrence_96_B j=∑ t,(recurrence_96_C j i t) • recurrence_96_B t := by decide +kernel
theorem recurrence_96_decoder_checked : recurrence_96_D*recurrence_96_X=1 := by decide +kernel
theorem recurrence_96_complete : Submodule.span ℚ (Set.range recurrence_96_B)=GeneratedOperatorAlgebra.wordSpan recurrence_96_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_96_words j,recurrence_96_words_checked j⟩
  · intro i j
    rw [recurrence_96_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_97_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-15,15],!![0,0,1;1,-15,15;15,-224,210]]
def recurrence_97_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-15,15]]
def recurrence_97_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_97_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-15,15]]]
def recurrence_97_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-15;0,1,15;0,1,15;0,-15,-224;1,15,210]
def recurrence_97_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_97_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_97_G (recurrence_97_words j)=recurrence_97_B j := by decide +kernel
theorem recurrence_97_products_checked : ∀ j i, recurrence_97_G i*recurrence_97_B j=∑ t,(recurrence_97_C j i t) • recurrence_97_B t := by decide +kernel
theorem recurrence_97_decoder_checked : recurrence_97_D*recurrence_97_X=1 := by decide +kernel
theorem recurrence_97_complete : Submodule.span ℚ (Set.range recurrence_97_B)=GeneratedOperatorAlgebra.wordSpan recurrence_97_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_97_words j,recurrence_97_words_checked j⟩
  · intro i j
    rw [recurrence_97_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_98_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,14,0],!![0,0,1,0;0,0,0,1;-1,0,14,0;0,-1,0,14],!![0,0,0,1;-1,0,14,0;0,-1,0,14;-14,0,195,0]]
def recurrence_98_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,14,0]]
def recurrence_98_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_98_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![-1,0,14,0]]]
def recurrence_98_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,-1;1,0,0,0;0,1,0,14;0,0,1,0;0,0,-1,0;0,0,0,-1;1,0,14,0;0,1,0,14;0,-1,0,-14;0,0,-1,0;0,14,0,195;1,0,14,0]
def recurrence_98_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_98_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_98_G (recurrence_98_words j)=recurrence_98_B j := by decide +kernel
theorem recurrence_98_products_checked : ∀ j i, recurrence_98_G i*recurrence_98_B j=∑ t,(recurrence_98_C j i t) • recurrence_98_B t := by decide +kernel
theorem recurrence_98_decoder_checked : recurrence_98_D*recurrence_98_X=1 := by decide +kernel
theorem recurrence_98_complete : Submodule.span ℚ (Set.range recurrence_98_B)=GeneratedOperatorAlgebra.wordSpan recurrence_98_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_98_words j,recurrence_98_words_checked j⟩
  · intro i j
    rw [recurrence_98_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_99_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,-1,3],!![0,0,1;0,-1,3;0,-3,8]]
def recurrence_99_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,-1,3]]
def recurrence_99_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_99_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,-1,3]]]
def recurrence_99_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,-1;0,1,3;0,0,0;0,-1,-3;1,3,8]
def recurrence_99_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_99_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_99_G (recurrence_99_words j)=recurrence_99_B j := by decide +kernel
theorem recurrence_99_products_checked : ∀ j i, recurrence_99_G i*recurrence_99_B j=∑ t,(recurrence_99_C j i t) • recurrence_99_B t := by decide +kernel
theorem recurrence_99_decoder_checked : recurrence_99_D*recurrence_99_X=1 := by decide +kernel
theorem recurrence_99_complete : Submodule.span ℚ (Set.range recurrence_99_B)=GeneratedOperatorAlgebra.wordSpan recurrence_99_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_99_words j,recurrence_99_words_checked j⟩
  · intro i j
    rw [recurrence_99_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
