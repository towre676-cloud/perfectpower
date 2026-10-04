import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_120_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_120_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_120_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_120_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_120_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_120_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_120_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_120_G (recurrence_120_words j)=recurrence_120_B j := by decide +kernel
theorem recurrence_120_products_checked : ∀ j i, recurrence_120_G i*recurrence_120_B j=∑ t,(recurrence_120_C j i t) • recurrence_120_B t := by decide +kernel
theorem recurrence_120_decoder_checked : recurrence_120_D*recurrence_120_X=1 := by decide +kernel
theorem recurrence_120_complete : Submodule.span ℚ (Set.range recurrence_120_B)=GeneratedOperatorAlgebra.wordSpan recurrence_120_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_120_words j,recurrence_120_words_checked j⟩
  · intro i j
    rw [recurrence_120_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_121_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,2],!![0,0,1;0,1,2;0,2,5]]
def recurrence_121_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,2]]
def recurrence_121_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_121_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,2]]]
def recurrence_121_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,2;0,0,0;0,1,2;1,2,5]
def recurrence_121_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_121_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_121_G (recurrence_121_words j)=recurrence_121_B j := by decide +kernel
theorem recurrence_121_products_checked : ∀ j i, recurrence_121_G i*recurrence_121_B j=∑ t,(recurrence_121_C j i t) • recurrence_121_B t := by decide +kernel
theorem recurrence_121_decoder_checked : recurrence_121_D*recurrence_121_X=1 := by decide +kernel
theorem recurrence_121_complete : Submodule.span ℚ (Set.range recurrence_121_B)=GeneratedOperatorAlgebra.wordSpan recurrence_121_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_121_words j,recurrence_121_words_checked j⟩
  · intro i j
    rw [recurrence_121_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_122_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,-1,3],!![0,0,1,0;0,0,0,1;0,0,-1,3;0,0,-3,8],!![0,0,0,1;0,0,-1,3;0,0,-3,8;0,0,-8,21]]
def recurrence_122_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,-1,3]]
def recurrence_122_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_122_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,0,-1,3]]]
def recurrence_122_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,0;0,1,0,-1;0,0,1,3;0,0,0,0;0,0,0,0;1,0,-1,-3;0,1,3,8;0,0,0,0;0,0,0,0;0,-1,-3,-8;1,3,8,21]
def recurrence_122_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_122_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_122_G (recurrence_122_words j)=recurrence_122_B j := by decide +kernel
theorem recurrence_122_products_checked : ∀ j i, recurrence_122_G i*recurrence_122_B j=∑ t,(recurrence_122_C j i t) • recurrence_122_B t := by decide +kernel
theorem recurrence_122_decoder_checked : recurrence_122_D*recurrence_122_X=1 := by decide +kernel
theorem recurrence_122_complete : Submodule.span ℚ (Set.range recurrence_122_B)=GeneratedOperatorAlgebra.wordSpan recurrence_122_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_122_words j,recurrence_122_words_checked j⟩
  · intro i j
    rw [recurrence_122_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_123_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,38]]
def recurrence_123_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,38]]
def recurrence_123_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_123_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,38]]]
def recurrence_123_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,38]
def recurrence_123_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_123_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_123_G (recurrence_123_words j)=recurrence_123_B j := by decide +kernel
theorem recurrence_123_products_checked : ∀ j i, recurrence_123_G i*recurrence_123_B j=∑ t,(recurrence_123_C j i t) • recurrence_123_B t := by decide +kernel
theorem recurrence_123_decoder_checked : recurrence_123_D*recurrence_123_X=1 := by decide +kernel
theorem recurrence_123_complete : Submodule.span ℚ (Set.range recurrence_123_B)=GeneratedOperatorAlgebra.wordSpan recurrence_123_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_123_words j,recurrence_123_words_checked j⟩
  · intro i j
    rw [recurrence_123_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_124_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,11]]
def recurrence_124_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,11]]
def recurrence_124_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_124_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,11]]]
def recurrence_124_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,11]
def recurrence_124_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_124_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_124_G (recurrence_124_words j)=recurrence_124_B j := by decide +kernel
theorem recurrence_124_products_checked : ∀ j i, recurrence_124_G i*recurrence_124_B j=∑ t,(recurrence_124_C j i t) • recurrence_124_B t := by decide +kernel
theorem recurrence_124_decoder_checked : recurrence_124_D*recurrence_124_X=1 := by decide +kernel
theorem recurrence_124_complete : Submodule.span ℚ (Set.range recurrence_124_B)=GeneratedOperatorAlgebra.wordSpan recurrence_124_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_124_words j,recurrence_124_words_checked j⟩
  · intro i j
    rw [recurrence_124_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_125_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,16]]
def recurrence_125_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,16]]
def recurrence_125_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_125_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,16]]]
def recurrence_125_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,16]
def recurrence_125_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_125_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_125_G (recurrence_125_words j)=recurrence_125_B j := by decide +kernel
theorem recurrence_125_products_checked : ∀ j i, recurrence_125_G i*recurrence_125_B j=∑ t,(recurrence_125_C j i t) • recurrence_125_B t := by decide +kernel
theorem recurrence_125_decoder_checked : recurrence_125_D*recurrence_125_X=1 := by decide +kernel
theorem recurrence_125_complete : Submodule.span ℚ (Set.range recurrence_125_B)=GeneratedOperatorAlgebra.wordSpan recurrence_125_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_125_words j,recurrence_125_words_checked j⟩
  · intro i j
    rw [recurrence_125_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_126_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,8]]
def recurrence_126_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,8]]
def recurrence_126_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_126_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,8]]]
def recurrence_126_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,8]
def recurrence_126_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_126_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_126_G (recurrence_126_words j)=recurrence_126_B j := by decide +kernel
theorem recurrence_126_products_checked : ∀ j i, recurrence_126_G i*recurrence_126_B j=∑ t,(recurrence_126_C j i t) • recurrence_126_B t := by decide +kernel
theorem recurrence_126_decoder_checked : recurrence_126_D*recurrence_126_X=1 := by decide +kernel
theorem recurrence_126_complete : Submodule.span ℚ (Set.range recurrence_126_B)=GeneratedOperatorAlgebra.wordSpan recurrence_126_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_126_words j,recurrence_126_words_checked j⟩
  · intro i j
    rw [recurrence_126_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_127_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,340,0],!![0,0,1,0;0,0,0,1;-1,0,340,0;0,-1,0,340],!![0,0,0,1;-1,0,340,0;0,-1,0,340;-340,0,115599,0]]
def recurrence_127_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,340,0]]
def recurrence_127_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_127_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![-1,0,340,0]]]
def recurrence_127_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,-1;1,0,0,0;0,1,0,340;0,0,1,0;0,0,-1,0;0,0,0,-1;1,0,340,0;0,1,0,340;0,-1,0,-340;0,0,-1,0;0,340,0,115599;1,0,340,0]
def recurrence_127_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_127_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_127_G (recurrence_127_words j)=recurrence_127_B j := by decide +kernel
theorem recurrence_127_products_checked : ∀ j i, recurrence_127_G i*recurrence_127_B j=∑ t,(recurrence_127_C j i t) • recurrence_127_B t := by decide +kernel
theorem recurrence_127_decoder_checked : recurrence_127_D*recurrence_127_X=1 := by decide +kernel
theorem recurrence_127_complete : Submodule.span ℚ (Set.range recurrence_127_B)=GeneratedOperatorAlgebra.wordSpan recurrence_127_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_127_words j,recurrence_127_words_checked j⟩
  · intro i j
    rw [recurrence_127_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_128_B : Fin 5 → Matrix (Fin 5) (Fin 5) ℚ := ![!![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1],!![0,1,0,0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1;1,-11,33,-33,11],!![0,0,1,0,0;0,0,0,1,0;0,0,0,0,1;1,-11,33,-33,11;11,-120,352,-330,88],!![0,0,0,1,0;0,0,0,0,1;1,-11,33,-33,11;11,-120,352,-330,88;88,-957,2784,-2552,638],!![0,0,0,0,1;1,-11,33,-33,11;11,-120,352,-330,88;88,-957,2784,-2552,638;638,-6930,20097,-18270,4466]]
def recurrence_128_G : Fin 1 → Matrix (Fin 5) (Fin 5) ℚ := ![!![0,1,0,0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1;1,-11,33,-33,11]]
def recurrence_128_words : Fin 5 → List (Fin 1) := ![[],[0],[0,0],[0,0,0],[0,0,0,0]]
def recurrence_128_C : Fin 5 → Fin 1 → Fin 5 → ℚ := ![![![0,1,0,0,0]],![![0,0,1,0,0]],![![0,0,0,1,0]],![![0,0,0,0,1]],![![1,-11,33,-33,11]]]
def recurrence_128_X : Matrix (Fin 25) (Fin 5) ℚ := !![1,0,0,0,0;0,1,0,0,0;0,0,1,0,0;0,0,0,1,0;0,0,0,0,1;0,0,0,0,1;1,0,0,0,-11;0,1,0,0,33;0,0,1,0,-33;0,0,0,1,11;0,0,0,1,11;0,0,0,-11,-120;1,0,0,33,352;0,1,0,-33,-330;0,0,1,11,88;0,0,1,11,88;0,0,-11,-120,-957;0,0,33,352,2784;1,0,-33,-330,-2552;0,1,11,88,638;0,1,11,88,638;0,-11,-120,-957,-6930;0,33,352,2784,20097;0,-33,-330,-2552,-18270;1,11,88,638,4466]
def recurrence_128_D : Matrix (Fin 5) (Fin 25) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_128_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_128_G (recurrence_128_words j)=recurrence_128_B j := by decide +kernel
theorem recurrence_128_products_checked : ∀ j i, recurrence_128_G i*recurrence_128_B j=∑ t,(recurrence_128_C j i t) • recurrence_128_B t := by decide +kernel
theorem recurrence_128_decoder_checked : recurrence_128_D*recurrence_128_X=1 := by decide +kernel
theorem recurrence_128_complete : Submodule.span ℚ (Set.range recurrence_128_B)=GeneratedOperatorAlgebra.wordSpan recurrence_128_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_128_words j,recurrence_128_words_checked j⟩
  · intro i j
    rw [recurrence_128_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_129_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,1,-8,8],!![0,0,1,0;0,0,0,1;0,1,-8,8;0,8,-63,56],!![0,0,0,1;0,1,-8,8;0,8,-63,56;0,56,-440,385]]
def recurrence_129_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,1,-8,8]]
def recurrence_129_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_129_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,1,-8,8]]]
def recurrence_129_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,1;0,1,0,-8;0,0,1,8;0,0,0,0;0,0,1,8;1,0,-8,-63;0,1,8,56;0,0,0,0;0,1,8,56;0,-8,-63,-440;1,8,56,385]
def recurrence_129_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_129_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_129_G (recurrence_129_words j)=recurrence_129_B j := by decide +kernel
theorem recurrence_129_products_checked : ∀ j i, recurrence_129_G i*recurrence_129_B j=∑ t,(recurrence_129_C j i t) • recurrence_129_B t := by decide +kernel
theorem recurrence_129_decoder_checked : recurrence_129_D*recurrence_129_X=1 := by decide +kernel
theorem recurrence_129_complete : Submodule.span ℚ (Set.range recurrence_129_B)=GeneratedOperatorAlgebra.wordSpan recurrence_129_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_129_words j,recurrence_129_words_checked j⟩
  · intro i j
    rw [recurrence_129_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
