import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_50_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,-1,3],!![0,0,1;0,-1,3;0,-3,8]]
def recurrence_50_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,-1,3]]
def recurrence_50_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_50_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,-1,3]]]
def recurrence_50_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,-1;0,1,3;0,0,0;0,-1,-3;1,3,8]
def recurrence_50_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_50_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_50_G (recurrence_50_words j)=recurrence_50_B j := by decide +kernel
theorem recurrence_50_products_checked : ∀ j i, recurrence_50_G i*recurrence_50_B j=∑ t,(recurrence_50_C j i t) • recurrence_50_B t := by decide +kernel
theorem recurrence_50_decoder_checked : recurrence_50_D*recurrence_50_X=1 := by decide +kernel
theorem recurrence_50_complete : Submodule.span ℚ (Set.range recurrence_50_B)=GeneratedOperatorAlgebra.wordSpan recurrence_50_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_50_words j,recurrence_50_words_checked j⟩
  · intro i j
    rw [recurrence_50_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_51_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1],!![0,0,1,0;0,0,0,1;0,0,1,1;0,0,1,2],!![0,0,0,1;0,0,1,1;0,0,1,2;0,0,2,3]]
def recurrence_51_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1]]
def recurrence_51_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_51_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,0,1,1]]]
def recurrence_51_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,0;0,1,0,1;0,0,1,1;0,0,0,0;0,0,0,0;1,0,1,1;0,1,1,2;0,0,0,0;0,0,0,0;0,1,1,2;1,1,2,3]
def recurrence_51_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_51_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_51_G (recurrence_51_words j)=recurrence_51_B j := by decide +kernel
theorem recurrence_51_products_checked : ∀ j i, recurrence_51_G i*recurrence_51_B j=∑ t,(recurrence_51_C j i t) • recurrence_51_B t := by decide +kernel
theorem recurrence_51_decoder_checked : recurrence_51_D*recurrence_51_X=1 := by decide +kernel
theorem recurrence_51_complete : Submodule.span ℚ (Set.range recurrence_51_B)=GeneratedOperatorAlgebra.wordSpan recurrence_51_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_51_words j,recurrence_51_words_checked j⟩
  · intro i j
    rw [recurrence_51_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_52_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,1],!![0,0,1;0,1,1;0,1,2]]
def recurrence_52_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,1]]
def recurrence_52_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_52_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,1]]]
def recurrence_52_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,1;0,0,0;0,1,1;1,1,2]
def recurrence_52_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_52_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_52_G (recurrence_52_words j)=recurrence_52_B j := by decide +kernel
theorem recurrence_52_products_checked : ∀ j i, recurrence_52_G i*recurrence_52_B j=∑ t,(recurrence_52_C j i t) • recurrence_52_B t := by decide +kernel
theorem recurrence_52_decoder_checked : recurrence_52_D*recurrence_52_X=1 := by decide +kernel
theorem recurrence_52_complete : Submodule.span ℚ (Set.range recurrence_52_B)=GeneratedOperatorAlgebra.wordSpan recurrence_52_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_52_words j,recurrence_52_words_checked j⟩
  · intro i j
    rw [recurrence_52_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_53_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,1,-35,35],!![0,0,1,0;0,0,0,1;0,1,-35,35;0,35,-1224,1190],!![0,0,0,1;0,1,-35,35;0,35,-1224,1190;0,1190,-41615,40426]]
def recurrence_53_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,1,-35,35]]
def recurrence_53_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_53_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,1,-35,35]]]
def recurrence_53_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,1;0,1,0,-35;0,0,1,35;0,0,0,0;0,0,1,35;1,0,-35,-1224;0,1,35,1190;0,0,0,0;0,1,35,1190;0,-35,-1224,-41615;1,35,1190,40426]
def recurrence_53_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_53_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_53_G (recurrence_53_words j)=recurrence_53_B j := by decide +kernel
theorem recurrence_53_products_checked : ∀ j i, recurrence_53_G i*recurrence_53_B j=∑ t,(recurrence_53_C j i t) • recurrence_53_B t := by decide +kernel
theorem recurrence_53_decoder_checked : recurrence_53_D*recurrence_53_X=1 := by decide +kernel
theorem recurrence_53_complete : Submodule.span ℚ (Set.range recurrence_53_B)=GeneratedOperatorAlgebra.wordSpan recurrence_53_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_53_words j,recurrence_53_words_checked j⟩
  · intro i j
    rw [recurrence_53_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_54_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,1,-15,15],!![0,0,1,0;0,0,0,1;0,1,-15,15;0,15,-224,210],!![0,0,0,1;0,1,-15,15;0,15,-224,210;0,210,-3135,2926]]
def recurrence_54_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,1,-15,15]]
def recurrence_54_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_54_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,1,-15,15]]]
def recurrence_54_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,1;0,1,0,-15;0,0,1,15;0,0,0,0;0,0,1,15;1,0,-15,-224;0,1,15,210;0,0,0,0;0,1,15,210;0,-15,-224,-3135;1,15,210,2926]
def recurrence_54_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_54_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_54_G (recurrence_54_words j)=recurrence_54_B j := by decide +kernel
theorem recurrence_54_products_checked : ∀ j i, recurrence_54_G i*recurrence_54_B j=∑ t,(recurrence_54_C j i t) • recurrence_54_B t := by decide +kernel
theorem recurrence_54_decoder_checked : recurrence_54_D*recurrence_54_X=1 := by decide +kernel
theorem recurrence_54_complete : Submodule.span ℚ (Set.range recurrence_54_B)=GeneratedOperatorAlgebra.wordSpan recurrence_54_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_54_words j,recurrence_54_words_checked j⟩
  · intro i j
    rw [recurrence_54_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_55_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,-1,3],!![0,0,1;0,-1,3;0,-3,8]]
def recurrence_55_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,-1,3]]
def recurrence_55_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_55_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,-1,3]]]
def recurrence_55_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,-1;0,1,3;0,0,0;0,-1,-3;1,3,8]
def recurrence_55_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_55_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_55_G (recurrence_55_words j)=recurrence_55_B j := by decide +kernel
theorem recurrence_55_products_checked : ∀ j i, recurrence_55_G i*recurrence_55_B j=∑ t,(recurrence_55_C j i t) • recurrence_55_B t := by decide +kernel
theorem recurrence_55_decoder_checked : recurrence_55_D*recurrence_55_X=1 := by decide +kernel
theorem recurrence_55_complete : Submodule.span ℚ (Set.range recurrence_55_B)=GeneratedOperatorAlgebra.wordSpan recurrence_55_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_55_words j,recurrence_55_words_checked j⟩
  · intro i j
    rw [recurrence_55_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_56_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-7,7],!![0,0,1;1,-7,7;7,-48,42]]
def recurrence_56_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-7,7]]
def recurrence_56_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_56_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-7,7]]]
def recurrence_56_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-7;0,1,7;0,1,7;0,-7,-48;1,7,42]
def recurrence_56_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_56_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_56_G (recurrence_56_words j)=recurrence_56_B j := by decide +kernel
theorem recurrence_56_products_checked : ∀ j i, recurrence_56_G i*recurrence_56_B j=∑ t,(recurrence_56_C j i t) • recurrence_56_B t := by decide +kernel
theorem recurrence_56_decoder_checked : recurrence_56_D*recurrence_56_X=1 := by decide +kernel
theorem recurrence_56_complete : Submodule.span ℚ (Set.range recurrence_56_B)=GeneratedOperatorAlgebra.wordSpan recurrence_56_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_56_words j,recurrence_56_words_checked j⟩
  · intro i j
    rw [recurrence_56_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_57_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,14]]
def recurrence_57_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,14]]
def recurrence_57_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_57_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,14]]]
def recurrence_57_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,14]
def recurrence_57_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_57_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_57_G (recurrence_57_words j)=recurrence_57_B j := by decide +kernel
theorem recurrence_57_products_checked : ∀ j i, recurrence_57_G i*recurrence_57_B j=∑ t,(recurrence_57_C j i t) • recurrence_57_B t := by decide +kernel
theorem recurrence_57_decoder_checked : recurrence_57_D*recurrence_57_X=1 := by decide +kernel
theorem recurrence_57_complete : Submodule.span ℚ (Set.range recurrence_57_B)=GeneratedOperatorAlgebra.wordSpan recurrence_57_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_57_words j,recurrence_57_words_checked j⟩
  · intro i j
    rw [recurrence_57_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_58_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,1],!![0,0,1;0,1,1;0,1,2]]
def recurrence_58_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,1]]
def recurrence_58_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_58_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,1]]]
def recurrence_58_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,1;0,0,0;0,1,1;1,1,2]
def recurrence_58_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_58_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_58_G (recurrence_58_words j)=recurrence_58_B j := by decide +kernel
theorem recurrence_58_products_checked : ∀ j i, recurrence_58_G i*recurrence_58_B j=∑ t,(recurrence_58_C j i t) • recurrence_58_B t := by decide +kernel
theorem recurrence_58_decoder_checked : recurrence_58_D*recurrence_58_X=1 := by decide +kernel
theorem recurrence_58_complete : Submodule.span ℚ (Set.range recurrence_58_B)=GeneratedOperatorAlgebra.wordSpan recurrence_58_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_58_words j,recurrence_58_words_checked j⟩
  · intro i j
    rw [recurrence_58_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_59_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,2]]
def recurrence_59_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,2]]
def recurrence_59_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_59_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,2]]]
def recurrence_59_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,2]
def recurrence_59_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_59_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_59_G (recurrence_59_words j)=recurrence_59_B j := by decide +kernel
theorem recurrence_59_products_checked : ∀ j i, recurrence_59_G i*recurrence_59_B j=∑ t,(recurrence_59_C j i t) • recurrence_59_B t := by decide +kernel
theorem recurrence_59_decoder_checked : recurrence_59_D*recurrence_59_X=1 := by decide +kernel
theorem recurrence_59_complete : Submodule.span ℚ (Set.range recurrence_59_B)=GeneratedOperatorAlgebra.wordSpan recurrence_59_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_59_words j,recurrence_59_words_checked j⟩
  · intro i j
    rw [recurrence_59_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
