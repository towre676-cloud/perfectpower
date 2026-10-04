import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_70_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,18]]
def recurrence_70_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,18]]
def recurrence_70_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_70_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,18]]]
def recurrence_70_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,18]
def recurrence_70_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_70_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_70_G (recurrence_70_words j)=recurrence_70_B j := by decide +kernel
theorem recurrence_70_products_checked : ∀ j i, recurrence_70_G i*recurrence_70_B j=∑ t,(recurrence_70_C j i t) • recurrence_70_B t := by decide +kernel
theorem recurrence_70_decoder_checked : recurrence_70_D*recurrence_70_X=1 := by decide +kernel
theorem recurrence_70_complete : Submodule.span ℚ (Set.range recurrence_70_B)=GeneratedOperatorAlgebra.wordSpan recurrence_70_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_70_words j,recurrence_70_words_checked j⟩
  · intro i j
    rw [recurrence_70_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_71_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,6]]
def recurrence_71_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,6]]
def recurrence_71_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_71_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,6]]]
def recurrence_71_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,6]
def recurrence_71_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_71_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_71_G (recurrence_71_words j)=recurrence_71_B j := by decide +kernel
theorem recurrence_71_products_checked : ∀ j i, recurrence_71_G i*recurrence_71_B j=∑ t,(recurrence_71_C j i t) • recurrence_71_B t := by decide +kernel
theorem recurrence_71_decoder_checked : recurrence_71_D*recurrence_71_X=1 := by decide +kernel
theorem recurrence_71_complete : Submodule.span ℚ (Set.range recurrence_71_B)=GeneratedOperatorAlgebra.wordSpan recurrence_71_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_71_words j,recurrence_71_words_checked j⟩
  · intro i j
    rw [recurrence_71_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_72_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,1298]]
def recurrence_72_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,1298]]
def recurrence_72_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_72_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,1298]]]
def recurrence_72_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,1298]
def recurrence_72_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_72_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_72_G (recurrence_72_words j)=recurrence_72_B j := by decide +kernel
theorem recurrence_72_products_checked : ∀ j i, recurrence_72_G i*recurrence_72_B j=∑ t,(recurrence_72_C j i t) • recurrence_72_B t := by decide +kernel
theorem recurrence_72_decoder_checked : recurrence_72_D*recurrence_72_X=1 := by decide +kernel
theorem recurrence_72_complete : Submodule.span ℚ (Set.range recurrence_72_B)=GeneratedOperatorAlgebra.wordSpan recurrence_72_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_72_words j,recurrence_72_words_checked j⟩
  · intro i j
    rw [recurrence_72_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_73_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_73_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_73_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_73_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_73_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_73_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_73_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_73_G (recurrence_73_words j)=recurrence_73_B j := by decide +kernel
theorem recurrence_73_products_checked : ∀ j i, recurrence_73_G i*recurrence_73_B j=∑ t,(recurrence_73_C j i t) • recurrence_73_B t := by decide +kernel
theorem recurrence_73_decoder_checked : recurrence_73_D*recurrence_73_X=1 := by decide +kernel
theorem recurrence_73_complete : Submodule.span ℚ (Set.range recurrence_73_B)=GeneratedOperatorAlgebra.wordSpan recurrence_73_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_73_words j,recurrence_73_words_checked j⟩
  · intro i j
    rw [recurrence_73_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_74_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,6,0],!![0,0,1,0;0,0,0,1;-1,0,6,0;0,-1,0,6],!![0,0,0,1;-1,0,6,0;0,-1,0,6;-6,0,35,0]]
def recurrence_74_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,6,0]]
def recurrence_74_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_74_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![-1,0,6,0]]]
def recurrence_74_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,-1;1,0,0,0;0,1,0,6;0,0,1,0;0,0,-1,0;0,0,0,-1;1,0,6,0;0,1,0,6;0,-1,0,-6;0,0,-1,0;0,6,0,35;1,0,6,0]
def recurrence_74_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_74_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_74_G (recurrence_74_words j)=recurrence_74_B j := by decide +kernel
theorem recurrence_74_products_checked : ∀ j i, recurrence_74_G i*recurrence_74_B j=∑ t,(recurrence_74_C j i t) • recurrence_74_B t := by decide +kernel
theorem recurrence_74_decoder_checked : recurrence_74_D*recurrence_74_X=1 := by decide +kernel
theorem recurrence_74_complete : Submodule.span ℚ (Set.range recurrence_74_B)=GeneratedOperatorAlgebra.wordSpan recurrence_74_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_74_words j,recurrence_74_words_checked j⟩
  · intro i j
    rw [recurrence_74_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_75_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,2]]
def recurrence_75_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,2]]
def recurrence_75_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_75_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,2]]]
def recurrence_75_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,2]
def recurrence_75_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_75_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_75_G (recurrence_75_words j)=recurrence_75_B j := by decide +kernel
theorem recurrence_75_products_checked : ∀ j i, recurrence_75_G i*recurrence_75_B j=∑ t,(recurrence_75_C j i t) • recurrence_75_B t := by decide +kernel
theorem recurrence_75_decoder_checked : recurrence_75_D*recurrence_75_X=1 := by decide +kernel
theorem recurrence_75_complete : Submodule.span ℚ (Set.range recurrence_75_B)=GeneratedOperatorAlgebra.wordSpan recurrence_75_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_75_words j,recurrence_75_words_checked j⟩
  · intro i j
    rw [recurrence_75_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_76_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-35,35],!![0,0,1;1,-35,35;35,-1224,1190]]
def recurrence_76_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-35,35]]
def recurrence_76_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_76_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-35,35]]]
def recurrence_76_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-35;0,1,35;0,1,35;0,-35,-1224;1,35,1190]
def recurrence_76_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_76_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_76_G (recurrence_76_words j)=recurrence_76_B j := by decide +kernel
theorem recurrence_76_products_checked : ∀ j i, recurrence_76_G i*recurrence_76_B j=∑ t,(recurrence_76_C j i t) • recurrence_76_B t := by decide +kernel
theorem recurrence_76_decoder_checked : recurrence_76_D*recurrence_76_X=1 := by decide +kernel
theorem recurrence_76_complete : Submodule.span ℚ (Set.range recurrence_76_B)=GeneratedOperatorAlgebra.wordSpan recurrence_76_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_76_words j,recurrence_76_words_checked j⟩
  · intro i j
    rw [recurrence_76_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_77_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;1,1]]
def recurrence_77_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;1,1]]
def recurrence_77_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_77_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![1,1]]]
def recurrence_77_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,1;1,1]
def recurrence_77_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_77_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_77_G (recurrence_77_words j)=recurrence_77_B j := by decide +kernel
theorem recurrence_77_products_checked : ∀ j i, recurrence_77_G i*recurrence_77_B j=∑ t,(recurrence_77_C j i t) • recurrence_77_B t := by decide +kernel
theorem recurrence_77_decoder_checked : recurrence_77_D*recurrence_77_X=1 := by decide +kernel
theorem recurrence_77_complete : Submodule.span ℚ (Set.range recurrence_77_B)=GeneratedOperatorAlgebra.wordSpan recurrence_77_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_77_words j,recurrence_77_words_checked j⟩
  · intro i j
    rw [recurrence_77_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_78_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;-1,5,5],!![0,0,1;-1,5,5;-5,24,30]]
def recurrence_78_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;-1,5,5]]
def recurrence_78_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_78_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![-1,5,5]]]
def recurrence_78_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,-1;1,0,5;0,1,5;0,-1,-5;0,5,24;1,5,30]
def recurrence_78_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_78_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_78_G (recurrence_78_words j)=recurrence_78_B j := by decide +kernel
theorem recurrence_78_products_checked : ∀ j i, recurrence_78_G i*recurrence_78_B j=∑ t,(recurrence_78_C j i t) • recurrence_78_B t := by decide +kernel
theorem recurrence_78_decoder_checked : recurrence_78_D*recurrence_78_X=1 := by decide +kernel
theorem recurrence_78_complete : Submodule.span ℚ (Set.range recurrence_78_B)=GeneratedOperatorAlgebra.wordSpan recurrence_78_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_78_words j,recurrence_78_words_checked j⟩
  · intro i j
    rw [recurrence_78_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_79_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,4]]
def recurrence_79_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,4]]
def recurrence_79_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_79_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,4]]]
def recurrence_79_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,4]
def recurrence_79_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_79_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_79_G (recurrence_79_words j)=recurrence_79_B j := by decide +kernel
theorem recurrence_79_products_checked : ∀ j i, recurrence_79_G i*recurrence_79_B j=∑ t,(recurrence_79_C j i t) • recurrence_79_B t := by decide +kernel
theorem recurrence_79_decoder_checked : recurrence_79_D*recurrence_79_X=1 := by decide +kernel
theorem recurrence_79_complete : Submodule.span ℚ (Set.range recurrence_79_B)=GeneratedOperatorAlgebra.wordSpan recurrence_79_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_79_words j,recurrence_79_words_checked j⟩
  · intro i j
    rw [recurrence_79_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
