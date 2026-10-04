import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_80_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,1],!![0,0,1;0,1,1;0,1,2]]
def recurrence_80_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,1]]
def recurrence_80_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_80_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,1]]]
def recurrence_80_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,1;0,0,0;0,1,1;1,1,2]
def recurrence_80_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_80_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_80_G (recurrence_80_words j)=recurrence_80_B j := by decide +kernel
theorem recurrence_80_products_checked : ∀ j i, recurrence_80_G i*recurrence_80_B j=∑ t,(recurrence_80_C j i t) • recurrence_80_B t := by decide +kernel
theorem recurrence_80_decoder_checked : recurrence_80_D*recurrence_80_X=1 := by decide +kernel
theorem recurrence_80_complete : Submodule.span ℚ (Set.range recurrence_80_B)=GeneratedOperatorAlgebra.wordSpan recurrence_80_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_80_words j,recurrence_80_words_checked j⟩
  · intro i j
    rw [recurrence_80_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_81_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,10,0],!![0,0,1,0;0,0,0,1;-1,0,10,0;0,-1,0,10],!![0,0,0,1;-1,0,10,0;0,-1,0,10;-10,0,99,0]]
def recurrence_81_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,10,0]]
def recurrence_81_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_81_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![-1,0,10,0]]]
def recurrence_81_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,-1;1,0,0,0;0,1,0,10;0,0,1,0;0,0,-1,0;0,0,0,-1;1,0,10,0;0,1,0,10;0,-1,0,-10;0,0,-1,0;0,10,0,99;1,0,10,0]
def recurrence_81_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_81_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_81_G (recurrence_81_words j)=recurrence_81_B j := by decide +kernel
theorem recurrence_81_products_checked : ∀ j i, recurrence_81_G i*recurrence_81_B j=∑ t,(recurrence_81_C j i t) • recurrence_81_B t := by decide +kernel
theorem recurrence_81_decoder_checked : recurrence_81_D*recurrence_81_X=1 := by decide +kernel
theorem recurrence_81_complete : Submodule.span ℚ (Set.range recurrence_81_B)=GeneratedOperatorAlgebra.wordSpan recurrence_81_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_81_words j,recurrence_81_words_checked j⟩
  · intro i j
    rw [recurrence_81_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_82_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-8,8],!![0,0,1;1,-8,8;8,-63,56]]
def recurrence_82_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-8,8]]
def recurrence_82_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_82_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-8,8]]]
def recurrence_82_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-8;0,1,8;0,1,8;0,-8,-63;1,8,56]
def recurrence_82_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_82_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_82_G (recurrence_82_words j)=recurrence_82_B j := by decide +kernel
theorem recurrence_82_products_checked : ∀ j i, recurrence_82_G i*recurrence_82_B j=∑ t,(recurrence_82_C j i t) • recurrence_82_B t := by decide +kernel
theorem recurrence_82_decoder_checked : recurrence_82_D*recurrence_82_X=1 := by decide +kernel
theorem recurrence_82_complete : Submodule.span ℚ (Set.range recurrence_82_B)=GeneratedOperatorAlgebra.wordSpan recurrence_82_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_82_words j,recurrence_82_words_checked j⟩
  · intro i j
    rw [recurrence_82_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_83_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-8,8],!![0,0,1;1,-8,8;8,-63,56]]
def recurrence_83_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-8,8]]
def recurrence_83_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_83_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-8,8]]]
def recurrence_83_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-8;0,1,8;0,1,8;0,-8,-63;1,8,56]
def recurrence_83_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_83_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_83_G (recurrence_83_words j)=recurrence_83_B j := by decide +kernel
theorem recurrence_83_products_checked : ∀ j i, recurrence_83_G i*recurrence_83_B j=∑ t,(recurrence_83_C j i t) • recurrence_83_B t := by decide +kernel
theorem recurrence_83_decoder_checked : recurrence_83_D*recurrence_83_X=1 := by decide +kernel
theorem recurrence_83_complete : Submodule.span ℚ (Set.range recurrence_83_B)=GeneratedOperatorAlgebra.wordSpan recurrence_83_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_83_words j,recurrence_83_words_checked j⟩
  · intro i j
    rw [recurrence_83_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_84_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-8,8],!![0,0,1;1,-8,8;8,-63,56]]
def recurrence_84_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-8,8]]
def recurrence_84_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_84_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-8,8]]]
def recurrence_84_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-8;0,1,8;0,1,8;0,-8,-63;1,8,56]
def recurrence_84_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_84_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_84_G (recurrence_84_words j)=recurrence_84_B j := by decide +kernel
theorem recurrence_84_products_checked : ∀ j i, recurrence_84_G i*recurrence_84_B j=∑ t,(recurrence_84_C j i t) • recurrence_84_B t := by decide +kernel
theorem recurrence_84_decoder_checked : recurrence_84_D*recurrence_84_X=1 := by decide +kernel
theorem recurrence_84_complete : Submodule.span ℚ (Set.range recurrence_84_B)=GeneratedOperatorAlgebra.wordSpan recurrence_84_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_84_words j,recurrence_84_words_checked j⟩
  · intro i j
    rw [recurrence_84_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_85_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,34]]
def recurrence_85_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,34]]
def recurrence_85_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_85_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,34]]]
def recurrence_85_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,34]
def recurrence_85_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_85_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_85_G (recurrence_85_words j)=recurrence_85_B j := by decide +kernel
theorem recurrence_85_products_checked : ∀ j i, recurrence_85_G i*recurrence_85_B j=∑ t,(recurrence_85_C j i t) • recurrence_85_B t := by decide +kernel
theorem recurrence_85_decoder_checked : recurrence_85_D*recurrence_85_X=1 := by decide +kernel
theorem recurrence_85_complete : Submodule.span ℚ (Set.range recurrence_85_B)=GeneratedOperatorAlgebra.wordSpan recurrence_85_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_85_words j,recurrence_85_words_checked j⟩
  · intro i j
    rw [recurrence_85_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_86_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,18,0],!![0,0,1,0;0,0,0,1;-1,0,18,0;0,-1,0,18],!![0,0,0,1;-1,0,18,0;0,-1,0,18;-18,0,323,0]]
def recurrence_86_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;-1,0,18,0]]
def recurrence_86_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_86_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![-1,0,18,0]]]
def recurrence_86_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,-1;1,0,0,0;0,1,0,18;0,0,1,0;0,0,-1,0;0,0,0,-1;1,0,18,0;0,1,0,18;0,-1,0,-18;0,0,-1,0;0,18,0,323;1,0,18,0]
def recurrence_86_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_86_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_86_G (recurrence_86_words j)=recurrence_86_B j := by decide +kernel
theorem recurrence_86_products_checked : ∀ j i, recurrence_86_G i*recurrence_86_B j=∑ t,(recurrence_86_C j i t) • recurrence_86_B t := by decide +kernel
theorem recurrence_86_decoder_checked : recurrence_86_D*recurrence_86_X=1 := by decide +kernel
theorem recurrence_86_complete : Submodule.span ℚ (Set.range recurrence_86_B)=GeneratedOperatorAlgebra.wordSpan recurrence_86_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_86_words j,recurrence_86_words_checked j⟩
  · intro i j
    rw [recurrence_86_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_87_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;1,-35,35],!![0,0,1;1,-35,35;35,-1224,1190]]
def recurrence_87_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;1,-35,35]]
def recurrence_87_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_87_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![1,-35,35]]]
def recurrence_87_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,1;1,0,-35;0,1,35;0,1,35;0,-35,-1224;1,35,1190]
def recurrence_87_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_87_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_87_G (recurrence_87_words j)=recurrence_87_B j := by decide +kernel
theorem recurrence_87_products_checked : ∀ j i, recurrence_87_G i*recurrence_87_B j=∑ t,(recurrence_87_C j i t) • recurrence_87_B t := by decide +kernel
theorem recurrence_87_decoder_checked : recurrence_87_D*recurrence_87_X=1 := by decide +kernel
theorem recurrence_87_complete : Submodule.span ℚ (Set.range recurrence_87_B)=GeneratedOperatorAlgebra.wordSpan recurrence_87_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_87_words j,recurrence_87_words_checked j⟩
  · intro i j
    rw [recurrence_87_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_88_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,-1,3],!![0,0,1;0,-1,3;0,-3,8]]
def recurrence_88_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,-1,3]]
def recurrence_88_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_88_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,-1,3]]]
def recurrence_88_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,-1;0,1,3;0,0,0;0,-1,-3;1,3,8]
def recurrence_88_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_88_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_88_G (recurrence_88_words j)=recurrence_88_B j := by decide +kernel
theorem recurrence_88_products_checked : ∀ j i, recurrence_88_G i*recurrence_88_B j=∑ t,(recurrence_88_C j i t) • recurrence_88_B t := by decide +kernel
theorem recurrence_88_decoder_checked : recurrence_88_D*recurrence_88_X=1 := by decide +kernel
theorem recurrence_88_complete : Submodule.span ℚ (Set.range recurrence_88_B)=GeneratedOperatorAlgebra.wordSpan recurrence_88_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_88_words j,recurrence_88_words_checked j⟩
  · intro i j
    rw [recurrence_88_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_89_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;-1,5,5],!![0,0,1;-1,5,5;-5,24,30]]
def recurrence_89_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;-1,5,5]]
def recurrence_89_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_89_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![-1,5,5]]]
def recurrence_89_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,-1;1,0,5;0,1,5;0,-1,-5;0,5,24;1,5,30]
def recurrence_89_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_89_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_89_G (recurrence_89_words j)=recurrence_89_B j := by decide +kernel
theorem recurrence_89_products_checked : ∀ j i, recurrence_89_G i*recurrence_89_B j=∑ t,(recurrence_89_C j i t) • recurrence_89_B t := by decide +kernel
theorem recurrence_89_decoder_checked : recurrence_89_D*recurrence_89_X=1 := by decide +kernel
theorem recurrence_89_complete : Submodule.span ℚ (Set.range recurrence_89_B)=GeneratedOperatorAlgebra.wordSpan recurrence_89_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_89_words j,recurrence_89_words_checked j⟩
  · intro i j
    rw [recurrence_89_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
