import PerfectPower.GeneratedOperatorAlgebra
namespace PerfectPower.MonographOperators
open Matrix
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def recurrence_130_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,1],!![0,0,1;0,1,1;0,1,2]]
def recurrence_130_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,1]]
def recurrence_130_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_130_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,1]]]
def recurrence_130_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,1;0,0,0;0,1,1;1,1,2]
def recurrence_130_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_130_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_130_G (recurrence_130_words j)=recurrence_130_B j := by decide +kernel
theorem recurrence_130_products_checked : ∀ j i, recurrence_130_G i*recurrence_130_B j=∑ t,(recurrence_130_C j i t) • recurrence_130_B t := by decide +kernel
theorem recurrence_130_decoder_checked : recurrence_130_D*recurrence_130_X=1 := by decide +kernel
theorem recurrence_130_complete : Submodule.span ℚ (Set.range recurrence_130_B)=GeneratedOperatorAlgebra.wordSpan recurrence_130_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_130_words j,recurrence_130_words_checked j⟩
  · intro i j
    rw [recurrence_130_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_131_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;-1,38]]
def recurrence_131_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;-1,38]]
def recurrence_131_words : Fin 2 → List (Fin 1) := ![[],[0]]
def recurrence_131_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![-1,38]]]
def recurrence_131_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,-1;1,38]
def recurrence_131_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem recurrence_131_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_131_G (recurrence_131_words j)=recurrence_131_B j := by decide +kernel
theorem recurrence_131_products_checked : ∀ j i, recurrence_131_G i*recurrence_131_B j=∑ t,(recurrence_131_C j i t) • recurrence_131_B t := by decide +kernel
theorem recurrence_131_decoder_checked : recurrence_131_D*recurrence_131_X=1 := by decide +kernel
theorem recurrence_131_complete : Submodule.span ℚ (Set.range recurrence_131_B)=GeneratedOperatorAlgebra.wordSpan recurrence_131_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_131_words j,recurrence_131_words_checked j⟩
  · intro i j
    rw [recurrence_131_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_132_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![0,1,0;0,0,1;0,1,1],!![0,0,1;0,1,1;0,1,2]]
def recurrence_132_G : Fin 1 → Matrix (Fin 3) (Fin 3) ℚ := ![!![0,1,0;0,0,1;0,1,1]]
def recurrence_132_words : Fin 3 → List (Fin 1) := ![[],[0],[0,0]]
def recurrence_132_C : Fin 3 → Fin 1 → Fin 3 → ℚ := ![![![0,1,0]],![![0,0,1]],![![0,1,1]]]
def recurrence_132_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,0,0;0,1,0;0,0,1;0,0,0;1,0,1;0,1,1;0,0,0;0,1,1;1,1,2]
def recurrence_132_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0]
theorem recurrence_132_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_132_G (recurrence_132_words j)=recurrence_132_B j := by decide +kernel
theorem recurrence_132_products_checked : ∀ j i, recurrence_132_G i*recurrence_132_B j=∑ t,(recurrence_132_C j i t) • recurrence_132_B t := by decide +kernel
theorem recurrence_132_decoder_checked : recurrence_132_D*recurrence_132_X=1 := by decide +kernel
theorem recurrence_132_complete : Submodule.span ℚ (Set.range recurrence_132_B)=GeneratedOperatorAlgebra.wordSpan recurrence_132_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_132_words j,recurrence_132_words_checked j⟩
  · intro i j
    rw [recurrence_132_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_133_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1],!![0,0,1,0;0,0,0,1;0,0,1,1;0,0,1,2],!![0,0,0,1;0,0,1,1;0,0,1,2;0,0,2,3]]
def recurrence_133_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1]]
def recurrence_133_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_133_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,0,1,1]]]
def recurrence_133_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,0;0,1,0,1;0,0,1,1;0,0,0,0;0,0,0,0;1,0,1,1;0,1,1,2;0,0,0,0;0,0,0,0;0,1,1,2;1,1,2,3]
def recurrence_133_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_133_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_133_G (recurrence_133_words j)=recurrence_133_B j := by decide +kernel
theorem recurrence_133_products_checked : ∀ j i, recurrence_133_G i*recurrence_133_B j=∑ t,(recurrence_133_C j i t) • recurrence_133_B t := by decide +kernel
theorem recurrence_133_decoder_checked : recurrence_133_D*recurrence_133_X=1 := by decide +kernel
theorem recurrence_133_complete : Submodule.span ℚ (Set.range recurrence_133_B)=GeneratedOperatorAlgebra.wordSpan recurrence_133_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_133_words j,recurrence_133_words_checked j⟩
  · intro i j
    rw [recurrence_133_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def recurrence_134_B : Fin 4 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1],!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1],!![0,0,1,0;0,0,0,1;0,0,1,1;0,0,1,2],!![0,0,0,1;0,0,1,1;0,0,1,2;0,0,2,3]]
def recurrence_134_G : Fin 1 → Matrix (Fin 4) (Fin 4) ℚ := ![!![0,1,0,0;0,0,1,0;0,0,0,1;0,0,1,1]]
def recurrence_134_words : Fin 4 → List (Fin 1) := ![[],[0],[0,0],[0,0,0]]
def recurrence_134_C : Fin 4 → Fin 1 → Fin 4 → ℚ := ![![![0,1,0,0]],![![0,0,1,0]],![![0,0,0,1]],![![0,0,1,1]]]
def recurrence_134_X : Matrix (Fin 16) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1;0,0,0,0;1,0,0,0;0,1,0,1;0,0,1,1;0,0,0,0;0,0,0,0;1,0,1,1;0,1,1,2;0,0,0,0;0,0,0,0;0,1,1,2;1,1,2,3]
def recurrence_134_D : Matrix (Fin 4) (Fin 16) ℚ := !![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0;0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
theorem recurrence_134_words_checked : ∀ j, GeneratedOperatorAlgebra.word recurrence_134_G (recurrence_134_words j)=recurrence_134_B j := by decide +kernel
theorem recurrence_134_products_checked : ∀ j i, recurrence_134_G i*recurrence_134_B j=∑ t,(recurrence_134_C j i t) • recurrence_134_B t := by decide +kernel
theorem recurrence_134_decoder_checked : recurrence_134_D*recurrence_134_X=1 := by decide +kernel
theorem recurrence_134_complete : Submodule.span ℚ (Set.range recurrence_134_B)=GeneratedOperatorAlgebra.wordSpan recurrence_134_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨recurrence_134_words j,recurrence_134_words_checked j⟩
  · intro i j
    rw [recurrence_134_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def example_0_B : Fin 4 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;0,0],!![0,0;1,0],!![0,0;0,1]]
def example_0_G : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;0,0],!![0,0;1,0]]
def example_0_words : Fin 4 → List (Fin 2) := ![[],[0],[1],[1,0]]
def example_0_C : Fin 4 → Fin 2 → Fin 4 → ℚ := ![![![0,1,0,0],![0,0,1,0]],![![0,0,0,0],![0,0,0,1]],![![1,0,0,-1],![0,0,0,0]],![![0,1,0,0],![0,0,0,0]]]
def example_0_X : Matrix (Fin 4) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;1,0,0,1]
def example_0_D : Matrix (Fin 4) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0;0,0,1,0;-1,0,0,1]
theorem example_0_words_checked : ∀ j, GeneratedOperatorAlgebra.word example_0_G (example_0_words j)=example_0_B j := by decide +kernel
theorem example_0_products_checked : ∀ j i, example_0_G i*example_0_B j=∑ t,(example_0_C j i t) • example_0_B t := by decide +kernel
theorem example_0_decoder_checked : example_0_D*example_0_X=1 := by decide +kernel
theorem example_0_complete : Submodule.span ℚ (Set.range example_0_B)=GeneratedOperatorAlgebra.wordSpan example_0_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨example_0_words j,example_0_words_checked j⟩
  · intro i j
    rw [example_0_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def example_1_B : Fin 3 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![1,0;0,0],!![0,1;0,0]]
def example_1_G : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,0],!![0,1;0,0]]
def example_1_words : Fin 3 → List (Fin 2) := ![[],[0],[1]]
def example_1_C : Fin 3 → Fin 2 → Fin 3 → ℚ := ![![![0,1,0],![0,0,1]],![![0,1,0],![0,0,0]],![![0,0,1],![0,0,0]]]
def example_1_X : Matrix (Fin 4) (Fin 3) ℚ := !![1,1,0;0,0,1;0,0,0;1,0,0]
def example_1_D : Matrix (Fin 3) (Fin 4) ℚ := !![0,0,0,1;1,0,0,-1;0,1,0,0]
theorem example_1_words_checked : ∀ j, GeneratedOperatorAlgebra.word example_1_G (example_1_words j)=example_1_B j := by decide +kernel
theorem example_1_products_checked : ∀ j i, example_1_G i*example_1_B j=∑ t,(example_1_C j i t) • example_1_B t := by decide +kernel
theorem example_1_decoder_checked : example_1_D*example_1_X=1 := by decide +kernel
theorem example_1_complete : Submodule.span ℚ (Set.range example_1_B)=GeneratedOperatorAlgebra.wordSpan example_1_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨example_1_words j,example_1_words_checked j⟩
  · intro i j
    rw [example_1_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def example_2_B : Fin 2 → Matrix (Fin 2) (Fin 2) ℚ := ![!![1,0;0,1],!![0,1;0,0]]
def example_2_G : Fin 1 → Matrix (Fin 2) (Fin 2) ℚ := ![!![0,1;0,0]]
def example_2_words : Fin 2 → List (Fin 1) := ![[],[0]]
def example_2_C : Fin 2 → Fin 1 → Fin 2 → ℚ := ![![![0,1]],![![0,0]]]
def example_2_X : Matrix (Fin 4) (Fin 2) ℚ := !![1,0;0,1;0,0;1,0]
def example_2_D : Matrix (Fin 2) (Fin 4) ℚ := !![1,0,0,0;0,1,0,0]
theorem example_2_words_checked : ∀ j, GeneratedOperatorAlgebra.word example_2_G (example_2_words j)=example_2_B j := by decide +kernel
theorem example_2_products_checked : ∀ j i, example_2_G i*example_2_B j=∑ t,(example_2_C j i t) • example_2_B t := by decide +kernel
theorem example_2_decoder_checked : example_2_D*example_2_X=1 := by decide +kernel
theorem example_2_complete : Submodule.span ℚ (Set.range example_2_B)=GeneratedOperatorAlgebra.wordSpan example_2_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨example_2_words j,example_2_words_checked j⟩
  · intro i j
    rw [example_2_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
def field756_B : Fin 3 → Matrix (Fin 3) (Fin 3) ℚ := ![!![1,0,0;0,1,0;0,0,1],!![-5,2,0;0,1,2;1,0,1],!![11,-4,2;1,-1,2;-2,1,-1]]
def field756_G : Fin 2 → Matrix (Fin 3) (Fin 3) ℚ := ![!![-5,2,0;0,1,2;1,0,1],!![11,-4,2;1,-1,2;-2,1,-1]]
def field756_words : Fin 3 → List (Fin 2) := ![[],[0],[1]]
def field756_C : Fin 3 → Fin 2 → Fin 3 → ℚ := ![![![0,1,0],![0,0,1]],![![3,0,2],![-5,3,-3]],![![-5,3,-3],![12,-7,6]]]
def field756_X : Matrix (Fin 9) (Fin 3) ℚ := !![1,-5,11;0,2,-4;0,0,2;0,0,1;1,1,-1;0,2,2;0,1,-2;0,0,1;1,1,-1]
def field756_D : Matrix (Fin 3) (Fin 9) ℚ := !![1,(5/2),(-1/2),0,0,0,0,0,0;0,(1/2),1,0,0,0,0,0,0;0,0,(1/2),0,0,0,0,0,0]
theorem field756_words_checked : ∀ j, GeneratedOperatorAlgebra.word field756_G (field756_words j)=field756_B j := by decide +kernel
theorem field756_products_checked : ∀ j i, field756_G i*field756_B j=∑ t,(field756_C j i t) • field756_B t := by decide +kernel
theorem field756_decoder_checked : field756_D*field756_X=1 := by decide +kernel
theorem field756_complete : Submodule.span ℚ (Set.range field756_B)=GeneratedOperatorAlgebra.wordSpan field756_G := by
  apply GeneratedOperatorAlgebra.finite_complete
  · exact ⟨0,by decide +kernel⟩
  · intro j;exact ⟨field756_words j,field756_words_checked j⟩
  · intro i j
    rw [field756_products_checked j i]
    apply Submodule.sum_mem
    intro t ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)
end PerfectPower.MonographOperators
