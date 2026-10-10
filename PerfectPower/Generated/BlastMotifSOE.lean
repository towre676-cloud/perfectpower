import PerfectPower.SOESemantics
namespace PerfectPower.CheckedSOE.Pddaa6506dde6c6acd8b153a8ea035e5ddc1c5c26ab7788eccae43bb15451834a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ddaa6506dde6c6acd8b153a8ea035e5ddc1c5c26ab7788eccae43bb15451834a; encodings are recorded in the compiler receipt.
def obs (s : Fin 6) : Fin 4 := if s = 0 then 3 else (if s = 1 then 3 else (if s = 2 then 3 else (if s = 3 then 0 else (if s = 4 then 2 else (1)))))
def step (s : Fin 6) (a : Fin 4) : Option (Fin 6) := if a = 0 then if s = 0 then some 1 else (if s = 1 then some 1 else (if s = 2 then some 1 else (if s = 3 then some 1 else (if s = 4 then some 1 else (some 1))))) else (if a = 1 then if s = 0 then some 2 else (if s = 1 then some 3 else (if s = 2 then some 2 else (if s = 3 then some 2 else (if s = 4 then some 2 else (some 2))))) else (if a = 2 then if s = 0 then some 0 else (if s = 1 then some 0 else (if s = 2 then some 4 else (if s = 3 then some 5 else (if s = 4 then some 0 else (some 0))))) else (if s = 0 then some 0 else (if s = 1 then some 0 else (if s = 2 then some 0 else (if s = 3 then some 0 else (if s = 4 then some 0 else (some 0))))))))
def q (s : Fin 6) : Fin 6 := if s = 0 then 0 else (if s = 1 then 1 else (if s = 2 then 2 else (if s = 3 then 3 else (if s = 4 then 4 else (5)))))
def out (s : Fin 6) : Fin 4 := if s = 0 then 3 else (if s = 1 then 3 else (if s = 2 then 3 else (if s = 3 then 0 else (if s = 4 then 2 else (1)))))
def target (s : Fin 6) (a : Fin 4) : Option (Fin 6) := if a = 0 then if s = 0 then some 1 else (if s = 1 then some 1 else (if s = 2 then some 1 else (if s = 3 then some 1 else (if s = 4 then some 1 else (some 1))))) else (if a = 1 then if s = 0 then some 2 else (if s = 1 then some 3 else (if s = 2 then some 2 else (if s = 3 then some 2 else (if s = 4 then some 2 else (some 2))))) else (if a = 2 then if s = 0 then some 0 else (if s = 1 then some 0 else (if s = 2 then some 4 else (if s = 3 then some 5 else (if s = 4 then some 0 else (some 0))))) else (if s = 0 then some 0 else (if s = 1 then some 0 else (if s = 2 then some 0 else (if s = 3 then some 0 else (if s = 4 then some 0 else (some 0))))))))
def experiment (i j : Fin 6) : List (Fin 4) := if i = 0 then if j = 0 then [] else (if j = 1 then [1] else (if j = 2 then [2] else (if j = 3 then [] else (if j = 4 then [] else ([]))))) else (if i = 1 then if j = 0 then [1] else (if j = 1 then [] else (if j = 2 then [1] else (if j = 3 then [] else (if j = 4 then [] else ([]))))) else (if i = 2 then if j = 0 then [2] else (if j = 1 then [1] else (if j = 2 then [] else (if j = 3 then [] else (if j = 4 then [] else ([]))))) else (if i = 3 then if j = 0 then [] else (if j = 1 then [] else (if j = 2 then [] else (if j = 3 then [] else (if j = 4 then [] else ([]))))) else (if i = 4 then if j = 0 then [] else (if j = 1 then [] else (if j = 2 then [] else (if j = 3 then [] else (if j = 4 then [] else ([]))))) else (if j = 0 then [] else (if j = 1 then [] else (if j = 2 then [] else (if j = 3 then [] else (if j = 4 then [] else ([]))))))))))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 6, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 6) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
#print axioms complete
end PerfectPower.CheckedSOE.Pddaa6506dde6c6acd8b153a8ea035e5ddc1c5c26ab7788eccae43bb15451834a
