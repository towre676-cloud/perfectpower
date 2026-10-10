import PerfectPower.SOESemantics
namespace PerfectPower.CheckedSOE.P72cb0a1ab42d3576c7f5e6eda35812287be0276a9c0101b516cb38639440fc4c
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 72cb0a1ab42d3576c7f5e6eda35812287be0276a9c0101b516cb38639440fc4c; encodings are recorded in the compiler receipt.
def obs (s : Fin 4) : Fin 2 := if s = 0 then 1 else (if s = 1 then 0 else (if s = 2 then 1 else (0)))
def step (s : Fin 4) (a : Fin 2) : Option (Fin 4) := if a = 0 then if s = 0 then some 0 else (if s = 1 then some 1 else (if s = 2 then some 2 else (some 3))) else (if s = 0 then some 1 else (if s = 1 then some 0 else (if s = 2 then some 3 else (some 2))))
def q (s : Fin 4) : Fin 2 := if s = 0 then 0 else (if s = 1 then 1 else (if s = 2 then 0 else (1)))
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 4) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
#print axioms complete
end PerfectPower.CheckedSOE.P72cb0a1ab42d3576c7f5e6eda35812287be0276a9c0101b516cb38639440fc4c
