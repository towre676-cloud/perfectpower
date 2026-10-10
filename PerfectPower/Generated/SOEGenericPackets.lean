import PerfectPower.SOESemantics
namespace PerfectPower.CheckedSOE.Pa5db63f224468d4a1e70eefcd5c950d18f421c944675d99618d66f7a1c33b7f3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a5db63f224468d4a1e70eefcd5c950d18f421c944675d99618d66f7a1c33b7f3; encodings are recorded in the compiler receipt.
def obs (s : Fin 3) : Fin 2 := if s = 0 then 0 else (if s = 1 then 0 else (1))
def step (s : Fin 3) (a : Fin 2) : Option (Fin 3) := if a = 0 then if s = 0 then some 1 else (if s = 1 then some 2 else (some 0)) else (if s = 0 then none else (if s = 1 then some 1 else (some 2)))
def q (s : Fin 3) : Fin 3 := if s = 0 then 0 else (if s = 1 then 1 else (2))
def out (s : Fin 3) : Fin 2 := if s = 0 then 0 else (if s = 1 then 0 else (1))
def target (s : Fin 3) (a : Fin 2) : Option (Fin 3) := if a = 0 then if s = 0 then some 1 else (if s = 1 then some 2 else (some 0)) else (if s = 0 then none else (if s = 1 then some 1 else (some 2)))
def experiment (i j : Fin 3) : List (Fin 2) := if i = 0 then if j = 0 then [] else (if j = 1 then [0] else ([])) else (if i = 1 then if j = 0 then [0] else (if j = 1 then [] else ([])) else (if j = 0 then [] else (if j = 1 then [] else ([]))))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 3, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 3) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
#print axioms complete
end PerfectPower.CheckedSOE.Pa5db63f224468d4a1e70eefcd5c950d18f421c944675d99618d66f7a1c33b7f3

namespace PerfectPower.CheckedSOE.P3d1786bcba8f55c26ff92609fc8ce999f1415547a881b81caf7fe22f11c91ef4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3d1786bcba8f55c26ff92609fc8ce999f1415547a881b81caf7fe22f11c91ef4; encodings are recorded in the compiler receipt.
def obs (s : Fin 4) : Fin 2 := if s = 0 then 0 else (if s = 1 then 0 else (if s = 2 then 0 else (1)))
def step (s : Fin 4) (a : Fin 2) : Option (Fin 4) := if a = 0 then if s = 0 then some 0 else (if s = 1 then some 1 else (if s = 2 then some 3 else (some 3))) else (if s = 0 then some 0 else (if s = 1 then some 3 else (if s = 2 then some 2 else (some 3))))
def q (s : Fin 4) : Fin 4 := if s = 0 then 0 else (if s = 1 then 1 else (if s = 2 then 2 else (3)))
def out (s : Fin 4) : Fin 2 := if s = 0 then 0 else (if s = 1 then 0 else (if s = 2 then 0 else (1)))
def target (s : Fin 4) (a : Fin 2) : Option (Fin 4) := if a = 0 then if s = 0 then some 0 else (if s = 1 then some 1 else (if s = 2 then some 3 else (some 3))) else (if s = 0 then some 0 else (if s = 1 then some 3 else (if s = 2 then some 2 else (some 3))))
def experiment (i j : Fin 4) : List (Fin 2) := if i = 0 then if j = 0 then [] else (if j = 1 then [1] else (if j = 2 then [0] else ([]))) else (if i = 1 then if j = 0 then [1] else (if j = 1 then [] else (if j = 2 then [0] else ([]))) else (if i = 2 then if j = 0 then [0] else (if j = 1 then [0] else (if j = 2 then [] else ([]))) else (if j = 0 then [] else (if j = 1 then [] else (if j = 2 then [] else ([]))))))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 4, i ≠ j →
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
end PerfectPower.CheckedSOE.P3d1786bcba8f55c26ff92609fc8ce999f1415547a881b81caf7fe22f11c91ef4

namespace PerfectPower.CheckedSOE.P10bd96dfe2526f87dde7880cd84bba06ab8770c0975e395b383a6c71f8c2e1db
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 10bd96dfe2526f87dde7880cd84bba06ab8770c0975e395b383a6c71f8c2e1db; encodings are recorded in the compiler receipt.
def obs (s : Fin 4) : Fin 3 := if s = 0 then 2 else (if s = 1 then 2 else (if s = 2 then 1 else (0)))
def step (s : Fin 4) (a : Fin 3) : Option (Fin 4) := if a = 0 then if s = 0 then some 1 else (if s = 1 then some 0 else (if s = 2 then some 3 else (some 2))) else (if a = 1 then if s = 0 then none else (if s = 1 then none else (if s = 2 then some 2 else (some 3))) else (if s = 0 then some 0 else (if s = 1 then some 0 else (if s = 2 then some 0 else (some 0)))))
def q (s : Fin 4) : Fin 3 := if s = 0 then 0 else (if s = 1 then 0 else (if s = 2 then 1 else (2)))
def out (s : Fin 3) : Fin 3 := if s = 0 then 2 else (if s = 1 then 1 else (0))
def target (s : Fin 3) (a : Fin 3) : Option (Fin 3) := if a = 0 then if s = 0 then some 0 else (if s = 1 then some 2 else (some 1)) else (if a = 1 then if s = 0 then none else (if s = 1 then some 1 else (some 2)) else (if s = 0 then some 0 else (if s = 1 then some 0 else (some 0))))
def experiment (i j : Fin 3) : List (Fin 3) := if i = 0 then if j = 0 then [] else (if j = 1 then [] else ([])) else (if i = 1 then if j = 0 then [] else (if j = 1 then [] else ([])) else (if j = 0 then [] else (if j = 1 then [] else ([]))))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 3, i ≠ j →
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
end PerfectPower.CheckedSOE.P10bd96dfe2526f87dde7880cd84bba06ab8770c0975e395b383a6c71f8c2e1db
