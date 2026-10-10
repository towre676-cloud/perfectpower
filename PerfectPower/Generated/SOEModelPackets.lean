import PerfectPower.SOESemantics
namespace PerfectPower.CheckedSOE.P37654be7125d0f56b4fadf7be5614ed8720fcc40dae22b8cd7b91cafb6d83104
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 37654be7125d0f56b4fadf7be5614ed8720fcc40dae22b8cd7b91cafb6d83104; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P37654be7125d0f56b4fadf7be5614ed8720fcc40dae22b8cd7b91cafb6d83104

namespace PerfectPower.SOEModelPackets
def obs000 := PerfectPower.CheckedSOE.P37654be7125d0f56b4fadf7be5614ed8720fcc40dae22b8cd7b91cafb6d83104.obs
def step000 := PerfectPower.CheckedSOE.P37654be7125d0f56b4fadf7be5614ed8720fcc40dae22b8cd7b91cafb6d83104.step
def q000 := PerfectPower.CheckedSOE.P37654be7125d0f56b4fadf7be5614ed8720fcc40dae22b8cd7b91cafb6d83104.q
def out000 := PerfectPower.CheckedSOE.P37654be7125d0f56b4fadf7be5614ed8720fcc40dae22b8cd7b91cafb6d83104.out
def target000 := PerfectPower.CheckedSOE.P37654be7125d0f56b4fadf7be5614ed8720fcc40dae22b8cd7b91cafb6d83104.target
theorem complete000 (s t : Fin 2) : SOESemantics.Equivalent step000 obs000 s t ↔ q000 s = q000 t := PerfectPower.CheckedSOE.P37654be7125d0f56b4fadf7be5614ed8720fcc40dae22b8cd7b91cafb6d83104.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pdfa4536042030a5100b7e1b10ddcf6888d16ead6dba61a38b039ad1ce77f689f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: dfa4536042030a5100b7e1b10ddcf6888d16ead6dba61a38b039ad1ce77f689f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pdfa4536042030a5100b7e1b10ddcf6888d16ead6dba61a38b039ad1ce77f689f

namespace PerfectPower.SOEModelPackets
def obs001 := PerfectPower.CheckedSOE.Pdfa4536042030a5100b7e1b10ddcf6888d16ead6dba61a38b039ad1ce77f689f.obs
def step001 := PerfectPower.CheckedSOE.Pdfa4536042030a5100b7e1b10ddcf6888d16ead6dba61a38b039ad1ce77f689f.step
def q001 := PerfectPower.CheckedSOE.Pdfa4536042030a5100b7e1b10ddcf6888d16ead6dba61a38b039ad1ce77f689f.q
def out001 := PerfectPower.CheckedSOE.Pdfa4536042030a5100b7e1b10ddcf6888d16ead6dba61a38b039ad1ce77f689f.out
def target001 := PerfectPower.CheckedSOE.Pdfa4536042030a5100b7e1b10ddcf6888d16ead6dba61a38b039ad1ce77f689f.target
theorem complete001 (s t : Fin 2) : SOESemantics.Equivalent step001 obs001 s t ↔ q001 s = q001 t := PerfectPower.CheckedSOE.Pdfa4536042030a5100b7e1b10ddcf6888d16ead6dba61a38b039ad1ce77f689f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc22f1d4a08189452fa48db514fe5a5bcb10a529a9bf10e2617c2f972a1ede1f3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c22f1d4a08189452fa48db514fe5a5bcb10a529a9bf10e2617c2f972a1ede1f3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc22f1d4a08189452fa48db514fe5a5bcb10a529a9bf10e2617c2f972a1ede1f3

namespace PerfectPower.SOEModelPackets
def obs002 := PerfectPower.CheckedSOE.Pc22f1d4a08189452fa48db514fe5a5bcb10a529a9bf10e2617c2f972a1ede1f3.obs
def step002 := PerfectPower.CheckedSOE.Pc22f1d4a08189452fa48db514fe5a5bcb10a529a9bf10e2617c2f972a1ede1f3.step
def q002 := PerfectPower.CheckedSOE.Pc22f1d4a08189452fa48db514fe5a5bcb10a529a9bf10e2617c2f972a1ede1f3.q
def out002 := PerfectPower.CheckedSOE.Pc22f1d4a08189452fa48db514fe5a5bcb10a529a9bf10e2617c2f972a1ede1f3.out
def target002 := PerfectPower.CheckedSOE.Pc22f1d4a08189452fa48db514fe5a5bcb10a529a9bf10e2617c2f972a1ede1f3.target
theorem complete002 (s t : Fin 2) : SOESemantics.Equivalent step002 obs002 s t ↔ q002 s = q002 t := PerfectPower.CheckedSOE.Pc22f1d4a08189452fa48db514fe5a5bcb10a529a9bf10e2617c2f972a1ede1f3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4861d3f7299dbb7f9473a9472ff4878265231d7b0be213ee59d8db3efdb4cfe6
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4861d3f7299dbb7f9473a9472ff4878265231d7b0be213ee59d8db3efdb4cfe6; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4861d3f7299dbb7f9473a9472ff4878265231d7b0be213ee59d8db3efdb4cfe6

namespace PerfectPower.SOEModelPackets
def obs003 := PerfectPower.CheckedSOE.P4861d3f7299dbb7f9473a9472ff4878265231d7b0be213ee59d8db3efdb4cfe6.obs
def step003 := PerfectPower.CheckedSOE.P4861d3f7299dbb7f9473a9472ff4878265231d7b0be213ee59d8db3efdb4cfe6.step
def q003 := PerfectPower.CheckedSOE.P4861d3f7299dbb7f9473a9472ff4878265231d7b0be213ee59d8db3efdb4cfe6.q
def out003 := PerfectPower.CheckedSOE.P4861d3f7299dbb7f9473a9472ff4878265231d7b0be213ee59d8db3efdb4cfe6.out
def target003 := PerfectPower.CheckedSOE.P4861d3f7299dbb7f9473a9472ff4878265231d7b0be213ee59d8db3efdb4cfe6.target
theorem complete003 (s t : Fin 2) : SOESemantics.Equivalent step003 obs003 s t ↔ q003 s = q003 t := PerfectPower.CheckedSOE.P4861d3f7299dbb7f9473a9472ff4878265231d7b0be213ee59d8db3efdb4cfe6.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa57adabd58042987fdb3df94d9f61b084644c3ac7c29c750b0c15a3b8288a2a2
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a57adabd58042987fdb3df94d9f61b084644c3ac7c29c750b0c15a3b8288a2a2; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa57adabd58042987fdb3df94d9f61b084644c3ac7c29c750b0c15a3b8288a2a2

namespace PerfectPower.SOEModelPackets
def obs004 := PerfectPower.CheckedSOE.Pa57adabd58042987fdb3df94d9f61b084644c3ac7c29c750b0c15a3b8288a2a2.obs
def step004 := PerfectPower.CheckedSOE.Pa57adabd58042987fdb3df94d9f61b084644c3ac7c29c750b0c15a3b8288a2a2.step
def q004 := PerfectPower.CheckedSOE.Pa57adabd58042987fdb3df94d9f61b084644c3ac7c29c750b0c15a3b8288a2a2.q
def out004 := PerfectPower.CheckedSOE.Pa57adabd58042987fdb3df94d9f61b084644c3ac7c29c750b0c15a3b8288a2a2.out
def target004 := PerfectPower.CheckedSOE.Pa57adabd58042987fdb3df94d9f61b084644c3ac7c29c750b0c15a3b8288a2a2.target
theorem complete004 (s t : Fin 2) : SOESemantics.Equivalent step004 obs004 s t ↔ q004 s = q004 t := PerfectPower.CheckedSOE.Pa57adabd58042987fdb3df94d9f61b084644c3ac7c29c750b0c15a3b8288a2a2.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd4cf067243beac18adc85fe2b952866d4d9a55a46450b88ba8e50b135900dd55
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d4cf067243beac18adc85fe2b952866d4d9a55a46450b88ba8e50b135900dd55; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd4cf067243beac18adc85fe2b952866d4d9a55a46450b88ba8e50b135900dd55

namespace PerfectPower.SOEModelPackets
def obs005 := PerfectPower.CheckedSOE.Pd4cf067243beac18adc85fe2b952866d4d9a55a46450b88ba8e50b135900dd55.obs
def step005 := PerfectPower.CheckedSOE.Pd4cf067243beac18adc85fe2b952866d4d9a55a46450b88ba8e50b135900dd55.step
def q005 := PerfectPower.CheckedSOE.Pd4cf067243beac18adc85fe2b952866d4d9a55a46450b88ba8e50b135900dd55.q
def out005 := PerfectPower.CheckedSOE.Pd4cf067243beac18adc85fe2b952866d4d9a55a46450b88ba8e50b135900dd55.out
def target005 := PerfectPower.CheckedSOE.Pd4cf067243beac18adc85fe2b952866d4d9a55a46450b88ba8e50b135900dd55.target
theorem complete005 (s t : Fin 2) : SOESemantics.Equivalent step005 obs005 s t ↔ q005 s = q005 t := PerfectPower.CheckedSOE.Pd4cf067243beac18adc85fe2b952866d4d9a55a46450b88ba8e50b135900dd55.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0490184fbd1b499c21ffa0c5f59d0294b56418bac7bfa52ae9d3a1eb1bbee0a0
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0490184fbd1b499c21ffa0c5f59d0294b56418bac7bfa52ae9d3a1eb1bbee0a0; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0490184fbd1b499c21ffa0c5f59d0294b56418bac7bfa52ae9d3a1eb1bbee0a0

namespace PerfectPower.SOEModelPackets
def obs006 := PerfectPower.CheckedSOE.P0490184fbd1b499c21ffa0c5f59d0294b56418bac7bfa52ae9d3a1eb1bbee0a0.obs
def step006 := PerfectPower.CheckedSOE.P0490184fbd1b499c21ffa0c5f59d0294b56418bac7bfa52ae9d3a1eb1bbee0a0.step
def q006 := PerfectPower.CheckedSOE.P0490184fbd1b499c21ffa0c5f59d0294b56418bac7bfa52ae9d3a1eb1bbee0a0.q
def out006 := PerfectPower.CheckedSOE.P0490184fbd1b499c21ffa0c5f59d0294b56418bac7bfa52ae9d3a1eb1bbee0a0.out
def target006 := PerfectPower.CheckedSOE.P0490184fbd1b499c21ffa0c5f59d0294b56418bac7bfa52ae9d3a1eb1bbee0a0.target
theorem complete006 (s t : Fin 2) : SOESemantics.Equivalent step006 obs006 s t ↔ q006 s = q006 t := PerfectPower.CheckedSOE.P0490184fbd1b499c21ffa0c5f59d0294b56418bac7bfa52ae9d3a1eb1bbee0a0.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P771bfd918b584f624345862642c6e5d127691b75fbf5bdeb3ea8194a133c7da1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 771bfd918b584f624345862642c6e5d127691b75fbf5bdeb3ea8194a133c7da1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P771bfd918b584f624345862642c6e5d127691b75fbf5bdeb3ea8194a133c7da1

namespace PerfectPower.SOEModelPackets
def obs007 := PerfectPower.CheckedSOE.P771bfd918b584f624345862642c6e5d127691b75fbf5bdeb3ea8194a133c7da1.obs
def step007 := PerfectPower.CheckedSOE.P771bfd918b584f624345862642c6e5d127691b75fbf5bdeb3ea8194a133c7da1.step
def q007 := PerfectPower.CheckedSOE.P771bfd918b584f624345862642c6e5d127691b75fbf5bdeb3ea8194a133c7da1.q
def out007 := PerfectPower.CheckedSOE.P771bfd918b584f624345862642c6e5d127691b75fbf5bdeb3ea8194a133c7da1.out
def target007 := PerfectPower.CheckedSOE.P771bfd918b584f624345862642c6e5d127691b75fbf5bdeb3ea8194a133c7da1.target
theorem complete007 (s t : Fin 2) : SOESemantics.Equivalent step007 obs007 s t ↔ q007 s = q007 t := PerfectPower.CheckedSOE.P771bfd918b584f624345862642c6e5d127691b75fbf5bdeb3ea8194a133c7da1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb69f0323a12aacc24ad74fa14d728dd233999c74ed221fce5f20879f52437063
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b69f0323a12aacc24ad74fa14d728dd233999c74ed221fce5f20879f52437063; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb69f0323a12aacc24ad74fa14d728dd233999c74ed221fce5f20879f52437063

namespace PerfectPower.SOEModelPackets
def obs008 := PerfectPower.CheckedSOE.Pb69f0323a12aacc24ad74fa14d728dd233999c74ed221fce5f20879f52437063.obs
def step008 := PerfectPower.CheckedSOE.Pb69f0323a12aacc24ad74fa14d728dd233999c74ed221fce5f20879f52437063.step
def q008 := PerfectPower.CheckedSOE.Pb69f0323a12aacc24ad74fa14d728dd233999c74ed221fce5f20879f52437063.q
def out008 := PerfectPower.CheckedSOE.Pb69f0323a12aacc24ad74fa14d728dd233999c74ed221fce5f20879f52437063.out
def target008 := PerfectPower.CheckedSOE.Pb69f0323a12aacc24ad74fa14d728dd233999c74ed221fce5f20879f52437063.target
theorem complete008 (s t : Fin 2) : SOESemantics.Equivalent step008 obs008 s t ↔ q008 s = q008 t := PerfectPower.CheckedSOE.Pb69f0323a12aacc24ad74fa14d728dd233999c74ed221fce5f20879f52437063.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0651007c610870dd64a1561638865deb65538a6cf576ab129a27e24fbf572d14
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0651007c610870dd64a1561638865deb65538a6cf576ab129a27e24fbf572d14; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0651007c610870dd64a1561638865deb65538a6cf576ab129a27e24fbf572d14

namespace PerfectPower.SOEModelPackets
def obs009 := PerfectPower.CheckedSOE.P0651007c610870dd64a1561638865deb65538a6cf576ab129a27e24fbf572d14.obs
def step009 := PerfectPower.CheckedSOE.P0651007c610870dd64a1561638865deb65538a6cf576ab129a27e24fbf572d14.step
def q009 := PerfectPower.CheckedSOE.P0651007c610870dd64a1561638865deb65538a6cf576ab129a27e24fbf572d14.q
def out009 := PerfectPower.CheckedSOE.P0651007c610870dd64a1561638865deb65538a6cf576ab129a27e24fbf572d14.out
def target009 := PerfectPower.CheckedSOE.P0651007c610870dd64a1561638865deb65538a6cf576ab129a27e24fbf572d14.target
theorem complete009 (s t : Fin 2) : SOESemantics.Equivalent step009 obs009 s t ↔ q009 s = q009 t := PerfectPower.CheckedSOE.P0651007c610870dd64a1561638865deb65538a6cf576ab129a27e24fbf572d14.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb19a0751dc8e20a5e6d6f843f4e88f14a57f64c33ba81497b933bd5b2704dcd3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b19a0751dc8e20a5e6d6f843f4e88f14a57f64c33ba81497b933bd5b2704dcd3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb19a0751dc8e20a5e6d6f843f4e88f14a57f64c33ba81497b933bd5b2704dcd3

namespace PerfectPower.SOEModelPackets
def obs010 := PerfectPower.CheckedSOE.Pb19a0751dc8e20a5e6d6f843f4e88f14a57f64c33ba81497b933bd5b2704dcd3.obs
def step010 := PerfectPower.CheckedSOE.Pb19a0751dc8e20a5e6d6f843f4e88f14a57f64c33ba81497b933bd5b2704dcd3.step
def q010 := PerfectPower.CheckedSOE.Pb19a0751dc8e20a5e6d6f843f4e88f14a57f64c33ba81497b933bd5b2704dcd3.q
def out010 := PerfectPower.CheckedSOE.Pb19a0751dc8e20a5e6d6f843f4e88f14a57f64c33ba81497b933bd5b2704dcd3.out
def target010 := PerfectPower.CheckedSOE.Pb19a0751dc8e20a5e6d6f843f4e88f14a57f64c33ba81497b933bd5b2704dcd3.target
theorem complete010 (s t : Fin 2) : SOESemantics.Equivalent step010 obs010 s t ↔ q010 s = q010 t := PerfectPower.CheckedSOE.Pb19a0751dc8e20a5e6d6f843f4e88f14a57f64c33ba81497b933bd5b2704dcd3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P993ae8ed55d3356087543f0329901f711ba8c2178eca8942f429e8a2fce5b842
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 993ae8ed55d3356087543f0329901f711ba8c2178eca8942f429e8a2fce5b842; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P993ae8ed55d3356087543f0329901f711ba8c2178eca8942f429e8a2fce5b842

namespace PerfectPower.SOEModelPackets
def obs011 := PerfectPower.CheckedSOE.P993ae8ed55d3356087543f0329901f711ba8c2178eca8942f429e8a2fce5b842.obs
def step011 := PerfectPower.CheckedSOE.P993ae8ed55d3356087543f0329901f711ba8c2178eca8942f429e8a2fce5b842.step
def q011 := PerfectPower.CheckedSOE.P993ae8ed55d3356087543f0329901f711ba8c2178eca8942f429e8a2fce5b842.q
def out011 := PerfectPower.CheckedSOE.P993ae8ed55d3356087543f0329901f711ba8c2178eca8942f429e8a2fce5b842.out
def target011 := PerfectPower.CheckedSOE.P993ae8ed55d3356087543f0329901f711ba8c2178eca8942f429e8a2fce5b842.target
theorem complete011 (s t : Fin 2) : SOESemantics.Equivalent step011 obs011 s t ↔ q011 s = q011 t := PerfectPower.CheckedSOE.P993ae8ed55d3356087543f0329901f711ba8c2178eca8942f429e8a2fce5b842.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf11638f8a7b94ebdd201cdd056cc7e09f463650af1dbef8393be80ceec0bd17f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f11638f8a7b94ebdd201cdd056cc7e09f463650af1dbef8393be80ceec0bd17f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf11638f8a7b94ebdd201cdd056cc7e09f463650af1dbef8393be80ceec0bd17f

namespace PerfectPower.SOEModelPackets
def obs012 := PerfectPower.CheckedSOE.Pf11638f8a7b94ebdd201cdd056cc7e09f463650af1dbef8393be80ceec0bd17f.obs
def step012 := PerfectPower.CheckedSOE.Pf11638f8a7b94ebdd201cdd056cc7e09f463650af1dbef8393be80ceec0bd17f.step
def q012 := PerfectPower.CheckedSOE.Pf11638f8a7b94ebdd201cdd056cc7e09f463650af1dbef8393be80ceec0bd17f.q
def out012 := PerfectPower.CheckedSOE.Pf11638f8a7b94ebdd201cdd056cc7e09f463650af1dbef8393be80ceec0bd17f.out
def target012 := PerfectPower.CheckedSOE.Pf11638f8a7b94ebdd201cdd056cc7e09f463650af1dbef8393be80ceec0bd17f.target
theorem complete012 (s t : Fin 2) : SOESemantics.Equivalent step012 obs012 s t ↔ q012 s = q012 t := PerfectPower.CheckedSOE.Pf11638f8a7b94ebdd201cdd056cc7e09f463650af1dbef8393be80ceec0bd17f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4853dbebbc03fb45e5e6caf5ea2a8229adc8ed77d802412962d4b0a1c08e9e58
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4853dbebbc03fb45e5e6caf5ea2a8229adc8ed77d802412962d4b0a1c08e9e58; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4853dbebbc03fb45e5e6caf5ea2a8229adc8ed77d802412962d4b0a1c08e9e58

namespace PerfectPower.SOEModelPackets
def obs013 := PerfectPower.CheckedSOE.P4853dbebbc03fb45e5e6caf5ea2a8229adc8ed77d802412962d4b0a1c08e9e58.obs
def step013 := PerfectPower.CheckedSOE.P4853dbebbc03fb45e5e6caf5ea2a8229adc8ed77d802412962d4b0a1c08e9e58.step
def q013 := PerfectPower.CheckedSOE.P4853dbebbc03fb45e5e6caf5ea2a8229adc8ed77d802412962d4b0a1c08e9e58.q
def out013 := PerfectPower.CheckedSOE.P4853dbebbc03fb45e5e6caf5ea2a8229adc8ed77d802412962d4b0a1c08e9e58.out
def target013 := PerfectPower.CheckedSOE.P4853dbebbc03fb45e5e6caf5ea2a8229adc8ed77d802412962d4b0a1c08e9e58.target
theorem complete013 (s t : Fin 2) : SOESemantics.Equivalent step013 obs013 s t ↔ q013 s = q013 t := PerfectPower.CheckedSOE.P4853dbebbc03fb45e5e6caf5ea2a8229adc8ed77d802412962d4b0a1c08e9e58.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P68a4c10fe9b000827abfa56fa740173f0d116cc97f08f00c694d4126cb14746f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 68a4c10fe9b000827abfa56fa740173f0d116cc97f08f00c694d4126cb14746f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P68a4c10fe9b000827abfa56fa740173f0d116cc97f08f00c694d4126cb14746f

namespace PerfectPower.SOEModelPackets
def obs014 := PerfectPower.CheckedSOE.P68a4c10fe9b000827abfa56fa740173f0d116cc97f08f00c694d4126cb14746f.obs
def step014 := PerfectPower.CheckedSOE.P68a4c10fe9b000827abfa56fa740173f0d116cc97f08f00c694d4126cb14746f.step
def q014 := PerfectPower.CheckedSOE.P68a4c10fe9b000827abfa56fa740173f0d116cc97f08f00c694d4126cb14746f.q
def out014 := PerfectPower.CheckedSOE.P68a4c10fe9b000827abfa56fa740173f0d116cc97f08f00c694d4126cb14746f.out
def target014 := PerfectPower.CheckedSOE.P68a4c10fe9b000827abfa56fa740173f0d116cc97f08f00c694d4126cb14746f.target
theorem complete014 (s t : Fin 2) : SOESemantics.Equivalent step014 obs014 s t ↔ q014 s = q014 t := PerfectPower.CheckedSOE.P68a4c10fe9b000827abfa56fa740173f0d116cc97f08f00c694d4126cb14746f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbf632f3e55b764413946864bc8cd1a2053a8639afcb55d10b137b5d691872fa8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: bf632f3e55b764413946864bc8cd1a2053a8639afcb55d10b137b5d691872fa8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbf632f3e55b764413946864bc8cd1a2053a8639afcb55d10b137b5d691872fa8

namespace PerfectPower.SOEModelPackets
def obs015 := PerfectPower.CheckedSOE.Pbf632f3e55b764413946864bc8cd1a2053a8639afcb55d10b137b5d691872fa8.obs
def step015 := PerfectPower.CheckedSOE.Pbf632f3e55b764413946864bc8cd1a2053a8639afcb55d10b137b5d691872fa8.step
def q015 := PerfectPower.CheckedSOE.Pbf632f3e55b764413946864bc8cd1a2053a8639afcb55d10b137b5d691872fa8.q
def out015 := PerfectPower.CheckedSOE.Pbf632f3e55b764413946864bc8cd1a2053a8639afcb55d10b137b5d691872fa8.out
def target015 := PerfectPower.CheckedSOE.Pbf632f3e55b764413946864bc8cd1a2053a8639afcb55d10b137b5d691872fa8.target
theorem complete015 (s t : Fin 2) : SOESemantics.Equivalent step015 obs015 s t ↔ q015 s = q015 t := PerfectPower.CheckedSOE.Pbf632f3e55b764413946864bc8cd1a2053a8639afcb55d10b137b5d691872fa8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Paf8a123f495faa77bae1249d0d969de4c1986b5b2e45218bd568ff1ebfc0529f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: af8a123f495faa77bae1249d0d969de4c1986b5b2e45218bd568ff1ebfc0529f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Paf8a123f495faa77bae1249d0d969de4c1986b5b2e45218bd568ff1ebfc0529f

namespace PerfectPower.SOEModelPackets
def obs016 := PerfectPower.CheckedSOE.Paf8a123f495faa77bae1249d0d969de4c1986b5b2e45218bd568ff1ebfc0529f.obs
def step016 := PerfectPower.CheckedSOE.Paf8a123f495faa77bae1249d0d969de4c1986b5b2e45218bd568ff1ebfc0529f.step
def q016 := PerfectPower.CheckedSOE.Paf8a123f495faa77bae1249d0d969de4c1986b5b2e45218bd568ff1ebfc0529f.q
def out016 := PerfectPower.CheckedSOE.Paf8a123f495faa77bae1249d0d969de4c1986b5b2e45218bd568ff1ebfc0529f.out
def target016 := PerfectPower.CheckedSOE.Paf8a123f495faa77bae1249d0d969de4c1986b5b2e45218bd568ff1ebfc0529f.target
theorem complete016 (s t : Fin 2) : SOESemantics.Equivalent step016 obs016 s t ↔ q016 s = q016 t := PerfectPower.CheckedSOE.Paf8a123f495faa77bae1249d0d969de4c1986b5b2e45218bd568ff1ebfc0529f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P35d8cd3b9e231d72cdb559488deaa10d4dd2b0972725f1a49f2f26bb28432e20
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 35d8cd3b9e231d72cdb559488deaa10d4dd2b0972725f1a49f2f26bb28432e20; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P35d8cd3b9e231d72cdb559488deaa10d4dd2b0972725f1a49f2f26bb28432e20

namespace PerfectPower.SOEModelPackets
def obs017 := PerfectPower.CheckedSOE.P35d8cd3b9e231d72cdb559488deaa10d4dd2b0972725f1a49f2f26bb28432e20.obs
def step017 := PerfectPower.CheckedSOE.P35d8cd3b9e231d72cdb559488deaa10d4dd2b0972725f1a49f2f26bb28432e20.step
def q017 := PerfectPower.CheckedSOE.P35d8cd3b9e231d72cdb559488deaa10d4dd2b0972725f1a49f2f26bb28432e20.q
def out017 := PerfectPower.CheckedSOE.P35d8cd3b9e231d72cdb559488deaa10d4dd2b0972725f1a49f2f26bb28432e20.out
def target017 := PerfectPower.CheckedSOE.P35d8cd3b9e231d72cdb559488deaa10d4dd2b0972725f1a49f2f26bb28432e20.target
theorem complete017 (s t : Fin 2) : SOESemantics.Equivalent step017 obs017 s t ↔ q017 s = q017 t := PerfectPower.CheckedSOE.P35d8cd3b9e231d72cdb559488deaa10d4dd2b0972725f1a49f2f26bb28432e20.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf8e0fee63c2438d2ecd80630b97d78b78f676c5843e1ae385b8814d179e595d8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f8e0fee63c2438d2ecd80630b97d78b78f676c5843e1ae385b8814d179e595d8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf8e0fee63c2438d2ecd80630b97d78b78f676c5843e1ae385b8814d179e595d8

namespace PerfectPower.SOEModelPackets
def obs018 := PerfectPower.CheckedSOE.Pf8e0fee63c2438d2ecd80630b97d78b78f676c5843e1ae385b8814d179e595d8.obs
def step018 := PerfectPower.CheckedSOE.Pf8e0fee63c2438d2ecd80630b97d78b78f676c5843e1ae385b8814d179e595d8.step
def q018 := PerfectPower.CheckedSOE.Pf8e0fee63c2438d2ecd80630b97d78b78f676c5843e1ae385b8814d179e595d8.q
def out018 := PerfectPower.CheckedSOE.Pf8e0fee63c2438d2ecd80630b97d78b78f676c5843e1ae385b8814d179e595d8.out
def target018 := PerfectPower.CheckedSOE.Pf8e0fee63c2438d2ecd80630b97d78b78f676c5843e1ae385b8814d179e595d8.target
theorem complete018 (s t : Fin 2) : SOESemantics.Equivalent step018 obs018 s t ↔ q018 s = q018 t := PerfectPower.CheckedSOE.Pf8e0fee63c2438d2ecd80630b97d78b78f676c5843e1ae385b8814d179e595d8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf92e7ad6bd421e20ebd7623056c49c88d0aef3317b54dd6137d4dffae0d1c24d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f92e7ad6bd421e20ebd7623056c49c88d0aef3317b54dd6137d4dffae0d1c24d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf92e7ad6bd421e20ebd7623056c49c88d0aef3317b54dd6137d4dffae0d1c24d

namespace PerfectPower.SOEModelPackets
def obs019 := PerfectPower.CheckedSOE.Pf92e7ad6bd421e20ebd7623056c49c88d0aef3317b54dd6137d4dffae0d1c24d.obs
def step019 := PerfectPower.CheckedSOE.Pf92e7ad6bd421e20ebd7623056c49c88d0aef3317b54dd6137d4dffae0d1c24d.step
def q019 := PerfectPower.CheckedSOE.Pf92e7ad6bd421e20ebd7623056c49c88d0aef3317b54dd6137d4dffae0d1c24d.q
def out019 := PerfectPower.CheckedSOE.Pf92e7ad6bd421e20ebd7623056c49c88d0aef3317b54dd6137d4dffae0d1c24d.out
def target019 := PerfectPower.CheckedSOE.Pf92e7ad6bd421e20ebd7623056c49c88d0aef3317b54dd6137d4dffae0d1c24d.target
theorem complete019 (s t : Fin 2) : SOESemantics.Equivalent step019 obs019 s t ↔ q019 s = q019 t := PerfectPower.CheckedSOE.Pf92e7ad6bd421e20ebd7623056c49c88d0aef3317b54dd6137d4dffae0d1c24d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa5970bc08517bbd8c69fb121c989c0041a3dd3f05de4148b380ad9fae3255f3b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a5970bc08517bbd8c69fb121c989c0041a3dd3f05de4148b380ad9fae3255f3b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa5970bc08517bbd8c69fb121c989c0041a3dd3f05de4148b380ad9fae3255f3b

namespace PerfectPower.SOEModelPackets
def obs020 := PerfectPower.CheckedSOE.Pa5970bc08517bbd8c69fb121c989c0041a3dd3f05de4148b380ad9fae3255f3b.obs
def step020 := PerfectPower.CheckedSOE.Pa5970bc08517bbd8c69fb121c989c0041a3dd3f05de4148b380ad9fae3255f3b.step
def q020 := PerfectPower.CheckedSOE.Pa5970bc08517bbd8c69fb121c989c0041a3dd3f05de4148b380ad9fae3255f3b.q
def out020 := PerfectPower.CheckedSOE.Pa5970bc08517bbd8c69fb121c989c0041a3dd3f05de4148b380ad9fae3255f3b.out
def target020 := PerfectPower.CheckedSOE.Pa5970bc08517bbd8c69fb121c989c0041a3dd3f05de4148b380ad9fae3255f3b.target
theorem complete020 (s t : Fin 2) : SOESemantics.Equivalent step020 obs020 s t ↔ q020 s = q020 t := PerfectPower.CheckedSOE.Pa5970bc08517bbd8c69fb121c989c0041a3dd3f05de4148b380ad9fae3255f3b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P252632fdaa097b39ff06341d0636d2f4ebb30f3a6b180b84baf8a48cd75ec8dd
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 252632fdaa097b39ff06341d0636d2f4ebb30f3a6b180b84baf8a48cd75ec8dd; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P252632fdaa097b39ff06341d0636d2f4ebb30f3a6b180b84baf8a48cd75ec8dd

namespace PerfectPower.SOEModelPackets
def obs021 := PerfectPower.CheckedSOE.P252632fdaa097b39ff06341d0636d2f4ebb30f3a6b180b84baf8a48cd75ec8dd.obs
def step021 := PerfectPower.CheckedSOE.P252632fdaa097b39ff06341d0636d2f4ebb30f3a6b180b84baf8a48cd75ec8dd.step
def q021 := PerfectPower.CheckedSOE.P252632fdaa097b39ff06341d0636d2f4ebb30f3a6b180b84baf8a48cd75ec8dd.q
def out021 := PerfectPower.CheckedSOE.P252632fdaa097b39ff06341d0636d2f4ebb30f3a6b180b84baf8a48cd75ec8dd.out
def target021 := PerfectPower.CheckedSOE.P252632fdaa097b39ff06341d0636d2f4ebb30f3a6b180b84baf8a48cd75ec8dd.target
theorem complete021 (s t : Fin 2) : SOESemantics.Equivalent step021 obs021 s t ↔ q021 s = q021 t := PerfectPower.CheckedSOE.P252632fdaa097b39ff06341d0636d2f4ebb30f3a6b180b84baf8a48cd75ec8dd.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0212fb35fcce234fcc6a27036dedb6c2478c99372d284af8b325229161661c49
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0212fb35fcce234fcc6a27036dedb6c2478c99372d284af8b325229161661c49; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0212fb35fcce234fcc6a27036dedb6c2478c99372d284af8b325229161661c49

namespace PerfectPower.SOEModelPackets
def obs022 := PerfectPower.CheckedSOE.P0212fb35fcce234fcc6a27036dedb6c2478c99372d284af8b325229161661c49.obs
def step022 := PerfectPower.CheckedSOE.P0212fb35fcce234fcc6a27036dedb6c2478c99372d284af8b325229161661c49.step
def q022 := PerfectPower.CheckedSOE.P0212fb35fcce234fcc6a27036dedb6c2478c99372d284af8b325229161661c49.q
def out022 := PerfectPower.CheckedSOE.P0212fb35fcce234fcc6a27036dedb6c2478c99372d284af8b325229161661c49.out
def target022 := PerfectPower.CheckedSOE.P0212fb35fcce234fcc6a27036dedb6c2478c99372d284af8b325229161661c49.target
theorem complete022 (s t : Fin 2) : SOESemantics.Equivalent step022 obs022 s t ↔ q022 s = q022 t := PerfectPower.CheckedSOE.P0212fb35fcce234fcc6a27036dedb6c2478c99372d284af8b325229161661c49.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf566a0cea6dbfd4e9874af0c38609b44fc4121efd7cdc2b01b298895187bc839
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f566a0cea6dbfd4e9874af0c38609b44fc4121efd7cdc2b01b298895187bc839; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf566a0cea6dbfd4e9874af0c38609b44fc4121efd7cdc2b01b298895187bc839

namespace PerfectPower.SOEModelPackets
def obs023 := PerfectPower.CheckedSOE.Pf566a0cea6dbfd4e9874af0c38609b44fc4121efd7cdc2b01b298895187bc839.obs
def step023 := PerfectPower.CheckedSOE.Pf566a0cea6dbfd4e9874af0c38609b44fc4121efd7cdc2b01b298895187bc839.step
def q023 := PerfectPower.CheckedSOE.Pf566a0cea6dbfd4e9874af0c38609b44fc4121efd7cdc2b01b298895187bc839.q
def out023 := PerfectPower.CheckedSOE.Pf566a0cea6dbfd4e9874af0c38609b44fc4121efd7cdc2b01b298895187bc839.out
def target023 := PerfectPower.CheckedSOE.Pf566a0cea6dbfd4e9874af0c38609b44fc4121efd7cdc2b01b298895187bc839.target
theorem complete023 (s t : Fin 2) : SOESemantics.Equivalent step023 obs023 s t ↔ q023 s = q023 t := PerfectPower.CheckedSOE.Pf566a0cea6dbfd4e9874af0c38609b44fc4121efd7cdc2b01b298895187bc839.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P34c99e7066b5ff0eb4c05ea2dd4ad9f246c452140693e9ad9fab5e5ba914cd1f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 34c99e7066b5ff0eb4c05ea2dd4ad9f246c452140693e9ad9fab5e5ba914cd1f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P34c99e7066b5ff0eb4c05ea2dd4ad9f246c452140693e9ad9fab5e5ba914cd1f

namespace PerfectPower.SOEModelPackets
def obs024 := PerfectPower.CheckedSOE.P34c99e7066b5ff0eb4c05ea2dd4ad9f246c452140693e9ad9fab5e5ba914cd1f.obs
def step024 := PerfectPower.CheckedSOE.P34c99e7066b5ff0eb4c05ea2dd4ad9f246c452140693e9ad9fab5e5ba914cd1f.step
def q024 := PerfectPower.CheckedSOE.P34c99e7066b5ff0eb4c05ea2dd4ad9f246c452140693e9ad9fab5e5ba914cd1f.q
def out024 := PerfectPower.CheckedSOE.P34c99e7066b5ff0eb4c05ea2dd4ad9f246c452140693e9ad9fab5e5ba914cd1f.out
def target024 := PerfectPower.CheckedSOE.P34c99e7066b5ff0eb4c05ea2dd4ad9f246c452140693e9ad9fab5e5ba914cd1f.target
theorem complete024 (s t : Fin 2) : SOESemantics.Equivalent step024 obs024 s t ↔ q024 s = q024 t := PerfectPower.CheckedSOE.P34c99e7066b5ff0eb4c05ea2dd4ad9f246c452140693e9ad9fab5e5ba914cd1f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe51d8214e8c859d2f93d2d1a3bdaa22be73e1abdd60e4215156525bb4a4acd18
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e51d8214e8c859d2f93d2d1a3bdaa22be73e1abdd60e4215156525bb4a4acd18; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe51d8214e8c859d2f93d2d1a3bdaa22be73e1abdd60e4215156525bb4a4acd18

namespace PerfectPower.SOEModelPackets
def obs025 := PerfectPower.CheckedSOE.Pe51d8214e8c859d2f93d2d1a3bdaa22be73e1abdd60e4215156525bb4a4acd18.obs
def step025 := PerfectPower.CheckedSOE.Pe51d8214e8c859d2f93d2d1a3bdaa22be73e1abdd60e4215156525bb4a4acd18.step
def q025 := PerfectPower.CheckedSOE.Pe51d8214e8c859d2f93d2d1a3bdaa22be73e1abdd60e4215156525bb4a4acd18.q
def out025 := PerfectPower.CheckedSOE.Pe51d8214e8c859d2f93d2d1a3bdaa22be73e1abdd60e4215156525bb4a4acd18.out
def target025 := PerfectPower.CheckedSOE.Pe51d8214e8c859d2f93d2d1a3bdaa22be73e1abdd60e4215156525bb4a4acd18.target
theorem complete025 (s t : Fin 2) : SOESemantics.Equivalent step025 obs025 s t ↔ q025 s = q025 t := PerfectPower.CheckedSOE.Pe51d8214e8c859d2f93d2d1a3bdaa22be73e1abdd60e4215156525bb4a4acd18.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P43247827a08c996742f0041ca52ed13e00c3983dfcb8def8321d4da0a3c8c6c9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 43247827a08c996742f0041ca52ed13e00c3983dfcb8def8321d4da0a3c8c6c9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P43247827a08c996742f0041ca52ed13e00c3983dfcb8def8321d4da0a3c8c6c9

namespace PerfectPower.SOEModelPackets
def obs026 := PerfectPower.CheckedSOE.P43247827a08c996742f0041ca52ed13e00c3983dfcb8def8321d4da0a3c8c6c9.obs
def step026 := PerfectPower.CheckedSOE.P43247827a08c996742f0041ca52ed13e00c3983dfcb8def8321d4da0a3c8c6c9.step
def q026 := PerfectPower.CheckedSOE.P43247827a08c996742f0041ca52ed13e00c3983dfcb8def8321d4da0a3c8c6c9.q
def out026 := PerfectPower.CheckedSOE.P43247827a08c996742f0041ca52ed13e00c3983dfcb8def8321d4da0a3c8c6c9.out
def target026 := PerfectPower.CheckedSOE.P43247827a08c996742f0041ca52ed13e00c3983dfcb8def8321d4da0a3c8c6c9.target
theorem complete026 (s t : Fin 2) : SOESemantics.Equivalent step026 obs026 s t ↔ q026 s = q026 t := PerfectPower.CheckedSOE.P43247827a08c996742f0041ca52ed13e00c3983dfcb8def8321d4da0a3c8c6c9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc2ba4e43dd40bc065687f849fc7f96f36f5be7bd1faaad153739117bfea45a00
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c2ba4e43dd40bc065687f849fc7f96f36f5be7bd1faaad153739117bfea45a00; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc2ba4e43dd40bc065687f849fc7f96f36f5be7bd1faaad153739117bfea45a00

namespace PerfectPower.SOEModelPackets
def obs027 := PerfectPower.CheckedSOE.Pc2ba4e43dd40bc065687f849fc7f96f36f5be7bd1faaad153739117bfea45a00.obs
def step027 := PerfectPower.CheckedSOE.Pc2ba4e43dd40bc065687f849fc7f96f36f5be7bd1faaad153739117bfea45a00.step
def q027 := PerfectPower.CheckedSOE.Pc2ba4e43dd40bc065687f849fc7f96f36f5be7bd1faaad153739117bfea45a00.q
def out027 := PerfectPower.CheckedSOE.Pc2ba4e43dd40bc065687f849fc7f96f36f5be7bd1faaad153739117bfea45a00.out
def target027 := PerfectPower.CheckedSOE.Pc2ba4e43dd40bc065687f849fc7f96f36f5be7bd1faaad153739117bfea45a00.target
theorem complete027 (s t : Fin 2) : SOESemantics.Equivalent step027 obs027 s t ↔ q027 s = q027 t := PerfectPower.CheckedSOE.Pc2ba4e43dd40bc065687f849fc7f96f36f5be7bd1faaad153739117bfea45a00.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P387a39ad0d9e9a65e1f2f96677ad79ec7e4d270566f570be94f3c43928761cb9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 387a39ad0d9e9a65e1f2f96677ad79ec7e4d270566f570be94f3c43928761cb9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P387a39ad0d9e9a65e1f2f96677ad79ec7e4d270566f570be94f3c43928761cb9

namespace PerfectPower.SOEModelPackets
def obs028 := PerfectPower.CheckedSOE.P387a39ad0d9e9a65e1f2f96677ad79ec7e4d270566f570be94f3c43928761cb9.obs
def step028 := PerfectPower.CheckedSOE.P387a39ad0d9e9a65e1f2f96677ad79ec7e4d270566f570be94f3c43928761cb9.step
def q028 := PerfectPower.CheckedSOE.P387a39ad0d9e9a65e1f2f96677ad79ec7e4d270566f570be94f3c43928761cb9.q
def out028 := PerfectPower.CheckedSOE.P387a39ad0d9e9a65e1f2f96677ad79ec7e4d270566f570be94f3c43928761cb9.out
def target028 := PerfectPower.CheckedSOE.P387a39ad0d9e9a65e1f2f96677ad79ec7e4d270566f570be94f3c43928761cb9.target
theorem complete028 (s t : Fin 2) : SOESemantics.Equivalent step028 obs028 s t ↔ q028 s = q028 t := PerfectPower.CheckedSOE.P387a39ad0d9e9a65e1f2f96677ad79ec7e4d270566f570be94f3c43928761cb9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa4e30b0eae16ec869fd2edfe89ea8caba80e58773e97a227954d72f9a6feeb8e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a4e30b0eae16ec869fd2edfe89ea8caba80e58773e97a227954d72f9a6feeb8e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa4e30b0eae16ec869fd2edfe89ea8caba80e58773e97a227954d72f9a6feeb8e

namespace PerfectPower.SOEModelPackets
def obs029 := PerfectPower.CheckedSOE.Pa4e30b0eae16ec869fd2edfe89ea8caba80e58773e97a227954d72f9a6feeb8e.obs
def step029 := PerfectPower.CheckedSOE.Pa4e30b0eae16ec869fd2edfe89ea8caba80e58773e97a227954d72f9a6feeb8e.step
def q029 := PerfectPower.CheckedSOE.Pa4e30b0eae16ec869fd2edfe89ea8caba80e58773e97a227954d72f9a6feeb8e.q
def out029 := PerfectPower.CheckedSOE.Pa4e30b0eae16ec869fd2edfe89ea8caba80e58773e97a227954d72f9a6feeb8e.out
def target029 := PerfectPower.CheckedSOE.Pa4e30b0eae16ec869fd2edfe89ea8caba80e58773e97a227954d72f9a6feeb8e.target
theorem complete029 (s t : Fin 2) : SOESemantics.Equivalent step029 obs029 s t ↔ q029 s = q029 t := PerfectPower.CheckedSOE.Pa4e30b0eae16ec869fd2edfe89ea8caba80e58773e97a227954d72f9a6feeb8e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0eb5c62145b099b64f65ddf852f97f2898e78c0c68b6a5fe776b4bdb9261c94e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0eb5c62145b099b64f65ddf852f97f2898e78c0c68b6a5fe776b4bdb9261c94e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0eb5c62145b099b64f65ddf852f97f2898e78c0c68b6a5fe776b4bdb9261c94e

namespace PerfectPower.SOEModelPackets
def obs030 := PerfectPower.CheckedSOE.P0eb5c62145b099b64f65ddf852f97f2898e78c0c68b6a5fe776b4bdb9261c94e.obs
def step030 := PerfectPower.CheckedSOE.P0eb5c62145b099b64f65ddf852f97f2898e78c0c68b6a5fe776b4bdb9261c94e.step
def q030 := PerfectPower.CheckedSOE.P0eb5c62145b099b64f65ddf852f97f2898e78c0c68b6a5fe776b4bdb9261c94e.q
def out030 := PerfectPower.CheckedSOE.P0eb5c62145b099b64f65ddf852f97f2898e78c0c68b6a5fe776b4bdb9261c94e.out
def target030 := PerfectPower.CheckedSOE.P0eb5c62145b099b64f65ddf852f97f2898e78c0c68b6a5fe776b4bdb9261c94e.target
theorem complete030 (s t : Fin 2) : SOESemantics.Equivalent step030 obs030 s t ↔ q030 s = q030 t := PerfectPower.CheckedSOE.P0eb5c62145b099b64f65ddf852f97f2898e78c0c68b6a5fe776b4bdb9261c94e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pcabcf9043040498e22d0c5eeb0bae6d79dbef4259a0ffd336cdbf469f79f3a76
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: cabcf9043040498e22d0c5eeb0bae6d79dbef4259a0ffd336cdbf469f79f3a76; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pcabcf9043040498e22d0c5eeb0bae6d79dbef4259a0ffd336cdbf469f79f3a76

namespace PerfectPower.SOEModelPackets
def obs031 := PerfectPower.CheckedSOE.Pcabcf9043040498e22d0c5eeb0bae6d79dbef4259a0ffd336cdbf469f79f3a76.obs
def step031 := PerfectPower.CheckedSOE.Pcabcf9043040498e22d0c5eeb0bae6d79dbef4259a0ffd336cdbf469f79f3a76.step
def q031 := PerfectPower.CheckedSOE.Pcabcf9043040498e22d0c5eeb0bae6d79dbef4259a0ffd336cdbf469f79f3a76.q
def out031 := PerfectPower.CheckedSOE.Pcabcf9043040498e22d0c5eeb0bae6d79dbef4259a0ffd336cdbf469f79f3a76.out
def target031 := PerfectPower.CheckedSOE.Pcabcf9043040498e22d0c5eeb0bae6d79dbef4259a0ffd336cdbf469f79f3a76.target
theorem complete031 (s t : Fin 2) : SOESemantics.Equivalent step031 obs031 s t ↔ q031 s = q031 t := PerfectPower.CheckedSOE.Pcabcf9043040498e22d0c5eeb0bae6d79dbef4259a0ffd336cdbf469f79f3a76.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Peba5a8754d18e7d140f905728275ed1d616a9bdd3d9a4801a7f81df2fecba626
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: eba5a8754d18e7d140f905728275ed1d616a9bdd3d9a4801a7f81df2fecba626; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Peba5a8754d18e7d140f905728275ed1d616a9bdd3d9a4801a7f81df2fecba626

namespace PerfectPower.SOEModelPackets
def obs032 := PerfectPower.CheckedSOE.Peba5a8754d18e7d140f905728275ed1d616a9bdd3d9a4801a7f81df2fecba626.obs
def step032 := PerfectPower.CheckedSOE.Peba5a8754d18e7d140f905728275ed1d616a9bdd3d9a4801a7f81df2fecba626.step
def q032 := PerfectPower.CheckedSOE.Peba5a8754d18e7d140f905728275ed1d616a9bdd3d9a4801a7f81df2fecba626.q
def out032 := PerfectPower.CheckedSOE.Peba5a8754d18e7d140f905728275ed1d616a9bdd3d9a4801a7f81df2fecba626.out
def target032 := PerfectPower.CheckedSOE.Peba5a8754d18e7d140f905728275ed1d616a9bdd3d9a4801a7f81df2fecba626.target
theorem complete032 (s t : Fin 2) : SOESemantics.Equivalent step032 obs032 s t ↔ q032 s = q032 t := PerfectPower.CheckedSOE.Peba5a8754d18e7d140f905728275ed1d616a9bdd3d9a4801a7f81df2fecba626.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P90b39be6a430c2ed61e0842c40669cec289d93fecb15f5e382bf3a851daa07f4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 90b39be6a430c2ed61e0842c40669cec289d93fecb15f5e382bf3a851daa07f4; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P90b39be6a430c2ed61e0842c40669cec289d93fecb15f5e382bf3a851daa07f4

namespace PerfectPower.SOEModelPackets
def obs033 := PerfectPower.CheckedSOE.P90b39be6a430c2ed61e0842c40669cec289d93fecb15f5e382bf3a851daa07f4.obs
def step033 := PerfectPower.CheckedSOE.P90b39be6a430c2ed61e0842c40669cec289d93fecb15f5e382bf3a851daa07f4.step
def q033 := PerfectPower.CheckedSOE.P90b39be6a430c2ed61e0842c40669cec289d93fecb15f5e382bf3a851daa07f4.q
def out033 := PerfectPower.CheckedSOE.P90b39be6a430c2ed61e0842c40669cec289d93fecb15f5e382bf3a851daa07f4.out
def target033 := PerfectPower.CheckedSOE.P90b39be6a430c2ed61e0842c40669cec289d93fecb15f5e382bf3a851daa07f4.target
theorem complete033 (s t : Fin 2) : SOESemantics.Equivalent step033 obs033 s t ↔ q033 s = q033 t := PerfectPower.CheckedSOE.P90b39be6a430c2ed61e0842c40669cec289d93fecb15f5e382bf3a851daa07f4.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P94b37982105e018b1f183ad9a4d34cc1dc2417de8cd94b80c24859280fc2e0f4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 94b37982105e018b1f183ad9a4d34cc1dc2417de8cd94b80c24859280fc2e0f4; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P94b37982105e018b1f183ad9a4d34cc1dc2417de8cd94b80c24859280fc2e0f4

namespace PerfectPower.SOEModelPackets
def obs034 := PerfectPower.CheckedSOE.P94b37982105e018b1f183ad9a4d34cc1dc2417de8cd94b80c24859280fc2e0f4.obs
def step034 := PerfectPower.CheckedSOE.P94b37982105e018b1f183ad9a4d34cc1dc2417de8cd94b80c24859280fc2e0f4.step
def q034 := PerfectPower.CheckedSOE.P94b37982105e018b1f183ad9a4d34cc1dc2417de8cd94b80c24859280fc2e0f4.q
def out034 := PerfectPower.CheckedSOE.P94b37982105e018b1f183ad9a4d34cc1dc2417de8cd94b80c24859280fc2e0f4.out
def target034 := PerfectPower.CheckedSOE.P94b37982105e018b1f183ad9a4d34cc1dc2417de8cd94b80c24859280fc2e0f4.target
theorem complete034 (s t : Fin 2) : SOESemantics.Equivalent step034 obs034 s t ↔ q034 s = q034 t := PerfectPower.CheckedSOE.P94b37982105e018b1f183ad9a4d34cc1dc2417de8cd94b80c24859280fc2e0f4.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf7f2aaf78364bebdbd8a7460bd3c436c13b6f0a5330939aa632ed89c29bb3c12
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f7f2aaf78364bebdbd8a7460bd3c436c13b6f0a5330939aa632ed89c29bb3c12; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf7f2aaf78364bebdbd8a7460bd3c436c13b6f0a5330939aa632ed89c29bb3c12

namespace PerfectPower.SOEModelPackets
def obs035 := PerfectPower.CheckedSOE.Pf7f2aaf78364bebdbd8a7460bd3c436c13b6f0a5330939aa632ed89c29bb3c12.obs
def step035 := PerfectPower.CheckedSOE.Pf7f2aaf78364bebdbd8a7460bd3c436c13b6f0a5330939aa632ed89c29bb3c12.step
def q035 := PerfectPower.CheckedSOE.Pf7f2aaf78364bebdbd8a7460bd3c436c13b6f0a5330939aa632ed89c29bb3c12.q
def out035 := PerfectPower.CheckedSOE.Pf7f2aaf78364bebdbd8a7460bd3c436c13b6f0a5330939aa632ed89c29bb3c12.out
def target035 := PerfectPower.CheckedSOE.Pf7f2aaf78364bebdbd8a7460bd3c436c13b6f0a5330939aa632ed89c29bb3c12.target
theorem complete035 (s t : Fin 2) : SOESemantics.Equivalent step035 obs035 s t ↔ q035 s = q035 t := PerfectPower.CheckedSOE.Pf7f2aaf78364bebdbd8a7460bd3c436c13b6f0a5330939aa632ed89c29bb3c12.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pdc107638c50b0529f6f00e50643fc067f48684846c5d1ad5d77e80298f843a4d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: dc107638c50b0529f6f00e50643fc067f48684846c5d1ad5d77e80298f843a4d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pdc107638c50b0529f6f00e50643fc067f48684846c5d1ad5d77e80298f843a4d

namespace PerfectPower.SOEModelPackets
def obs036 := PerfectPower.CheckedSOE.Pdc107638c50b0529f6f00e50643fc067f48684846c5d1ad5d77e80298f843a4d.obs
def step036 := PerfectPower.CheckedSOE.Pdc107638c50b0529f6f00e50643fc067f48684846c5d1ad5d77e80298f843a4d.step
def q036 := PerfectPower.CheckedSOE.Pdc107638c50b0529f6f00e50643fc067f48684846c5d1ad5d77e80298f843a4d.q
def out036 := PerfectPower.CheckedSOE.Pdc107638c50b0529f6f00e50643fc067f48684846c5d1ad5d77e80298f843a4d.out
def target036 := PerfectPower.CheckedSOE.Pdc107638c50b0529f6f00e50643fc067f48684846c5d1ad5d77e80298f843a4d.target
theorem complete036 (s t : Fin 2) : SOESemantics.Equivalent step036 obs036 s t ↔ q036 s = q036 t := PerfectPower.CheckedSOE.Pdc107638c50b0529f6f00e50643fc067f48684846c5d1ad5d77e80298f843a4d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc41bdd688e03b36495f8f691144fa02809653671dadc50fffefa1833b1f90592
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c41bdd688e03b36495f8f691144fa02809653671dadc50fffefa1833b1f90592; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc41bdd688e03b36495f8f691144fa02809653671dadc50fffefa1833b1f90592

namespace PerfectPower.SOEModelPackets
def obs037 := PerfectPower.CheckedSOE.Pc41bdd688e03b36495f8f691144fa02809653671dadc50fffefa1833b1f90592.obs
def step037 := PerfectPower.CheckedSOE.Pc41bdd688e03b36495f8f691144fa02809653671dadc50fffefa1833b1f90592.step
def q037 := PerfectPower.CheckedSOE.Pc41bdd688e03b36495f8f691144fa02809653671dadc50fffefa1833b1f90592.q
def out037 := PerfectPower.CheckedSOE.Pc41bdd688e03b36495f8f691144fa02809653671dadc50fffefa1833b1f90592.out
def target037 := PerfectPower.CheckedSOE.Pc41bdd688e03b36495f8f691144fa02809653671dadc50fffefa1833b1f90592.target
theorem complete037 (s t : Fin 2) : SOESemantics.Equivalent step037 obs037 s t ↔ q037 s = q037 t := PerfectPower.CheckedSOE.Pc41bdd688e03b36495f8f691144fa02809653671dadc50fffefa1833b1f90592.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc0a9e85cd2d98acacf700ac38c4432bac79edb4de607e47a1ddaab4d44bc97d8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c0a9e85cd2d98acacf700ac38c4432bac79edb4de607e47a1ddaab4d44bc97d8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc0a9e85cd2d98acacf700ac38c4432bac79edb4de607e47a1ddaab4d44bc97d8

namespace PerfectPower.SOEModelPackets
def obs038 := PerfectPower.CheckedSOE.Pc0a9e85cd2d98acacf700ac38c4432bac79edb4de607e47a1ddaab4d44bc97d8.obs
def step038 := PerfectPower.CheckedSOE.Pc0a9e85cd2d98acacf700ac38c4432bac79edb4de607e47a1ddaab4d44bc97d8.step
def q038 := PerfectPower.CheckedSOE.Pc0a9e85cd2d98acacf700ac38c4432bac79edb4de607e47a1ddaab4d44bc97d8.q
def out038 := PerfectPower.CheckedSOE.Pc0a9e85cd2d98acacf700ac38c4432bac79edb4de607e47a1ddaab4d44bc97d8.out
def target038 := PerfectPower.CheckedSOE.Pc0a9e85cd2d98acacf700ac38c4432bac79edb4de607e47a1ddaab4d44bc97d8.target
theorem complete038 (s t : Fin 2) : SOESemantics.Equivalent step038 obs038 s t ↔ q038 s = q038 t := PerfectPower.CheckedSOE.Pc0a9e85cd2d98acacf700ac38c4432bac79edb4de607e47a1ddaab4d44bc97d8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc8c83c6a1af8327f1da8d52a922c5934f4f3bad6ba0e801a444c82224159b804
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c8c83c6a1af8327f1da8d52a922c5934f4f3bad6ba0e801a444c82224159b804; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc8c83c6a1af8327f1da8d52a922c5934f4f3bad6ba0e801a444c82224159b804

namespace PerfectPower.SOEModelPackets
def obs039 := PerfectPower.CheckedSOE.Pc8c83c6a1af8327f1da8d52a922c5934f4f3bad6ba0e801a444c82224159b804.obs
def step039 := PerfectPower.CheckedSOE.Pc8c83c6a1af8327f1da8d52a922c5934f4f3bad6ba0e801a444c82224159b804.step
def q039 := PerfectPower.CheckedSOE.Pc8c83c6a1af8327f1da8d52a922c5934f4f3bad6ba0e801a444c82224159b804.q
def out039 := PerfectPower.CheckedSOE.Pc8c83c6a1af8327f1da8d52a922c5934f4f3bad6ba0e801a444c82224159b804.out
def target039 := PerfectPower.CheckedSOE.Pc8c83c6a1af8327f1da8d52a922c5934f4f3bad6ba0e801a444c82224159b804.target
theorem complete039 (s t : Fin 2) : SOESemantics.Equivalent step039 obs039 s t ↔ q039 s = q039 t := PerfectPower.CheckedSOE.Pc8c83c6a1af8327f1da8d52a922c5934f4f3bad6ba0e801a444c82224159b804.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P65e776f7b16357848e7001782b1e64810f9d202bcdc852036e64717a3008b54e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 65e776f7b16357848e7001782b1e64810f9d202bcdc852036e64717a3008b54e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P65e776f7b16357848e7001782b1e64810f9d202bcdc852036e64717a3008b54e

namespace PerfectPower.SOEModelPackets
def obs040 := PerfectPower.CheckedSOE.P65e776f7b16357848e7001782b1e64810f9d202bcdc852036e64717a3008b54e.obs
def step040 := PerfectPower.CheckedSOE.P65e776f7b16357848e7001782b1e64810f9d202bcdc852036e64717a3008b54e.step
def q040 := PerfectPower.CheckedSOE.P65e776f7b16357848e7001782b1e64810f9d202bcdc852036e64717a3008b54e.q
def out040 := PerfectPower.CheckedSOE.P65e776f7b16357848e7001782b1e64810f9d202bcdc852036e64717a3008b54e.out
def target040 := PerfectPower.CheckedSOE.P65e776f7b16357848e7001782b1e64810f9d202bcdc852036e64717a3008b54e.target
theorem complete040 (s t : Fin 2) : SOESemantics.Equivalent step040 obs040 s t ↔ q040 s = q040 t := PerfectPower.CheckedSOE.P65e776f7b16357848e7001782b1e64810f9d202bcdc852036e64717a3008b54e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd094d055582c6cdb85ca2ba82399dd653ef83926e451b805609340c6d138a0d3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d094d055582c6cdb85ca2ba82399dd653ef83926e451b805609340c6d138a0d3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd094d055582c6cdb85ca2ba82399dd653ef83926e451b805609340c6d138a0d3

namespace PerfectPower.SOEModelPackets
def obs041 := PerfectPower.CheckedSOE.Pd094d055582c6cdb85ca2ba82399dd653ef83926e451b805609340c6d138a0d3.obs
def step041 := PerfectPower.CheckedSOE.Pd094d055582c6cdb85ca2ba82399dd653ef83926e451b805609340c6d138a0d3.step
def q041 := PerfectPower.CheckedSOE.Pd094d055582c6cdb85ca2ba82399dd653ef83926e451b805609340c6d138a0d3.q
def out041 := PerfectPower.CheckedSOE.Pd094d055582c6cdb85ca2ba82399dd653ef83926e451b805609340c6d138a0d3.out
def target041 := PerfectPower.CheckedSOE.Pd094d055582c6cdb85ca2ba82399dd653ef83926e451b805609340c6d138a0d3.target
theorem complete041 (s t : Fin 2) : SOESemantics.Equivalent step041 obs041 s t ↔ q041 s = q041 t := PerfectPower.CheckedSOE.Pd094d055582c6cdb85ca2ba82399dd653ef83926e451b805609340c6d138a0d3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0c6214e7dc98805837788529ee0fb4ab84a1e1d014069058b8aa73370391bfeb
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0c6214e7dc98805837788529ee0fb4ab84a1e1d014069058b8aa73370391bfeb; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0c6214e7dc98805837788529ee0fb4ab84a1e1d014069058b8aa73370391bfeb

namespace PerfectPower.SOEModelPackets
def obs042 := PerfectPower.CheckedSOE.P0c6214e7dc98805837788529ee0fb4ab84a1e1d014069058b8aa73370391bfeb.obs
def step042 := PerfectPower.CheckedSOE.P0c6214e7dc98805837788529ee0fb4ab84a1e1d014069058b8aa73370391bfeb.step
def q042 := PerfectPower.CheckedSOE.P0c6214e7dc98805837788529ee0fb4ab84a1e1d014069058b8aa73370391bfeb.q
def out042 := PerfectPower.CheckedSOE.P0c6214e7dc98805837788529ee0fb4ab84a1e1d014069058b8aa73370391bfeb.out
def target042 := PerfectPower.CheckedSOE.P0c6214e7dc98805837788529ee0fb4ab84a1e1d014069058b8aa73370391bfeb.target
theorem complete042 (s t : Fin 2) : SOESemantics.Equivalent step042 obs042 s t ↔ q042 s = q042 t := PerfectPower.CheckedSOE.P0c6214e7dc98805837788529ee0fb4ab84a1e1d014069058b8aa73370391bfeb.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P5f434b5188a0dd92c904114a452883dedb1a1d4d099fd04ab8e1e360af61c2af
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 5f434b5188a0dd92c904114a452883dedb1a1d4d099fd04ab8e1e360af61c2af; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P5f434b5188a0dd92c904114a452883dedb1a1d4d099fd04ab8e1e360af61c2af

namespace PerfectPower.SOEModelPackets
def obs043 := PerfectPower.CheckedSOE.P5f434b5188a0dd92c904114a452883dedb1a1d4d099fd04ab8e1e360af61c2af.obs
def step043 := PerfectPower.CheckedSOE.P5f434b5188a0dd92c904114a452883dedb1a1d4d099fd04ab8e1e360af61c2af.step
def q043 := PerfectPower.CheckedSOE.P5f434b5188a0dd92c904114a452883dedb1a1d4d099fd04ab8e1e360af61c2af.q
def out043 := PerfectPower.CheckedSOE.P5f434b5188a0dd92c904114a452883dedb1a1d4d099fd04ab8e1e360af61c2af.out
def target043 := PerfectPower.CheckedSOE.P5f434b5188a0dd92c904114a452883dedb1a1d4d099fd04ab8e1e360af61c2af.target
theorem complete043 (s t : Fin 2) : SOESemantics.Equivalent step043 obs043 s t ↔ q043 s = q043 t := PerfectPower.CheckedSOE.P5f434b5188a0dd92c904114a452883dedb1a1d4d099fd04ab8e1e360af61c2af.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc111c22dc09474773ae6513b93b6a81eca5ee8e7ba1b13ec0908282650501d9d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c111c22dc09474773ae6513b93b6a81eca5ee8e7ba1b13ec0908282650501d9d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc111c22dc09474773ae6513b93b6a81eca5ee8e7ba1b13ec0908282650501d9d

namespace PerfectPower.SOEModelPackets
def obs044 := PerfectPower.CheckedSOE.Pc111c22dc09474773ae6513b93b6a81eca5ee8e7ba1b13ec0908282650501d9d.obs
def step044 := PerfectPower.CheckedSOE.Pc111c22dc09474773ae6513b93b6a81eca5ee8e7ba1b13ec0908282650501d9d.step
def q044 := PerfectPower.CheckedSOE.Pc111c22dc09474773ae6513b93b6a81eca5ee8e7ba1b13ec0908282650501d9d.q
def out044 := PerfectPower.CheckedSOE.Pc111c22dc09474773ae6513b93b6a81eca5ee8e7ba1b13ec0908282650501d9d.out
def target044 := PerfectPower.CheckedSOE.Pc111c22dc09474773ae6513b93b6a81eca5ee8e7ba1b13ec0908282650501d9d.target
theorem complete044 (s t : Fin 2) : SOESemantics.Equivalent step044 obs044 s t ↔ q044 s = q044 t := PerfectPower.CheckedSOE.Pc111c22dc09474773ae6513b93b6a81eca5ee8e7ba1b13ec0908282650501d9d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P3652ae4ef7b5485aad82b9d60bc3d7543b9780dc58cb8c744720b1d5c5a70111
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3652ae4ef7b5485aad82b9d60bc3d7543b9780dc58cb8c744720b1d5c5a70111; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P3652ae4ef7b5485aad82b9d60bc3d7543b9780dc58cb8c744720b1d5c5a70111

namespace PerfectPower.SOEModelPackets
def obs045 := PerfectPower.CheckedSOE.P3652ae4ef7b5485aad82b9d60bc3d7543b9780dc58cb8c744720b1d5c5a70111.obs
def step045 := PerfectPower.CheckedSOE.P3652ae4ef7b5485aad82b9d60bc3d7543b9780dc58cb8c744720b1d5c5a70111.step
def q045 := PerfectPower.CheckedSOE.P3652ae4ef7b5485aad82b9d60bc3d7543b9780dc58cb8c744720b1d5c5a70111.q
def out045 := PerfectPower.CheckedSOE.P3652ae4ef7b5485aad82b9d60bc3d7543b9780dc58cb8c744720b1d5c5a70111.out
def target045 := PerfectPower.CheckedSOE.P3652ae4ef7b5485aad82b9d60bc3d7543b9780dc58cb8c744720b1d5c5a70111.target
theorem complete045 (s t : Fin 2) : SOESemantics.Equivalent step045 obs045 s t ↔ q045 s = q045 t := PerfectPower.CheckedSOE.P3652ae4ef7b5485aad82b9d60bc3d7543b9780dc58cb8c744720b1d5c5a70111.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd2dbdf30b3d66981d4fb5ee2b3510f9fecbecd0d7d979ec232299390e142c909
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d2dbdf30b3d66981d4fb5ee2b3510f9fecbecd0d7d979ec232299390e142c909; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd2dbdf30b3d66981d4fb5ee2b3510f9fecbecd0d7d979ec232299390e142c909

namespace PerfectPower.SOEModelPackets
def obs046 := PerfectPower.CheckedSOE.Pd2dbdf30b3d66981d4fb5ee2b3510f9fecbecd0d7d979ec232299390e142c909.obs
def step046 := PerfectPower.CheckedSOE.Pd2dbdf30b3d66981d4fb5ee2b3510f9fecbecd0d7d979ec232299390e142c909.step
def q046 := PerfectPower.CheckedSOE.Pd2dbdf30b3d66981d4fb5ee2b3510f9fecbecd0d7d979ec232299390e142c909.q
def out046 := PerfectPower.CheckedSOE.Pd2dbdf30b3d66981d4fb5ee2b3510f9fecbecd0d7d979ec232299390e142c909.out
def target046 := PerfectPower.CheckedSOE.Pd2dbdf30b3d66981d4fb5ee2b3510f9fecbecd0d7d979ec232299390e142c909.target
theorem complete046 (s t : Fin 2) : SOESemantics.Equivalent step046 obs046 s t ↔ q046 s = q046 t := PerfectPower.CheckedSOE.Pd2dbdf30b3d66981d4fb5ee2b3510f9fecbecd0d7d979ec232299390e142c909.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P721df57698749e39fcb549becdc2ee189e5dc509bc5fd0441020aad0d184f47b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 721df57698749e39fcb549becdc2ee189e5dc509bc5fd0441020aad0d184f47b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P721df57698749e39fcb549becdc2ee189e5dc509bc5fd0441020aad0d184f47b

namespace PerfectPower.SOEModelPackets
def obs047 := PerfectPower.CheckedSOE.P721df57698749e39fcb549becdc2ee189e5dc509bc5fd0441020aad0d184f47b.obs
def step047 := PerfectPower.CheckedSOE.P721df57698749e39fcb549becdc2ee189e5dc509bc5fd0441020aad0d184f47b.step
def q047 := PerfectPower.CheckedSOE.P721df57698749e39fcb549becdc2ee189e5dc509bc5fd0441020aad0d184f47b.q
def out047 := PerfectPower.CheckedSOE.P721df57698749e39fcb549becdc2ee189e5dc509bc5fd0441020aad0d184f47b.out
def target047 := PerfectPower.CheckedSOE.P721df57698749e39fcb549becdc2ee189e5dc509bc5fd0441020aad0d184f47b.target
theorem complete047 (s t : Fin 2) : SOESemantics.Equivalent step047 obs047 s t ↔ q047 s = q047 t := PerfectPower.CheckedSOE.P721df57698749e39fcb549becdc2ee189e5dc509bc5fd0441020aad0d184f47b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P7af47c544df597b0e4c8d8b71a2eb18dd169362459bbbfcf7583dbab31b35a0c
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 7af47c544df597b0e4c8d8b71a2eb18dd169362459bbbfcf7583dbab31b35a0c; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P7af47c544df597b0e4c8d8b71a2eb18dd169362459bbbfcf7583dbab31b35a0c

namespace PerfectPower.SOEModelPackets
def obs048 := PerfectPower.CheckedSOE.P7af47c544df597b0e4c8d8b71a2eb18dd169362459bbbfcf7583dbab31b35a0c.obs
def step048 := PerfectPower.CheckedSOE.P7af47c544df597b0e4c8d8b71a2eb18dd169362459bbbfcf7583dbab31b35a0c.step
def q048 := PerfectPower.CheckedSOE.P7af47c544df597b0e4c8d8b71a2eb18dd169362459bbbfcf7583dbab31b35a0c.q
def out048 := PerfectPower.CheckedSOE.P7af47c544df597b0e4c8d8b71a2eb18dd169362459bbbfcf7583dbab31b35a0c.out
def target048 := PerfectPower.CheckedSOE.P7af47c544df597b0e4c8d8b71a2eb18dd169362459bbbfcf7583dbab31b35a0c.target
theorem complete048 (s t : Fin 2) : SOESemantics.Equivalent step048 obs048 s t ↔ q048 s = q048 t := PerfectPower.CheckedSOE.P7af47c544df597b0e4c8d8b71a2eb18dd169362459bbbfcf7583dbab31b35a0c.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P778041e18d62c83d2bb4862c61bf98706a6a76284c51fa80c4b76c02c9d585c3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 778041e18d62c83d2bb4862c61bf98706a6a76284c51fa80c4b76c02c9d585c3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P778041e18d62c83d2bb4862c61bf98706a6a76284c51fa80c4b76c02c9d585c3

namespace PerfectPower.SOEModelPackets
def obs049 := PerfectPower.CheckedSOE.P778041e18d62c83d2bb4862c61bf98706a6a76284c51fa80c4b76c02c9d585c3.obs
def step049 := PerfectPower.CheckedSOE.P778041e18d62c83d2bb4862c61bf98706a6a76284c51fa80c4b76c02c9d585c3.step
def q049 := PerfectPower.CheckedSOE.P778041e18d62c83d2bb4862c61bf98706a6a76284c51fa80c4b76c02c9d585c3.q
def out049 := PerfectPower.CheckedSOE.P778041e18d62c83d2bb4862c61bf98706a6a76284c51fa80c4b76c02c9d585c3.out
def target049 := PerfectPower.CheckedSOE.P778041e18d62c83d2bb4862c61bf98706a6a76284c51fa80c4b76c02c9d585c3.target
theorem complete049 (s t : Fin 2) : SOESemantics.Equivalent step049 obs049 s t ↔ q049 s = q049 t := PerfectPower.CheckedSOE.P778041e18d62c83d2bb4862c61bf98706a6a76284c51fa80c4b76c02c9d585c3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P47e0a60fa1344142a662ee8204907a18a8bcf86facbd263fb3023035e28431f2
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 47e0a60fa1344142a662ee8204907a18a8bcf86facbd263fb3023035e28431f2; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P47e0a60fa1344142a662ee8204907a18a8bcf86facbd263fb3023035e28431f2

namespace PerfectPower.SOEModelPackets
def obs050 := PerfectPower.CheckedSOE.P47e0a60fa1344142a662ee8204907a18a8bcf86facbd263fb3023035e28431f2.obs
def step050 := PerfectPower.CheckedSOE.P47e0a60fa1344142a662ee8204907a18a8bcf86facbd263fb3023035e28431f2.step
def q050 := PerfectPower.CheckedSOE.P47e0a60fa1344142a662ee8204907a18a8bcf86facbd263fb3023035e28431f2.q
def out050 := PerfectPower.CheckedSOE.P47e0a60fa1344142a662ee8204907a18a8bcf86facbd263fb3023035e28431f2.out
def target050 := PerfectPower.CheckedSOE.P47e0a60fa1344142a662ee8204907a18a8bcf86facbd263fb3023035e28431f2.target
theorem complete050 (s t : Fin 2) : SOESemantics.Equivalent step050 obs050 s t ↔ q050 s = q050 t := PerfectPower.CheckedSOE.P47e0a60fa1344142a662ee8204907a18a8bcf86facbd263fb3023035e28431f2.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbd0ad43b0d5a7bcb21dffe5df29e6640a8272134ab2246d763c793d0e3e4356a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: bd0ad43b0d5a7bcb21dffe5df29e6640a8272134ab2246d763c793d0e3e4356a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbd0ad43b0d5a7bcb21dffe5df29e6640a8272134ab2246d763c793d0e3e4356a

namespace PerfectPower.SOEModelPackets
def obs051 := PerfectPower.CheckedSOE.Pbd0ad43b0d5a7bcb21dffe5df29e6640a8272134ab2246d763c793d0e3e4356a.obs
def step051 := PerfectPower.CheckedSOE.Pbd0ad43b0d5a7bcb21dffe5df29e6640a8272134ab2246d763c793d0e3e4356a.step
def q051 := PerfectPower.CheckedSOE.Pbd0ad43b0d5a7bcb21dffe5df29e6640a8272134ab2246d763c793d0e3e4356a.q
def out051 := PerfectPower.CheckedSOE.Pbd0ad43b0d5a7bcb21dffe5df29e6640a8272134ab2246d763c793d0e3e4356a.out
def target051 := PerfectPower.CheckedSOE.Pbd0ad43b0d5a7bcb21dffe5df29e6640a8272134ab2246d763c793d0e3e4356a.target
theorem complete051 (s t : Fin 2) : SOESemantics.Equivalent step051 obs051 s t ↔ q051 s = q051 t := PerfectPower.CheckedSOE.Pbd0ad43b0d5a7bcb21dffe5df29e6640a8272134ab2246d763c793d0e3e4356a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4c2feb2c9e64337d09ae4e5feedf1daa25a233e78eaf1df8afe729e436b31ae3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4c2feb2c9e64337d09ae4e5feedf1daa25a233e78eaf1df8afe729e436b31ae3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4c2feb2c9e64337d09ae4e5feedf1daa25a233e78eaf1df8afe729e436b31ae3

namespace PerfectPower.SOEModelPackets
def obs052 := PerfectPower.CheckedSOE.P4c2feb2c9e64337d09ae4e5feedf1daa25a233e78eaf1df8afe729e436b31ae3.obs
def step052 := PerfectPower.CheckedSOE.P4c2feb2c9e64337d09ae4e5feedf1daa25a233e78eaf1df8afe729e436b31ae3.step
def q052 := PerfectPower.CheckedSOE.P4c2feb2c9e64337d09ae4e5feedf1daa25a233e78eaf1df8afe729e436b31ae3.q
def out052 := PerfectPower.CheckedSOE.P4c2feb2c9e64337d09ae4e5feedf1daa25a233e78eaf1df8afe729e436b31ae3.out
def target052 := PerfectPower.CheckedSOE.P4c2feb2c9e64337d09ae4e5feedf1daa25a233e78eaf1df8afe729e436b31ae3.target
theorem complete052 (s t : Fin 2) : SOESemantics.Equivalent step052 obs052 s t ↔ q052 s = q052 t := PerfectPower.CheckedSOE.P4c2feb2c9e64337d09ae4e5feedf1daa25a233e78eaf1df8afe729e436b31ae3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P616a7ef40e25efe47592560f521c48e30880ad958581b1205c0230ab1bce5530
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 616a7ef40e25efe47592560f521c48e30880ad958581b1205c0230ab1bce5530; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P616a7ef40e25efe47592560f521c48e30880ad958581b1205c0230ab1bce5530

namespace PerfectPower.SOEModelPackets
def obs053 := PerfectPower.CheckedSOE.P616a7ef40e25efe47592560f521c48e30880ad958581b1205c0230ab1bce5530.obs
def step053 := PerfectPower.CheckedSOE.P616a7ef40e25efe47592560f521c48e30880ad958581b1205c0230ab1bce5530.step
def q053 := PerfectPower.CheckedSOE.P616a7ef40e25efe47592560f521c48e30880ad958581b1205c0230ab1bce5530.q
def out053 := PerfectPower.CheckedSOE.P616a7ef40e25efe47592560f521c48e30880ad958581b1205c0230ab1bce5530.out
def target053 := PerfectPower.CheckedSOE.P616a7ef40e25efe47592560f521c48e30880ad958581b1205c0230ab1bce5530.target
theorem complete053 (s t : Fin 2) : SOESemantics.Equivalent step053 obs053 s t ↔ q053 s = q053 t := PerfectPower.CheckedSOE.P616a7ef40e25efe47592560f521c48e30880ad958581b1205c0230ab1bce5530.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6201ba53c3d0d30ecf1d08cb6ba619b56bb075fc5082243b81d429c9999ccb96
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6201ba53c3d0d30ecf1d08cb6ba619b56bb075fc5082243b81d429c9999ccb96; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6201ba53c3d0d30ecf1d08cb6ba619b56bb075fc5082243b81d429c9999ccb96

namespace PerfectPower.SOEModelPackets
def obs054 := PerfectPower.CheckedSOE.P6201ba53c3d0d30ecf1d08cb6ba619b56bb075fc5082243b81d429c9999ccb96.obs
def step054 := PerfectPower.CheckedSOE.P6201ba53c3d0d30ecf1d08cb6ba619b56bb075fc5082243b81d429c9999ccb96.step
def q054 := PerfectPower.CheckedSOE.P6201ba53c3d0d30ecf1d08cb6ba619b56bb075fc5082243b81d429c9999ccb96.q
def out054 := PerfectPower.CheckedSOE.P6201ba53c3d0d30ecf1d08cb6ba619b56bb075fc5082243b81d429c9999ccb96.out
def target054 := PerfectPower.CheckedSOE.P6201ba53c3d0d30ecf1d08cb6ba619b56bb075fc5082243b81d429c9999ccb96.target
theorem complete054 (s t : Fin 2) : SOESemantics.Equivalent step054 obs054 s t ↔ q054 s = q054 t := PerfectPower.CheckedSOE.P6201ba53c3d0d30ecf1d08cb6ba619b56bb075fc5082243b81d429c9999ccb96.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P7072eac4dd545fc72e6552ba7762f3d62ca0e1bc44464ee15c8329c3b0c5bee4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 7072eac4dd545fc72e6552ba7762f3d62ca0e1bc44464ee15c8329c3b0c5bee4; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P7072eac4dd545fc72e6552ba7762f3d62ca0e1bc44464ee15c8329c3b0c5bee4

namespace PerfectPower.SOEModelPackets
def obs055 := PerfectPower.CheckedSOE.P7072eac4dd545fc72e6552ba7762f3d62ca0e1bc44464ee15c8329c3b0c5bee4.obs
def step055 := PerfectPower.CheckedSOE.P7072eac4dd545fc72e6552ba7762f3d62ca0e1bc44464ee15c8329c3b0c5bee4.step
def q055 := PerfectPower.CheckedSOE.P7072eac4dd545fc72e6552ba7762f3d62ca0e1bc44464ee15c8329c3b0c5bee4.q
def out055 := PerfectPower.CheckedSOE.P7072eac4dd545fc72e6552ba7762f3d62ca0e1bc44464ee15c8329c3b0c5bee4.out
def target055 := PerfectPower.CheckedSOE.P7072eac4dd545fc72e6552ba7762f3d62ca0e1bc44464ee15c8329c3b0c5bee4.target
theorem complete055 (s t : Fin 2) : SOESemantics.Equivalent step055 obs055 s t ↔ q055 s = q055 t := PerfectPower.CheckedSOE.P7072eac4dd545fc72e6552ba7762f3d62ca0e1bc44464ee15c8329c3b0c5bee4.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe73748148dcf47754a5e13e9a6a6f73a4f0db94ce2a314bae23b37e1378d2560
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e73748148dcf47754a5e13e9a6a6f73a4f0db94ce2a314bae23b37e1378d2560; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe73748148dcf47754a5e13e9a6a6f73a4f0db94ce2a314bae23b37e1378d2560

namespace PerfectPower.SOEModelPackets
def obs056 := PerfectPower.CheckedSOE.Pe73748148dcf47754a5e13e9a6a6f73a4f0db94ce2a314bae23b37e1378d2560.obs
def step056 := PerfectPower.CheckedSOE.Pe73748148dcf47754a5e13e9a6a6f73a4f0db94ce2a314bae23b37e1378d2560.step
def q056 := PerfectPower.CheckedSOE.Pe73748148dcf47754a5e13e9a6a6f73a4f0db94ce2a314bae23b37e1378d2560.q
def out056 := PerfectPower.CheckedSOE.Pe73748148dcf47754a5e13e9a6a6f73a4f0db94ce2a314bae23b37e1378d2560.out
def target056 := PerfectPower.CheckedSOE.Pe73748148dcf47754a5e13e9a6a6f73a4f0db94ce2a314bae23b37e1378d2560.target
theorem complete056 (s t : Fin 2) : SOESemantics.Equivalent step056 obs056 s t ↔ q056 s = q056 t := PerfectPower.CheckedSOE.Pe73748148dcf47754a5e13e9a6a6f73a4f0db94ce2a314bae23b37e1378d2560.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P59f610c6a7ea1a9f97cc85c750b9f851a5da11487685f6a21b4f003368d60030
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 59f610c6a7ea1a9f97cc85c750b9f851a5da11487685f6a21b4f003368d60030; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P59f610c6a7ea1a9f97cc85c750b9f851a5da11487685f6a21b4f003368d60030

namespace PerfectPower.SOEModelPackets
def obs057 := PerfectPower.CheckedSOE.P59f610c6a7ea1a9f97cc85c750b9f851a5da11487685f6a21b4f003368d60030.obs
def step057 := PerfectPower.CheckedSOE.P59f610c6a7ea1a9f97cc85c750b9f851a5da11487685f6a21b4f003368d60030.step
def q057 := PerfectPower.CheckedSOE.P59f610c6a7ea1a9f97cc85c750b9f851a5da11487685f6a21b4f003368d60030.q
def out057 := PerfectPower.CheckedSOE.P59f610c6a7ea1a9f97cc85c750b9f851a5da11487685f6a21b4f003368d60030.out
def target057 := PerfectPower.CheckedSOE.P59f610c6a7ea1a9f97cc85c750b9f851a5da11487685f6a21b4f003368d60030.target
theorem complete057 (s t : Fin 2) : SOESemantics.Equivalent step057 obs057 s t ↔ q057 s = q057 t := PerfectPower.CheckedSOE.P59f610c6a7ea1a9f97cc85c750b9f851a5da11487685f6a21b4f003368d60030.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2d0b2d2703e23acde64764c0976299e2e125393c2e1c20abe5c4880b25d7a3a1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2d0b2d2703e23acde64764c0976299e2e125393c2e1c20abe5c4880b25d7a3a1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2d0b2d2703e23acde64764c0976299e2e125393c2e1c20abe5c4880b25d7a3a1

namespace PerfectPower.SOEModelPackets
def obs058 := PerfectPower.CheckedSOE.P2d0b2d2703e23acde64764c0976299e2e125393c2e1c20abe5c4880b25d7a3a1.obs
def step058 := PerfectPower.CheckedSOE.P2d0b2d2703e23acde64764c0976299e2e125393c2e1c20abe5c4880b25d7a3a1.step
def q058 := PerfectPower.CheckedSOE.P2d0b2d2703e23acde64764c0976299e2e125393c2e1c20abe5c4880b25d7a3a1.q
def out058 := PerfectPower.CheckedSOE.P2d0b2d2703e23acde64764c0976299e2e125393c2e1c20abe5c4880b25d7a3a1.out
def target058 := PerfectPower.CheckedSOE.P2d0b2d2703e23acde64764c0976299e2e125393c2e1c20abe5c4880b25d7a3a1.target
theorem complete058 (s t : Fin 2) : SOESemantics.Equivalent step058 obs058 s t ↔ q058 s = q058 t := PerfectPower.CheckedSOE.P2d0b2d2703e23acde64764c0976299e2e125393c2e1c20abe5c4880b25d7a3a1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf63ea1b7fadcf44efcf0cc9138e8cf1865488c3f431e92d74ff30de912c738cd
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f63ea1b7fadcf44efcf0cc9138e8cf1865488c3f431e92d74ff30de912c738cd; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf63ea1b7fadcf44efcf0cc9138e8cf1865488c3f431e92d74ff30de912c738cd

namespace PerfectPower.SOEModelPackets
def obs059 := PerfectPower.CheckedSOE.Pf63ea1b7fadcf44efcf0cc9138e8cf1865488c3f431e92d74ff30de912c738cd.obs
def step059 := PerfectPower.CheckedSOE.Pf63ea1b7fadcf44efcf0cc9138e8cf1865488c3f431e92d74ff30de912c738cd.step
def q059 := PerfectPower.CheckedSOE.Pf63ea1b7fadcf44efcf0cc9138e8cf1865488c3f431e92d74ff30de912c738cd.q
def out059 := PerfectPower.CheckedSOE.Pf63ea1b7fadcf44efcf0cc9138e8cf1865488c3f431e92d74ff30de912c738cd.out
def target059 := PerfectPower.CheckedSOE.Pf63ea1b7fadcf44efcf0cc9138e8cf1865488c3f431e92d74ff30de912c738cd.target
theorem complete059 (s t : Fin 2) : SOESemantics.Equivalent step059 obs059 s t ↔ q059 s = q059 t := PerfectPower.CheckedSOE.Pf63ea1b7fadcf44efcf0cc9138e8cf1865488c3f431e92d74ff30de912c738cd.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc92855434509450ec8a1c142199d89d4ef36e1e595800b6f97a097d3ec52e134
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c92855434509450ec8a1c142199d89d4ef36e1e595800b6f97a097d3ec52e134; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc92855434509450ec8a1c142199d89d4ef36e1e595800b6f97a097d3ec52e134

namespace PerfectPower.SOEModelPackets
def obs060 := PerfectPower.CheckedSOE.Pc92855434509450ec8a1c142199d89d4ef36e1e595800b6f97a097d3ec52e134.obs
def step060 := PerfectPower.CheckedSOE.Pc92855434509450ec8a1c142199d89d4ef36e1e595800b6f97a097d3ec52e134.step
def q060 := PerfectPower.CheckedSOE.Pc92855434509450ec8a1c142199d89d4ef36e1e595800b6f97a097d3ec52e134.q
def out060 := PerfectPower.CheckedSOE.Pc92855434509450ec8a1c142199d89d4ef36e1e595800b6f97a097d3ec52e134.out
def target060 := PerfectPower.CheckedSOE.Pc92855434509450ec8a1c142199d89d4ef36e1e595800b6f97a097d3ec52e134.target
theorem complete060 (s t : Fin 2) : SOESemantics.Equivalent step060 obs060 s t ↔ q060 s = q060 t := PerfectPower.CheckedSOE.Pc92855434509450ec8a1c142199d89d4ef36e1e595800b6f97a097d3ec52e134.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6bbffe8105293197fbe6ac10df02d5dc6ac824fa4cf27d7295af6f7d943410b3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6bbffe8105293197fbe6ac10df02d5dc6ac824fa4cf27d7295af6f7d943410b3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6bbffe8105293197fbe6ac10df02d5dc6ac824fa4cf27d7295af6f7d943410b3

namespace PerfectPower.SOEModelPackets
def obs061 := PerfectPower.CheckedSOE.P6bbffe8105293197fbe6ac10df02d5dc6ac824fa4cf27d7295af6f7d943410b3.obs
def step061 := PerfectPower.CheckedSOE.P6bbffe8105293197fbe6ac10df02d5dc6ac824fa4cf27d7295af6f7d943410b3.step
def q061 := PerfectPower.CheckedSOE.P6bbffe8105293197fbe6ac10df02d5dc6ac824fa4cf27d7295af6f7d943410b3.q
def out061 := PerfectPower.CheckedSOE.P6bbffe8105293197fbe6ac10df02d5dc6ac824fa4cf27d7295af6f7d943410b3.out
def target061 := PerfectPower.CheckedSOE.P6bbffe8105293197fbe6ac10df02d5dc6ac824fa4cf27d7295af6f7d943410b3.target
theorem complete061 (s t : Fin 2) : SOESemantics.Equivalent step061 obs061 s t ↔ q061 s = q061 t := PerfectPower.CheckedSOE.P6bbffe8105293197fbe6ac10df02d5dc6ac824fa4cf27d7295af6f7d943410b3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P90dca8d3623f4864f0d40162b6c637e7d714072febcf065c18bddc5c5e191663
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 90dca8d3623f4864f0d40162b6c637e7d714072febcf065c18bddc5c5e191663; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P90dca8d3623f4864f0d40162b6c637e7d714072febcf065c18bddc5c5e191663

namespace PerfectPower.SOEModelPackets
def obs062 := PerfectPower.CheckedSOE.P90dca8d3623f4864f0d40162b6c637e7d714072febcf065c18bddc5c5e191663.obs
def step062 := PerfectPower.CheckedSOE.P90dca8d3623f4864f0d40162b6c637e7d714072febcf065c18bddc5c5e191663.step
def q062 := PerfectPower.CheckedSOE.P90dca8d3623f4864f0d40162b6c637e7d714072febcf065c18bddc5c5e191663.q
def out062 := PerfectPower.CheckedSOE.P90dca8d3623f4864f0d40162b6c637e7d714072febcf065c18bddc5c5e191663.out
def target062 := PerfectPower.CheckedSOE.P90dca8d3623f4864f0d40162b6c637e7d714072febcf065c18bddc5c5e191663.target
theorem complete062 (s t : Fin 2) : SOESemantics.Equivalent step062 obs062 s t ↔ q062 s = q062 t := PerfectPower.CheckedSOE.P90dca8d3623f4864f0d40162b6c637e7d714072febcf065c18bddc5c5e191663.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2c9920f4880a1847c1a23d9b56a6af7dd791f873af88bbaff818b880ab959764
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2c9920f4880a1847c1a23d9b56a6af7dd791f873af88bbaff818b880ab959764; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2c9920f4880a1847c1a23d9b56a6af7dd791f873af88bbaff818b880ab959764

namespace PerfectPower.SOEModelPackets
def obs063 := PerfectPower.CheckedSOE.P2c9920f4880a1847c1a23d9b56a6af7dd791f873af88bbaff818b880ab959764.obs
def step063 := PerfectPower.CheckedSOE.P2c9920f4880a1847c1a23d9b56a6af7dd791f873af88bbaff818b880ab959764.step
def q063 := PerfectPower.CheckedSOE.P2c9920f4880a1847c1a23d9b56a6af7dd791f873af88bbaff818b880ab959764.q
def out063 := PerfectPower.CheckedSOE.P2c9920f4880a1847c1a23d9b56a6af7dd791f873af88bbaff818b880ab959764.out
def target063 := PerfectPower.CheckedSOE.P2c9920f4880a1847c1a23d9b56a6af7dd791f873af88bbaff818b880ab959764.target
theorem complete063 (s t : Fin 2) : SOESemantics.Equivalent step063 obs063 s t ↔ q063 s = q063 t := PerfectPower.CheckedSOE.P2c9920f4880a1847c1a23d9b56a6af7dd791f873af88bbaff818b880ab959764.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P3b2d089884f604d9692e09525da17b43f5fd1254c4b7e508b018f818a1e82ed8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3b2d089884f604d9692e09525da17b43f5fd1254c4b7e508b018f818a1e82ed8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P3b2d089884f604d9692e09525da17b43f5fd1254c4b7e508b018f818a1e82ed8

namespace PerfectPower.SOEModelPackets
def obs064 := PerfectPower.CheckedSOE.P3b2d089884f604d9692e09525da17b43f5fd1254c4b7e508b018f818a1e82ed8.obs
def step064 := PerfectPower.CheckedSOE.P3b2d089884f604d9692e09525da17b43f5fd1254c4b7e508b018f818a1e82ed8.step
def q064 := PerfectPower.CheckedSOE.P3b2d089884f604d9692e09525da17b43f5fd1254c4b7e508b018f818a1e82ed8.q
def out064 := PerfectPower.CheckedSOE.P3b2d089884f604d9692e09525da17b43f5fd1254c4b7e508b018f818a1e82ed8.out
def target064 := PerfectPower.CheckedSOE.P3b2d089884f604d9692e09525da17b43f5fd1254c4b7e508b018f818a1e82ed8.target
theorem complete064 (s t : Fin 2) : SOESemantics.Equivalent step064 obs064 s t ↔ q064 s = q064 t := PerfectPower.CheckedSOE.P3b2d089884f604d9692e09525da17b43f5fd1254c4b7e508b018f818a1e82ed8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc3f3937862f79ca7e728252b7dc81864e54331ffe16f704c235088491e14b702
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c3f3937862f79ca7e728252b7dc81864e54331ffe16f704c235088491e14b702; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc3f3937862f79ca7e728252b7dc81864e54331ffe16f704c235088491e14b702

namespace PerfectPower.SOEModelPackets
def obs065 := PerfectPower.CheckedSOE.Pc3f3937862f79ca7e728252b7dc81864e54331ffe16f704c235088491e14b702.obs
def step065 := PerfectPower.CheckedSOE.Pc3f3937862f79ca7e728252b7dc81864e54331ffe16f704c235088491e14b702.step
def q065 := PerfectPower.CheckedSOE.Pc3f3937862f79ca7e728252b7dc81864e54331ffe16f704c235088491e14b702.q
def out065 := PerfectPower.CheckedSOE.Pc3f3937862f79ca7e728252b7dc81864e54331ffe16f704c235088491e14b702.out
def target065 := PerfectPower.CheckedSOE.Pc3f3937862f79ca7e728252b7dc81864e54331ffe16f704c235088491e14b702.target
theorem complete065 (s t : Fin 2) : SOESemantics.Equivalent step065 obs065 s t ↔ q065 s = q065 t := PerfectPower.CheckedSOE.Pc3f3937862f79ca7e728252b7dc81864e54331ffe16f704c235088491e14b702.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd9b54cce5d51362f2ee390308211764df4ab46bcace8619ff0636f1b55d8289a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d9b54cce5d51362f2ee390308211764df4ab46bcace8619ff0636f1b55d8289a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd9b54cce5d51362f2ee390308211764df4ab46bcace8619ff0636f1b55d8289a

namespace PerfectPower.SOEModelPackets
def obs066 := PerfectPower.CheckedSOE.Pd9b54cce5d51362f2ee390308211764df4ab46bcace8619ff0636f1b55d8289a.obs
def step066 := PerfectPower.CheckedSOE.Pd9b54cce5d51362f2ee390308211764df4ab46bcace8619ff0636f1b55d8289a.step
def q066 := PerfectPower.CheckedSOE.Pd9b54cce5d51362f2ee390308211764df4ab46bcace8619ff0636f1b55d8289a.q
def out066 := PerfectPower.CheckedSOE.Pd9b54cce5d51362f2ee390308211764df4ab46bcace8619ff0636f1b55d8289a.out
def target066 := PerfectPower.CheckedSOE.Pd9b54cce5d51362f2ee390308211764df4ab46bcace8619ff0636f1b55d8289a.target
theorem complete066 (s t : Fin 2) : SOESemantics.Equivalent step066 obs066 s t ↔ q066 s = q066 t := PerfectPower.CheckedSOE.Pd9b54cce5d51362f2ee390308211764df4ab46bcace8619ff0636f1b55d8289a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P7d3aa6b7e24216c165edd43b7dba2c84f9ff4cd28fc1f3769b8ccc6f04de1eb8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 7d3aa6b7e24216c165edd43b7dba2c84f9ff4cd28fc1f3769b8ccc6f04de1eb8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P7d3aa6b7e24216c165edd43b7dba2c84f9ff4cd28fc1f3769b8ccc6f04de1eb8

namespace PerfectPower.SOEModelPackets
def obs067 := PerfectPower.CheckedSOE.P7d3aa6b7e24216c165edd43b7dba2c84f9ff4cd28fc1f3769b8ccc6f04de1eb8.obs
def step067 := PerfectPower.CheckedSOE.P7d3aa6b7e24216c165edd43b7dba2c84f9ff4cd28fc1f3769b8ccc6f04de1eb8.step
def q067 := PerfectPower.CheckedSOE.P7d3aa6b7e24216c165edd43b7dba2c84f9ff4cd28fc1f3769b8ccc6f04de1eb8.q
def out067 := PerfectPower.CheckedSOE.P7d3aa6b7e24216c165edd43b7dba2c84f9ff4cd28fc1f3769b8ccc6f04de1eb8.out
def target067 := PerfectPower.CheckedSOE.P7d3aa6b7e24216c165edd43b7dba2c84f9ff4cd28fc1f3769b8ccc6f04de1eb8.target
theorem complete067 (s t : Fin 2) : SOESemantics.Equivalent step067 obs067 s t ↔ q067 s = q067 t := PerfectPower.CheckedSOE.P7d3aa6b7e24216c165edd43b7dba2c84f9ff4cd28fc1f3769b8ccc6f04de1eb8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pfcaa723ad179d89505ad0d7325d59cbb5bf7602b0ad027206184a55ee0514410
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: fcaa723ad179d89505ad0d7325d59cbb5bf7602b0ad027206184a55ee0514410; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pfcaa723ad179d89505ad0d7325d59cbb5bf7602b0ad027206184a55ee0514410

namespace PerfectPower.SOEModelPackets
def obs068 := PerfectPower.CheckedSOE.Pfcaa723ad179d89505ad0d7325d59cbb5bf7602b0ad027206184a55ee0514410.obs
def step068 := PerfectPower.CheckedSOE.Pfcaa723ad179d89505ad0d7325d59cbb5bf7602b0ad027206184a55ee0514410.step
def q068 := PerfectPower.CheckedSOE.Pfcaa723ad179d89505ad0d7325d59cbb5bf7602b0ad027206184a55ee0514410.q
def out068 := PerfectPower.CheckedSOE.Pfcaa723ad179d89505ad0d7325d59cbb5bf7602b0ad027206184a55ee0514410.out
def target068 := PerfectPower.CheckedSOE.Pfcaa723ad179d89505ad0d7325d59cbb5bf7602b0ad027206184a55ee0514410.target
theorem complete068 (s t : Fin 2) : SOESemantics.Equivalent step068 obs068 s t ↔ q068 s = q068 t := PerfectPower.CheckedSOE.Pfcaa723ad179d89505ad0d7325d59cbb5bf7602b0ad027206184a55ee0514410.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6f28d84fd74519756a40ab076a972dc8e9b81380b1f77b6d95871f6f7c64fa8d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6f28d84fd74519756a40ab076a972dc8e9b81380b1f77b6d95871f6f7c64fa8d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6f28d84fd74519756a40ab076a972dc8e9b81380b1f77b6d95871f6f7c64fa8d

namespace PerfectPower.SOEModelPackets
def obs069 := PerfectPower.CheckedSOE.P6f28d84fd74519756a40ab076a972dc8e9b81380b1f77b6d95871f6f7c64fa8d.obs
def step069 := PerfectPower.CheckedSOE.P6f28d84fd74519756a40ab076a972dc8e9b81380b1f77b6d95871f6f7c64fa8d.step
def q069 := PerfectPower.CheckedSOE.P6f28d84fd74519756a40ab076a972dc8e9b81380b1f77b6d95871f6f7c64fa8d.q
def out069 := PerfectPower.CheckedSOE.P6f28d84fd74519756a40ab076a972dc8e9b81380b1f77b6d95871f6f7c64fa8d.out
def target069 := PerfectPower.CheckedSOE.P6f28d84fd74519756a40ab076a972dc8e9b81380b1f77b6d95871f6f7c64fa8d.target
theorem complete069 (s t : Fin 2) : SOESemantics.Equivalent step069 obs069 s t ↔ q069 s = q069 t := PerfectPower.CheckedSOE.P6f28d84fd74519756a40ab076a972dc8e9b81380b1f77b6d95871f6f7c64fa8d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P3c8281734de9888d92c49079ce00cd4f0a4cd9d54213bd24db1aaec4796e25c9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3c8281734de9888d92c49079ce00cd4f0a4cd9d54213bd24db1aaec4796e25c9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P3c8281734de9888d92c49079ce00cd4f0a4cd9d54213bd24db1aaec4796e25c9

namespace PerfectPower.SOEModelPackets
def obs070 := PerfectPower.CheckedSOE.P3c8281734de9888d92c49079ce00cd4f0a4cd9d54213bd24db1aaec4796e25c9.obs
def step070 := PerfectPower.CheckedSOE.P3c8281734de9888d92c49079ce00cd4f0a4cd9d54213bd24db1aaec4796e25c9.step
def q070 := PerfectPower.CheckedSOE.P3c8281734de9888d92c49079ce00cd4f0a4cd9d54213bd24db1aaec4796e25c9.q
def out070 := PerfectPower.CheckedSOE.P3c8281734de9888d92c49079ce00cd4f0a4cd9d54213bd24db1aaec4796e25c9.out
def target070 := PerfectPower.CheckedSOE.P3c8281734de9888d92c49079ce00cd4f0a4cd9d54213bd24db1aaec4796e25c9.target
theorem complete070 (s t : Fin 2) : SOESemantics.Equivalent step070 obs070 s t ↔ q070 s = q070 t := PerfectPower.CheckedSOE.P3c8281734de9888d92c49079ce00cd4f0a4cd9d54213bd24db1aaec4796e25c9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb36d110271e57a8d288ce229cdd7fc05fed44ac4bdb6ec3e3453564433236c29
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b36d110271e57a8d288ce229cdd7fc05fed44ac4bdb6ec3e3453564433236c29; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb36d110271e57a8d288ce229cdd7fc05fed44ac4bdb6ec3e3453564433236c29

namespace PerfectPower.SOEModelPackets
def obs071 := PerfectPower.CheckedSOE.Pb36d110271e57a8d288ce229cdd7fc05fed44ac4bdb6ec3e3453564433236c29.obs
def step071 := PerfectPower.CheckedSOE.Pb36d110271e57a8d288ce229cdd7fc05fed44ac4bdb6ec3e3453564433236c29.step
def q071 := PerfectPower.CheckedSOE.Pb36d110271e57a8d288ce229cdd7fc05fed44ac4bdb6ec3e3453564433236c29.q
def out071 := PerfectPower.CheckedSOE.Pb36d110271e57a8d288ce229cdd7fc05fed44ac4bdb6ec3e3453564433236c29.out
def target071 := PerfectPower.CheckedSOE.Pb36d110271e57a8d288ce229cdd7fc05fed44ac4bdb6ec3e3453564433236c29.target
theorem complete071 (s t : Fin 2) : SOESemantics.Equivalent step071 obs071 s t ↔ q071 s = q071 t := PerfectPower.CheckedSOE.Pb36d110271e57a8d288ce229cdd7fc05fed44ac4bdb6ec3e3453564433236c29.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf5d2d8bd32a3150911102fd2cdb62c9fc953475c836068643a6040463d91e34e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f5d2d8bd32a3150911102fd2cdb62c9fc953475c836068643a6040463d91e34e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf5d2d8bd32a3150911102fd2cdb62c9fc953475c836068643a6040463d91e34e

namespace PerfectPower.SOEModelPackets
def obs072 := PerfectPower.CheckedSOE.Pf5d2d8bd32a3150911102fd2cdb62c9fc953475c836068643a6040463d91e34e.obs
def step072 := PerfectPower.CheckedSOE.Pf5d2d8bd32a3150911102fd2cdb62c9fc953475c836068643a6040463d91e34e.step
def q072 := PerfectPower.CheckedSOE.Pf5d2d8bd32a3150911102fd2cdb62c9fc953475c836068643a6040463d91e34e.q
def out072 := PerfectPower.CheckedSOE.Pf5d2d8bd32a3150911102fd2cdb62c9fc953475c836068643a6040463d91e34e.out
def target072 := PerfectPower.CheckedSOE.Pf5d2d8bd32a3150911102fd2cdb62c9fc953475c836068643a6040463d91e34e.target
theorem complete072 (s t : Fin 2) : SOESemantics.Equivalent step072 obs072 s t ↔ q072 s = q072 t := PerfectPower.CheckedSOE.Pf5d2d8bd32a3150911102fd2cdb62c9fc953475c836068643a6040463d91e34e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P77b210c22ea23280f330d56a02c2019ae95468ecb0436f428574b27ef9ec170f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 77b210c22ea23280f330d56a02c2019ae95468ecb0436f428574b27ef9ec170f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P77b210c22ea23280f330d56a02c2019ae95468ecb0436f428574b27ef9ec170f

namespace PerfectPower.SOEModelPackets
def obs073 := PerfectPower.CheckedSOE.P77b210c22ea23280f330d56a02c2019ae95468ecb0436f428574b27ef9ec170f.obs
def step073 := PerfectPower.CheckedSOE.P77b210c22ea23280f330d56a02c2019ae95468ecb0436f428574b27ef9ec170f.step
def q073 := PerfectPower.CheckedSOE.P77b210c22ea23280f330d56a02c2019ae95468ecb0436f428574b27ef9ec170f.q
def out073 := PerfectPower.CheckedSOE.P77b210c22ea23280f330d56a02c2019ae95468ecb0436f428574b27ef9ec170f.out
def target073 := PerfectPower.CheckedSOE.P77b210c22ea23280f330d56a02c2019ae95468ecb0436f428574b27ef9ec170f.target
theorem complete073 (s t : Fin 2) : SOESemantics.Equivalent step073 obs073 s t ↔ q073 s = q073 t := PerfectPower.CheckedSOE.P77b210c22ea23280f330d56a02c2019ae95468ecb0436f428574b27ef9ec170f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P56b6c2084339adf0cd2c52b201677d88302c2a42c09fcc7847f5d6adf316dfa8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 56b6c2084339adf0cd2c52b201677d88302c2a42c09fcc7847f5d6adf316dfa8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P56b6c2084339adf0cd2c52b201677d88302c2a42c09fcc7847f5d6adf316dfa8

namespace PerfectPower.SOEModelPackets
def obs074 := PerfectPower.CheckedSOE.P56b6c2084339adf0cd2c52b201677d88302c2a42c09fcc7847f5d6adf316dfa8.obs
def step074 := PerfectPower.CheckedSOE.P56b6c2084339adf0cd2c52b201677d88302c2a42c09fcc7847f5d6adf316dfa8.step
def q074 := PerfectPower.CheckedSOE.P56b6c2084339adf0cd2c52b201677d88302c2a42c09fcc7847f5d6adf316dfa8.q
def out074 := PerfectPower.CheckedSOE.P56b6c2084339adf0cd2c52b201677d88302c2a42c09fcc7847f5d6adf316dfa8.out
def target074 := PerfectPower.CheckedSOE.P56b6c2084339adf0cd2c52b201677d88302c2a42c09fcc7847f5d6adf316dfa8.target
theorem complete074 (s t : Fin 2) : SOESemantics.Equivalent step074 obs074 s t ↔ q074 s = q074 t := PerfectPower.CheckedSOE.P56b6c2084339adf0cd2c52b201677d88302c2a42c09fcc7847f5d6adf316dfa8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P13fc33cefd99ef6a9f117d6e88bd63d36a9028cad97d667d7720b79da2dc28a3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 13fc33cefd99ef6a9f117d6e88bd63d36a9028cad97d667d7720b79da2dc28a3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P13fc33cefd99ef6a9f117d6e88bd63d36a9028cad97d667d7720b79da2dc28a3

namespace PerfectPower.SOEModelPackets
def obs075 := PerfectPower.CheckedSOE.P13fc33cefd99ef6a9f117d6e88bd63d36a9028cad97d667d7720b79da2dc28a3.obs
def step075 := PerfectPower.CheckedSOE.P13fc33cefd99ef6a9f117d6e88bd63d36a9028cad97d667d7720b79da2dc28a3.step
def q075 := PerfectPower.CheckedSOE.P13fc33cefd99ef6a9f117d6e88bd63d36a9028cad97d667d7720b79da2dc28a3.q
def out075 := PerfectPower.CheckedSOE.P13fc33cefd99ef6a9f117d6e88bd63d36a9028cad97d667d7720b79da2dc28a3.out
def target075 := PerfectPower.CheckedSOE.P13fc33cefd99ef6a9f117d6e88bd63d36a9028cad97d667d7720b79da2dc28a3.target
theorem complete075 (s t : Fin 2) : SOESemantics.Equivalent step075 obs075 s t ↔ q075 s = q075 t := PerfectPower.CheckedSOE.P13fc33cefd99ef6a9f117d6e88bd63d36a9028cad97d667d7720b79da2dc28a3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pcb919db96acd491afd0d724b561a645e882eccd01c0de0e2da5ec8d21065b19b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: cb919db96acd491afd0d724b561a645e882eccd01c0de0e2da5ec8d21065b19b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pcb919db96acd491afd0d724b561a645e882eccd01c0de0e2da5ec8d21065b19b

namespace PerfectPower.SOEModelPackets
def obs076 := PerfectPower.CheckedSOE.Pcb919db96acd491afd0d724b561a645e882eccd01c0de0e2da5ec8d21065b19b.obs
def step076 := PerfectPower.CheckedSOE.Pcb919db96acd491afd0d724b561a645e882eccd01c0de0e2da5ec8d21065b19b.step
def q076 := PerfectPower.CheckedSOE.Pcb919db96acd491afd0d724b561a645e882eccd01c0de0e2da5ec8d21065b19b.q
def out076 := PerfectPower.CheckedSOE.Pcb919db96acd491afd0d724b561a645e882eccd01c0de0e2da5ec8d21065b19b.out
def target076 := PerfectPower.CheckedSOE.Pcb919db96acd491afd0d724b561a645e882eccd01c0de0e2da5ec8d21065b19b.target
theorem complete076 (s t : Fin 2) : SOESemantics.Equivalent step076 obs076 s t ↔ q076 s = q076 t := PerfectPower.CheckedSOE.Pcb919db96acd491afd0d724b561a645e882eccd01c0de0e2da5ec8d21065b19b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P11ebadeffe295e1d7e7c0e45fb447818d9e0f6ed91e89e75886a116e3ad159fc
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 11ebadeffe295e1d7e7c0e45fb447818d9e0f6ed91e89e75886a116e3ad159fc; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P11ebadeffe295e1d7e7c0e45fb447818d9e0f6ed91e89e75886a116e3ad159fc

namespace PerfectPower.SOEModelPackets
def obs077 := PerfectPower.CheckedSOE.P11ebadeffe295e1d7e7c0e45fb447818d9e0f6ed91e89e75886a116e3ad159fc.obs
def step077 := PerfectPower.CheckedSOE.P11ebadeffe295e1d7e7c0e45fb447818d9e0f6ed91e89e75886a116e3ad159fc.step
def q077 := PerfectPower.CheckedSOE.P11ebadeffe295e1d7e7c0e45fb447818d9e0f6ed91e89e75886a116e3ad159fc.q
def out077 := PerfectPower.CheckedSOE.P11ebadeffe295e1d7e7c0e45fb447818d9e0f6ed91e89e75886a116e3ad159fc.out
def target077 := PerfectPower.CheckedSOE.P11ebadeffe295e1d7e7c0e45fb447818d9e0f6ed91e89e75886a116e3ad159fc.target
theorem complete077 (s t : Fin 2) : SOESemantics.Equivalent step077 obs077 s t ↔ q077 s = q077 t := PerfectPower.CheckedSOE.P11ebadeffe295e1d7e7c0e45fb447818d9e0f6ed91e89e75886a116e3ad159fc.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P616b43eb8e35e47fae741810f6f280b00de98b2f2bb5025a955d0f9c7b687743
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 616b43eb8e35e47fae741810f6f280b00de98b2f2bb5025a955d0f9c7b687743; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P616b43eb8e35e47fae741810f6f280b00de98b2f2bb5025a955d0f9c7b687743

namespace PerfectPower.SOEModelPackets
def obs078 := PerfectPower.CheckedSOE.P616b43eb8e35e47fae741810f6f280b00de98b2f2bb5025a955d0f9c7b687743.obs
def step078 := PerfectPower.CheckedSOE.P616b43eb8e35e47fae741810f6f280b00de98b2f2bb5025a955d0f9c7b687743.step
def q078 := PerfectPower.CheckedSOE.P616b43eb8e35e47fae741810f6f280b00de98b2f2bb5025a955d0f9c7b687743.q
def out078 := PerfectPower.CheckedSOE.P616b43eb8e35e47fae741810f6f280b00de98b2f2bb5025a955d0f9c7b687743.out
def target078 := PerfectPower.CheckedSOE.P616b43eb8e35e47fae741810f6f280b00de98b2f2bb5025a955d0f9c7b687743.target
theorem complete078 (s t : Fin 2) : SOESemantics.Equivalent step078 obs078 s t ↔ q078 s = q078 t := PerfectPower.CheckedSOE.P616b43eb8e35e47fae741810f6f280b00de98b2f2bb5025a955d0f9c7b687743.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc585a42053af93016d700e904a36dbd67d94cefb986c9bdebeb19aa1a8f1e5b9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c585a42053af93016d700e904a36dbd67d94cefb986c9bdebeb19aa1a8f1e5b9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc585a42053af93016d700e904a36dbd67d94cefb986c9bdebeb19aa1a8f1e5b9

namespace PerfectPower.SOEModelPackets
def obs079 := PerfectPower.CheckedSOE.Pc585a42053af93016d700e904a36dbd67d94cefb986c9bdebeb19aa1a8f1e5b9.obs
def step079 := PerfectPower.CheckedSOE.Pc585a42053af93016d700e904a36dbd67d94cefb986c9bdebeb19aa1a8f1e5b9.step
def q079 := PerfectPower.CheckedSOE.Pc585a42053af93016d700e904a36dbd67d94cefb986c9bdebeb19aa1a8f1e5b9.q
def out079 := PerfectPower.CheckedSOE.Pc585a42053af93016d700e904a36dbd67d94cefb986c9bdebeb19aa1a8f1e5b9.out
def target079 := PerfectPower.CheckedSOE.Pc585a42053af93016d700e904a36dbd67d94cefb986c9bdebeb19aa1a8f1e5b9.target
theorem complete079 (s t : Fin 2) : SOESemantics.Equivalent step079 obs079 s t ↔ q079 s = q079 t := PerfectPower.CheckedSOE.Pc585a42053af93016d700e904a36dbd67d94cefb986c9bdebeb19aa1a8f1e5b9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pafc5e8f6a7aff778f09fd8cebf3dfa6f4a9edd5f2b81aeb9eaeb5abf156cd4ca
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: afc5e8f6a7aff778f09fd8cebf3dfa6f4a9edd5f2b81aeb9eaeb5abf156cd4ca; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pafc5e8f6a7aff778f09fd8cebf3dfa6f4a9edd5f2b81aeb9eaeb5abf156cd4ca

namespace PerfectPower.SOEModelPackets
def obs080 := PerfectPower.CheckedSOE.Pafc5e8f6a7aff778f09fd8cebf3dfa6f4a9edd5f2b81aeb9eaeb5abf156cd4ca.obs
def step080 := PerfectPower.CheckedSOE.Pafc5e8f6a7aff778f09fd8cebf3dfa6f4a9edd5f2b81aeb9eaeb5abf156cd4ca.step
def q080 := PerfectPower.CheckedSOE.Pafc5e8f6a7aff778f09fd8cebf3dfa6f4a9edd5f2b81aeb9eaeb5abf156cd4ca.q
def out080 := PerfectPower.CheckedSOE.Pafc5e8f6a7aff778f09fd8cebf3dfa6f4a9edd5f2b81aeb9eaeb5abf156cd4ca.out
def target080 := PerfectPower.CheckedSOE.Pafc5e8f6a7aff778f09fd8cebf3dfa6f4a9edd5f2b81aeb9eaeb5abf156cd4ca.target
theorem complete080 (s t : Fin 2) : SOESemantics.Equivalent step080 obs080 s t ↔ q080 s = q080 t := PerfectPower.CheckedSOE.Pafc5e8f6a7aff778f09fd8cebf3dfa6f4a9edd5f2b81aeb9eaeb5abf156cd4ca.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P3965b95e26986c1c034433c10e5d52cf582b52b365978fde5d1e841caa5fc11a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3965b95e26986c1c034433c10e5d52cf582b52b365978fde5d1e841caa5fc11a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P3965b95e26986c1c034433c10e5d52cf582b52b365978fde5d1e841caa5fc11a

namespace PerfectPower.SOEModelPackets
def obs081 := PerfectPower.CheckedSOE.P3965b95e26986c1c034433c10e5d52cf582b52b365978fde5d1e841caa5fc11a.obs
def step081 := PerfectPower.CheckedSOE.P3965b95e26986c1c034433c10e5d52cf582b52b365978fde5d1e841caa5fc11a.step
def q081 := PerfectPower.CheckedSOE.P3965b95e26986c1c034433c10e5d52cf582b52b365978fde5d1e841caa5fc11a.q
def out081 := PerfectPower.CheckedSOE.P3965b95e26986c1c034433c10e5d52cf582b52b365978fde5d1e841caa5fc11a.out
def target081 := PerfectPower.CheckedSOE.P3965b95e26986c1c034433c10e5d52cf582b52b365978fde5d1e841caa5fc11a.target
theorem complete081 (s t : Fin 2) : SOESemantics.Equivalent step081 obs081 s t ↔ q081 s = q081 t := PerfectPower.CheckedSOE.P3965b95e26986c1c034433c10e5d52cf582b52b365978fde5d1e841caa5fc11a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P844ef83387f00a3a49e2e77e311d28d8468f5474eba68da12dfcf0c422072dd9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 844ef83387f00a3a49e2e77e311d28d8468f5474eba68da12dfcf0c422072dd9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P844ef83387f00a3a49e2e77e311d28d8468f5474eba68da12dfcf0c422072dd9

namespace PerfectPower.SOEModelPackets
def obs082 := PerfectPower.CheckedSOE.P844ef83387f00a3a49e2e77e311d28d8468f5474eba68da12dfcf0c422072dd9.obs
def step082 := PerfectPower.CheckedSOE.P844ef83387f00a3a49e2e77e311d28d8468f5474eba68da12dfcf0c422072dd9.step
def q082 := PerfectPower.CheckedSOE.P844ef83387f00a3a49e2e77e311d28d8468f5474eba68da12dfcf0c422072dd9.q
def out082 := PerfectPower.CheckedSOE.P844ef83387f00a3a49e2e77e311d28d8468f5474eba68da12dfcf0c422072dd9.out
def target082 := PerfectPower.CheckedSOE.P844ef83387f00a3a49e2e77e311d28d8468f5474eba68da12dfcf0c422072dd9.target
theorem complete082 (s t : Fin 2) : SOESemantics.Equivalent step082 obs082 s t ↔ q082 s = q082 t := PerfectPower.CheckedSOE.P844ef83387f00a3a49e2e77e311d28d8468f5474eba68da12dfcf0c422072dd9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pebffcb2edd3c786bb54712598ce4cd030739f40663092d4125ce5bd76d593016
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ebffcb2edd3c786bb54712598ce4cd030739f40663092d4125ce5bd76d593016; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pebffcb2edd3c786bb54712598ce4cd030739f40663092d4125ce5bd76d593016

namespace PerfectPower.SOEModelPackets
def obs083 := PerfectPower.CheckedSOE.Pebffcb2edd3c786bb54712598ce4cd030739f40663092d4125ce5bd76d593016.obs
def step083 := PerfectPower.CheckedSOE.Pebffcb2edd3c786bb54712598ce4cd030739f40663092d4125ce5bd76d593016.step
def q083 := PerfectPower.CheckedSOE.Pebffcb2edd3c786bb54712598ce4cd030739f40663092d4125ce5bd76d593016.q
def out083 := PerfectPower.CheckedSOE.Pebffcb2edd3c786bb54712598ce4cd030739f40663092d4125ce5bd76d593016.out
def target083 := PerfectPower.CheckedSOE.Pebffcb2edd3c786bb54712598ce4cd030739f40663092d4125ce5bd76d593016.target
theorem complete083 (s t : Fin 2) : SOESemantics.Equivalent step083 obs083 s t ↔ q083 s = q083 t := PerfectPower.CheckedSOE.Pebffcb2edd3c786bb54712598ce4cd030739f40663092d4125ce5bd76d593016.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd4e9ffcc761db28698b92e631b7d851ced84669011f421923917b53e2040439f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d4e9ffcc761db28698b92e631b7d851ced84669011f421923917b53e2040439f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd4e9ffcc761db28698b92e631b7d851ced84669011f421923917b53e2040439f

namespace PerfectPower.SOEModelPackets
def obs084 := PerfectPower.CheckedSOE.Pd4e9ffcc761db28698b92e631b7d851ced84669011f421923917b53e2040439f.obs
def step084 := PerfectPower.CheckedSOE.Pd4e9ffcc761db28698b92e631b7d851ced84669011f421923917b53e2040439f.step
def q084 := PerfectPower.CheckedSOE.Pd4e9ffcc761db28698b92e631b7d851ced84669011f421923917b53e2040439f.q
def out084 := PerfectPower.CheckedSOE.Pd4e9ffcc761db28698b92e631b7d851ced84669011f421923917b53e2040439f.out
def target084 := PerfectPower.CheckedSOE.Pd4e9ffcc761db28698b92e631b7d851ced84669011f421923917b53e2040439f.target
theorem complete084 (s t : Fin 2) : SOESemantics.Equivalent step084 obs084 s t ↔ q084 s = q084 t := PerfectPower.CheckedSOE.Pd4e9ffcc761db28698b92e631b7d851ced84669011f421923917b53e2040439f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P40371e6105079964b1ac3a45322b3663de422d579c4d300bebbb6caa2fbec08d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 40371e6105079964b1ac3a45322b3663de422d579c4d300bebbb6caa2fbec08d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P40371e6105079964b1ac3a45322b3663de422d579c4d300bebbb6caa2fbec08d

namespace PerfectPower.SOEModelPackets
def obs085 := PerfectPower.CheckedSOE.P40371e6105079964b1ac3a45322b3663de422d579c4d300bebbb6caa2fbec08d.obs
def step085 := PerfectPower.CheckedSOE.P40371e6105079964b1ac3a45322b3663de422d579c4d300bebbb6caa2fbec08d.step
def q085 := PerfectPower.CheckedSOE.P40371e6105079964b1ac3a45322b3663de422d579c4d300bebbb6caa2fbec08d.q
def out085 := PerfectPower.CheckedSOE.P40371e6105079964b1ac3a45322b3663de422d579c4d300bebbb6caa2fbec08d.out
def target085 := PerfectPower.CheckedSOE.P40371e6105079964b1ac3a45322b3663de422d579c4d300bebbb6caa2fbec08d.target
theorem complete085 (s t : Fin 2) : SOESemantics.Equivalent step085 obs085 s t ↔ q085 s = q085 t := PerfectPower.CheckedSOE.P40371e6105079964b1ac3a45322b3663de422d579c4d300bebbb6caa2fbec08d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe2bddda51b52714f23b2df8554dccf4dc65718aee99e3de3cf25140ef9763f3a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e2bddda51b52714f23b2df8554dccf4dc65718aee99e3de3cf25140ef9763f3a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe2bddda51b52714f23b2df8554dccf4dc65718aee99e3de3cf25140ef9763f3a

namespace PerfectPower.SOEModelPackets
def obs086 := PerfectPower.CheckedSOE.Pe2bddda51b52714f23b2df8554dccf4dc65718aee99e3de3cf25140ef9763f3a.obs
def step086 := PerfectPower.CheckedSOE.Pe2bddda51b52714f23b2df8554dccf4dc65718aee99e3de3cf25140ef9763f3a.step
def q086 := PerfectPower.CheckedSOE.Pe2bddda51b52714f23b2df8554dccf4dc65718aee99e3de3cf25140ef9763f3a.q
def out086 := PerfectPower.CheckedSOE.Pe2bddda51b52714f23b2df8554dccf4dc65718aee99e3de3cf25140ef9763f3a.out
def target086 := PerfectPower.CheckedSOE.Pe2bddda51b52714f23b2df8554dccf4dc65718aee99e3de3cf25140ef9763f3a.target
theorem complete086 (s t : Fin 2) : SOESemantics.Equivalent step086 obs086 s t ↔ q086 s = q086 t := PerfectPower.CheckedSOE.Pe2bddda51b52714f23b2df8554dccf4dc65718aee99e3de3cf25140ef9763f3a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P9d022ff357ec3be7ed9b7a885c367e8e5fd01a52b33fed9174690a59e4f75aa2
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 9d022ff357ec3be7ed9b7a885c367e8e5fd01a52b33fed9174690a59e4f75aa2; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P9d022ff357ec3be7ed9b7a885c367e8e5fd01a52b33fed9174690a59e4f75aa2

namespace PerfectPower.SOEModelPackets
def obs087 := PerfectPower.CheckedSOE.P9d022ff357ec3be7ed9b7a885c367e8e5fd01a52b33fed9174690a59e4f75aa2.obs
def step087 := PerfectPower.CheckedSOE.P9d022ff357ec3be7ed9b7a885c367e8e5fd01a52b33fed9174690a59e4f75aa2.step
def q087 := PerfectPower.CheckedSOE.P9d022ff357ec3be7ed9b7a885c367e8e5fd01a52b33fed9174690a59e4f75aa2.q
def out087 := PerfectPower.CheckedSOE.P9d022ff357ec3be7ed9b7a885c367e8e5fd01a52b33fed9174690a59e4f75aa2.out
def target087 := PerfectPower.CheckedSOE.P9d022ff357ec3be7ed9b7a885c367e8e5fd01a52b33fed9174690a59e4f75aa2.target
theorem complete087 (s t : Fin 2) : SOESemantics.Equivalent step087 obs087 s t ↔ q087 s = q087 t := PerfectPower.CheckedSOE.P9d022ff357ec3be7ed9b7a885c367e8e5fd01a52b33fed9174690a59e4f75aa2.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pfe2fc89879be65d274c60762e753ec4c376f1337d8e36c1bdbb3bb615562c538
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: fe2fc89879be65d274c60762e753ec4c376f1337d8e36c1bdbb3bb615562c538; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pfe2fc89879be65d274c60762e753ec4c376f1337d8e36c1bdbb3bb615562c538

namespace PerfectPower.SOEModelPackets
def obs088 := PerfectPower.CheckedSOE.Pfe2fc89879be65d274c60762e753ec4c376f1337d8e36c1bdbb3bb615562c538.obs
def step088 := PerfectPower.CheckedSOE.Pfe2fc89879be65d274c60762e753ec4c376f1337d8e36c1bdbb3bb615562c538.step
def q088 := PerfectPower.CheckedSOE.Pfe2fc89879be65d274c60762e753ec4c376f1337d8e36c1bdbb3bb615562c538.q
def out088 := PerfectPower.CheckedSOE.Pfe2fc89879be65d274c60762e753ec4c376f1337d8e36c1bdbb3bb615562c538.out
def target088 := PerfectPower.CheckedSOE.Pfe2fc89879be65d274c60762e753ec4c376f1337d8e36c1bdbb3bb615562c538.target
theorem complete088 (s t : Fin 2) : SOESemantics.Equivalent step088 obs088 s t ↔ q088 s = q088 t := PerfectPower.CheckedSOE.Pfe2fc89879be65d274c60762e753ec4c376f1337d8e36c1bdbb3bb615562c538.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P46fc4328d35196d119e01911ba88fc9c362e3a1adfae054358acff0b3427b3c9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 46fc4328d35196d119e01911ba88fc9c362e3a1adfae054358acff0b3427b3c9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P46fc4328d35196d119e01911ba88fc9c362e3a1adfae054358acff0b3427b3c9

namespace PerfectPower.SOEModelPackets
def obs089 := PerfectPower.CheckedSOE.P46fc4328d35196d119e01911ba88fc9c362e3a1adfae054358acff0b3427b3c9.obs
def step089 := PerfectPower.CheckedSOE.P46fc4328d35196d119e01911ba88fc9c362e3a1adfae054358acff0b3427b3c9.step
def q089 := PerfectPower.CheckedSOE.P46fc4328d35196d119e01911ba88fc9c362e3a1adfae054358acff0b3427b3c9.q
def out089 := PerfectPower.CheckedSOE.P46fc4328d35196d119e01911ba88fc9c362e3a1adfae054358acff0b3427b3c9.out
def target089 := PerfectPower.CheckedSOE.P46fc4328d35196d119e01911ba88fc9c362e3a1adfae054358acff0b3427b3c9.target
theorem complete089 (s t : Fin 2) : SOESemantics.Equivalent step089 obs089 s t ↔ q089 s = q089 t := PerfectPower.CheckedSOE.P46fc4328d35196d119e01911ba88fc9c362e3a1adfae054358acff0b3427b3c9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Paabaeb6008a9954aa1be74adb57a322da81fd049e375a99788e1a7f85b3b8255
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: aabaeb6008a9954aa1be74adb57a322da81fd049e375a99788e1a7f85b3b8255; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Paabaeb6008a9954aa1be74adb57a322da81fd049e375a99788e1a7f85b3b8255

namespace PerfectPower.SOEModelPackets
def obs090 := PerfectPower.CheckedSOE.Paabaeb6008a9954aa1be74adb57a322da81fd049e375a99788e1a7f85b3b8255.obs
def step090 := PerfectPower.CheckedSOE.Paabaeb6008a9954aa1be74adb57a322da81fd049e375a99788e1a7f85b3b8255.step
def q090 := PerfectPower.CheckedSOE.Paabaeb6008a9954aa1be74adb57a322da81fd049e375a99788e1a7f85b3b8255.q
def out090 := PerfectPower.CheckedSOE.Paabaeb6008a9954aa1be74adb57a322da81fd049e375a99788e1a7f85b3b8255.out
def target090 := PerfectPower.CheckedSOE.Paabaeb6008a9954aa1be74adb57a322da81fd049e375a99788e1a7f85b3b8255.target
theorem complete090 (s t : Fin 2) : SOESemantics.Equivalent step090 obs090 s t ↔ q090 s = q090 t := PerfectPower.CheckedSOE.Paabaeb6008a9954aa1be74adb57a322da81fd049e375a99788e1a7f85b3b8255.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P90e83d180ce8bc83e0063b0078fedcf28abfda1a6b5285ad6d5e64d6ebcdbcb1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 90e83d180ce8bc83e0063b0078fedcf28abfda1a6b5285ad6d5e64d6ebcdbcb1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P90e83d180ce8bc83e0063b0078fedcf28abfda1a6b5285ad6d5e64d6ebcdbcb1

namespace PerfectPower.SOEModelPackets
def obs091 := PerfectPower.CheckedSOE.P90e83d180ce8bc83e0063b0078fedcf28abfda1a6b5285ad6d5e64d6ebcdbcb1.obs
def step091 := PerfectPower.CheckedSOE.P90e83d180ce8bc83e0063b0078fedcf28abfda1a6b5285ad6d5e64d6ebcdbcb1.step
def q091 := PerfectPower.CheckedSOE.P90e83d180ce8bc83e0063b0078fedcf28abfda1a6b5285ad6d5e64d6ebcdbcb1.q
def out091 := PerfectPower.CheckedSOE.P90e83d180ce8bc83e0063b0078fedcf28abfda1a6b5285ad6d5e64d6ebcdbcb1.out
def target091 := PerfectPower.CheckedSOE.P90e83d180ce8bc83e0063b0078fedcf28abfda1a6b5285ad6d5e64d6ebcdbcb1.target
theorem complete091 (s t : Fin 2) : SOESemantics.Equivalent step091 obs091 s t ↔ q091 s = q091 t := PerfectPower.CheckedSOE.P90e83d180ce8bc83e0063b0078fedcf28abfda1a6b5285ad6d5e64d6ebcdbcb1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P41cec1b664e797d2da80193d6a6c773b8da8ebe0be4d68f630d45509c1ffd398
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 41cec1b664e797d2da80193d6a6c773b8da8ebe0be4d68f630d45509c1ffd398; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P41cec1b664e797d2da80193d6a6c773b8da8ebe0be4d68f630d45509c1ffd398

namespace PerfectPower.SOEModelPackets
def obs092 := PerfectPower.CheckedSOE.P41cec1b664e797d2da80193d6a6c773b8da8ebe0be4d68f630d45509c1ffd398.obs
def step092 := PerfectPower.CheckedSOE.P41cec1b664e797d2da80193d6a6c773b8da8ebe0be4d68f630d45509c1ffd398.step
def q092 := PerfectPower.CheckedSOE.P41cec1b664e797d2da80193d6a6c773b8da8ebe0be4d68f630d45509c1ffd398.q
def out092 := PerfectPower.CheckedSOE.P41cec1b664e797d2da80193d6a6c773b8da8ebe0be4d68f630d45509c1ffd398.out
def target092 := PerfectPower.CheckedSOE.P41cec1b664e797d2da80193d6a6c773b8da8ebe0be4d68f630d45509c1ffd398.target
theorem complete092 (s t : Fin 2) : SOESemantics.Equivalent step092 obs092 s t ↔ q092 s = q092 t := PerfectPower.CheckedSOE.P41cec1b664e797d2da80193d6a6c773b8da8ebe0be4d68f630d45509c1ffd398.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P48ae227260ae0669f508380fdfb26acd4fcf557b7a4b7f48f07cffc87af15bf3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 48ae227260ae0669f508380fdfb26acd4fcf557b7a4b7f48f07cffc87af15bf3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P48ae227260ae0669f508380fdfb26acd4fcf557b7a4b7f48f07cffc87af15bf3

namespace PerfectPower.SOEModelPackets
def obs093 := PerfectPower.CheckedSOE.P48ae227260ae0669f508380fdfb26acd4fcf557b7a4b7f48f07cffc87af15bf3.obs
def step093 := PerfectPower.CheckedSOE.P48ae227260ae0669f508380fdfb26acd4fcf557b7a4b7f48f07cffc87af15bf3.step
def q093 := PerfectPower.CheckedSOE.P48ae227260ae0669f508380fdfb26acd4fcf557b7a4b7f48f07cffc87af15bf3.q
def out093 := PerfectPower.CheckedSOE.P48ae227260ae0669f508380fdfb26acd4fcf557b7a4b7f48f07cffc87af15bf3.out
def target093 := PerfectPower.CheckedSOE.P48ae227260ae0669f508380fdfb26acd4fcf557b7a4b7f48f07cffc87af15bf3.target
theorem complete093 (s t : Fin 2) : SOESemantics.Equivalent step093 obs093 s t ↔ q093 s = q093 t := PerfectPower.CheckedSOE.P48ae227260ae0669f508380fdfb26acd4fcf557b7a4b7f48f07cffc87af15bf3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0d1e61084b83d5c4342451cbfdb1d19b21954b2a02e349328e8e1ead561090f3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0d1e61084b83d5c4342451cbfdb1d19b21954b2a02e349328e8e1ead561090f3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0d1e61084b83d5c4342451cbfdb1d19b21954b2a02e349328e8e1ead561090f3

namespace PerfectPower.SOEModelPackets
def obs094 := PerfectPower.CheckedSOE.P0d1e61084b83d5c4342451cbfdb1d19b21954b2a02e349328e8e1ead561090f3.obs
def step094 := PerfectPower.CheckedSOE.P0d1e61084b83d5c4342451cbfdb1d19b21954b2a02e349328e8e1ead561090f3.step
def q094 := PerfectPower.CheckedSOE.P0d1e61084b83d5c4342451cbfdb1d19b21954b2a02e349328e8e1ead561090f3.q
def out094 := PerfectPower.CheckedSOE.P0d1e61084b83d5c4342451cbfdb1d19b21954b2a02e349328e8e1ead561090f3.out
def target094 := PerfectPower.CheckedSOE.P0d1e61084b83d5c4342451cbfdb1d19b21954b2a02e349328e8e1ead561090f3.target
theorem complete094 (s t : Fin 2) : SOESemantics.Equivalent step094 obs094 s t ↔ q094 s = q094 t := PerfectPower.CheckedSOE.P0d1e61084b83d5c4342451cbfdb1d19b21954b2a02e349328e8e1ead561090f3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P91ba188d33862936ced72d28626c6987d4542ccf1c7f3a0e83f185cdb8e17e51
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 91ba188d33862936ced72d28626c6987d4542ccf1c7f3a0e83f185cdb8e17e51; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P91ba188d33862936ced72d28626c6987d4542ccf1c7f3a0e83f185cdb8e17e51

namespace PerfectPower.SOEModelPackets
def obs095 := PerfectPower.CheckedSOE.P91ba188d33862936ced72d28626c6987d4542ccf1c7f3a0e83f185cdb8e17e51.obs
def step095 := PerfectPower.CheckedSOE.P91ba188d33862936ced72d28626c6987d4542ccf1c7f3a0e83f185cdb8e17e51.step
def q095 := PerfectPower.CheckedSOE.P91ba188d33862936ced72d28626c6987d4542ccf1c7f3a0e83f185cdb8e17e51.q
def out095 := PerfectPower.CheckedSOE.P91ba188d33862936ced72d28626c6987d4542ccf1c7f3a0e83f185cdb8e17e51.out
def target095 := PerfectPower.CheckedSOE.P91ba188d33862936ced72d28626c6987d4542ccf1c7f3a0e83f185cdb8e17e51.target
theorem complete095 (s t : Fin 2) : SOESemantics.Equivalent step095 obs095 s t ↔ q095 s = q095 t := PerfectPower.CheckedSOE.P91ba188d33862936ced72d28626c6987d4542ccf1c7f3a0e83f185cdb8e17e51.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P00097a06d3f5bc01d70eaed05f3ece7936ecf0bd699ba5d68f000a539a587137
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 00097a06d3f5bc01d70eaed05f3ece7936ecf0bd699ba5d68f000a539a587137; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P00097a06d3f5bc01d70eaed05f3ece7936ecf0bd699ba5d68f000a539a587137

namespace PerfectPower.SOEModelPackets
def obs096 := PerfectPower.CheckedSOE.P00097a06d3f5bc01d70eaed05f3ece7936ecf0bd699ba5d68f000a539a587137.obs
def step096 := PerfectPower.CheckedSOE.P00097a06d3f5bc01d70eaed05f3ece7936ecf0bd699ba5d68f000a539a587137.step
def q096 := PerfectPower.CheckedSOE.P00097a06d3f5bc01d70eaed05f3ece7936ecf0bd699ba5d68f000a539a587137.q
def out096 := PerfectPower.CheckedSOE.P00097a06d3f5bc01d70eaed05f3ece7936ecf0bd699ba5d68f000a539a587137.out
def target096 := PerfectPower.CheckedSOE.P00097a06d3f5bc01d70eaed05f3ece7936ecf0bd699ba5d68f000a539a587137.target
theorem complete096 (s t : Fin 2) : SOESemantics.Equivalent step096 obs096 s t ↔ q096 s = q096 t := PerfectPower.CheckedSOE.P00097a06d3f5bc01d70eaed05f3ece7936ecf0bd699ba5d68f000a539a587137.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6cebd7eee0cdde359dec30d50fde9d66a5a9bb202c6b1d1b6627c5026cc64712
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6cebd7eee0cdde359dec30d50fde9d66a5a9bb202c6b1d1b6627c5026cc64712; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6cebd7eee0cdde359dec30d50fde9d66a5a9bb202c6b1d1b6627c5026cc64712

namespace PerfectPower.SOEModelPackets
def obs097 := PerfectPower.CheckedSOE.P6cebd7eee0cdde359dec30d50fde9d66a5a9bb202c6b1d1b6627c5026cc64712.obs
def step097 := PerfectPower.CheckedSOE.P6cebd7eee0cdde359dec30d50fde9d66a5a9bb202c6b1d1b6627c5026cc64712.step
def q097 := PerfectPower.CheckedSOE.P6cebd7eee0cdde359dec30d50fde9d66a5a9bb202c6b1d1b6627c5026cc64712.q
def out097 := PerfectPower.CheckedSOE.P6cebd7eee0cdde359dec30d50fde9d66a5a9bb202c6b1d1b6627c5026cc64712.out
def target097 := PerfectPower.CheckedSOE.P6cebd7eee0cdde359dec30d50fde9d66a5a9bb202c6b1d1b6627c5026cc64712.target
theorem complete097 (s t : Fin 2) : SOESemantics.Equivalent step097 obs097 s t ↔ q097 s = q097 t := PerfectPower.CheckedSOE.P6cebd7eee0cdde359dec30d50fde9d66a5a9bb202c6b1d1b6627c5026cc64712.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P1a4dc323568771a61937823b3d6023b6ec3f2aadfabe9aff0c29397ef5b12fbe
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 1a4dc323568771a61937823b3d6023b6ec3f2aadfabe9aff0c29397ef5b12fbe; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P1a4dc323568771a61937823b3d6023b6ec3f2aadfabe9aff0c29397ef5b12fbe

namespace PerfectPower.SOEModelPackets
def obs098 := PerfectPower.CheckedSOE.P1a4dc323568771a61937823b3d6023b6ec3f2aadfabe9aff0c29397ef5b12fbe.obs
def step098 := PerfectPower.CheckedSOE.P1a4dc323568771a61937823b3d6023b6ec3f2aadfabe9aff0c29397ef5b12fbe.step
def q098 := PerfectPower.CheckedSOE.P1a4dc323568771a61937823b3d6023b6ec3f2aadfabe9aff0c29397ef5b12fbe.q
def out098 := PerfectPower.CheckedSOE.P1a4dc323568771a61937823b3d6023b6ec3f2aadfabe9aff0c29397ef5b12fbe.out
def target098 := PerfectPower.CheckedSOE.P1a4dc323568771a61937823b3d6023b6ec3f2aadfabe9aff0c29397ef5b12fbe.target
theorem complete098 (s t : Fin 2) : SOESemantics.Equivalent step098 obs098 s t ↔ q098 s = q098 t := PerfectPower.CheckedSOE.P1a4dc323568771a61937823b3d6023b6ec3f2aadfabe9aff0c29397ef5b12fbe.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb6cc652ccef760984e64134fd449a312da3e6762e7b27cb7c956ba62b5c38848
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b6cc652ccef760984e64134fd449a312da3e6762e7b27cb7c956ba62b5c38848; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb6cc652ccef760984e64134fd449a312da3e6762e7b27cb7c956ba62b5c38848

namespace PerfectPower.SOEModelPackets
def obs099 := PerfectPower.CheckedSOE.Pb6cc652ccef760984e64134fd449a312da3e6762e7b27cb7c956ba62b5c38848.obs
def step099 := PerfectPower.CheckedSOE.Pb6cc652ccef760984e64134fd449a312da3e6762e7b27cb7c956ba62b5c38848.step
def q099 := PerfectPower.CheckedSOE.Pb6cc652ccef760984e64134fd449a312da3e6762e7b27cb7c956ba62b5c38848.q
def out099 := PerfectPower.CheckedSOE.Pb6cc652ccef760984e64134fd449a312da3e6762e7b27cb7c956ba62b5c38848.out
def target099 := PerfectPower.CheckedSOE.Pb6cc652ccef760984e64134fd449a312da3e6762e7b27cb7c956ba62b5c38848.target
theorem complete099 (s t : Fin 2) : SOESemantics.Equivalent step099 obs099 s t ↔ q099 s = q099 t := PerfectPower.CheckedSOE.Pb6cc652ccef760984e64134fd449a312da3e6762e7b27cb7c956ba62b5c38848.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P63a3ec2c7d225c63b0016153db01f4c6f3a6a16f447234f878935a171901ee6b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 63a3ec2c7d225c63b0016153db01f4c6f3a6a16f447234f878935a171901ee6b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P63a3ec2c7d225c63b0016153db01f4c6f3a6a16f447234f878935a171901ee6b

namespace PerfectPower.SOEModelPackets
def obs100 := PerfectPower.CheckedSOE.P63a3ec2c7d225c63b0016153db01f4c6f3a6a16f447234f878935a171901ee6b.obs
def step100 := PerfectPower.CheckedSOE.P63a3ec2c7d225c63b0016153db01f4c6f3a6a16f447234f878935a171901ee6b.step
def q100 := PerfectPower.CheckedSOE.P63a3ec2c7d225c63b0016153db01f4c6f3a6a16f447234f878935a171901ee6b.q
def out100 := PerfectPower.CheckedSOE.P63a3ec2c7d225c63b0016153db01f4c6f3a6a16f447234f878935a171901ee6b.out
def target100 := PerfectPower.CheckedSOE.P63a3ec2c7d225c63b0016153db01f4c6f3a6a16f447234f878935a171901ee6b.target
theorem complete100 (s t : Fin 2) : SOESemantics.Equivalent step100 obs100 s t ↔ q100 s = q100 t := PerfectPower.CheckedSOE.P63a3ec2c7d225c63b0016153db01f4c6f3a6a16f447234f878935a171901ee6b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P57f742bcf886c021e539317af7fdbe7d1a29903ef67f34de85d5332587df84e9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 57f742bcf886c021e539317af7fdbe7d1a29903ef67f34de85d5332587df84e9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P57f742bcf886c021e539317af7fdbe7d1a29903ef67f34de85d5332587df84e9

namespace PerfectPower.SOEModelPackets
def obs101 := PerfectPower.CheckedSOE.P57f742bcf886c021e539317af7fdbe7d1a29903ef67f34de85d5332587df84e9.obs
def step101 := PerfectPower.CheckedSOE.P57f742bcf886c021e539317af7fdbe7d1a29903ef67f34de85d5332587df84e9.step
def q101 := PerfectPower.CheckedSOE.P57f742bcf886c021e539317af7fdbe7d1a29903ef67f34de85d5332587df84e9.q
def out101 := PerfectPower.CheckedSOE.P57f742bcf886c021e539317af7fdbe7d1a29903ef67f34de85d5332587df84e9.out
def target101 := PerfectPower.CheckedSOE.P57f742bcf886c021e539317af7fdbe7d1a29903ef67f34de85d5332587df84e9.target
theorem complete101 (s t : Fin 2) : SOESemantics.Equivalent step101 obs101 s t ↔ q101 s = q101 t := PerfectPower.CheckedSOE.P57f742bcf886c021e539317af7fdbe7d1a29903ef67f34de85d5332587df84e9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb16decd73bb128d8c841cf787910ea6cf331b66ee9425fd70e893223b822f8ff
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b16decd73bb128d8c841cf787910ea6cf331b66ee9425fd70e893223b822f8ff; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb16decd73bb128d8c841cf787910ea6cf331b66ee9425fd70e893223b822f8ff

namespace PerfectPower.SOEModelPackets
def obs102 := PerfectPower.CheckedSOE.Pb16decd73bb128d8c841cf787910ea6cf331b66ee9425fd70e893223b822f8ff.obs
def step102 := PerfectPower.CheckedSOE.Pb16decd73bb128d8c841cf787910ea6cf331b66ee9425fd70e893223b822f8ff.step
def q102 := PerfectPower.CheckedSOE.Pb16decd73bb128d8c841cf787910ea6cf331b66ee9425fd70e893223b822f8ff.q
def out102 := PerfectPower.CheckedSOE.Pb16decd73bb128d8c841cf787910ea6cf331b66ee9425fd70e893223b822f8ff.out
def target102 := PerfectPower.CheckedSOE.Pb16decd73bb128d8c841cf787910ea6cf331b66ee9425fd70e893223b822f8ff.target
theorem complete102 (s t : Fin 2) : SOESemantics.Equivalent step102 obs102 s t ↔ q102 s = q102 t := PerfectPower.CheckedSOE.Pb16decd73bb128d8c841cf787910ea6cf331b66ee9425fd70e893223b822f8ff.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pdfc76ce9b58f2f026fc53f64ddcc991399f9f289eae31816cdc185ce14ee496e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: dfc76ce9b58f2f026fc53f64ddcc991399f9f289eae31816cdc185ce14ee496e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pdfc76ce9b58f2f026fc53f64ddcc991399f9f289eae31816cdc185ce14ee496e

namespace PerfectPower.SOEModelPackets
def obs103 := PerfectPower.CheckedSOE.Pdfc76ce9b58f2f026fc53f64ddcc991399f9f289eae31816cdc185ce14ee496e.obs
def step103 := PerfectPower.CheckedSOE.Pdfc76ce9b58f2f026fc53f64ddcc991399f9f289eae31816cdc185ce14ee496e.step
def q103 := PerfectPower.CheckedSOE.Pdfc76ce9b58f2f026fc53f64ddcc991399f9f289eae31816cdc185ce14ee496e.q
def out103 := PerfectPower.CheckedSOE.Pdfc76ce9b58f2f026fc53f64ddcc991399f9f289eae31816cdc185ce14ee496e.out
def target103 := PerfectPower.CheckedSOE.Pdfc76ce9b58f2f026fc53f64ddcc991399f9f289eae31816cdc185ce14ee496e.target
theorem complete103 (s t : Fin 2) : SOESemantics.Equivalent step103 obs103 s t ↔ q103 s = q103 t := PerfectPower.CheckedSOE.Pdfc76ce9b58f2f026fc53f64ddcc991399f9f289eae31816cdc185ce14ee496e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pdaaf5e6763a4a8a1b48749b45c39cc3fb197572a1fc92526fcaa4f427177b29f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: daaf5e6763a4a8a1b48749b45c39cc3fb197572a1fc92526fcaa4f427177b29f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pdaaf5e6763a4a8a1b48749b45c39cc3fb197572a1fc92526fcaa4f427177b29f

namespace PerfectPower.SOEModelPackets
def obs104 := PerfectPower.CheckedSOE.Pdaaf5e6763a4a8a1b48749b45c39cc3fb197572a1fc92526fcaa4f427177b29f.obs
def step104 := PerfectPower.CheckedSOE.Pdaaf5e6763a4a8a1b48749b45c39cc3fb197572a1fc92526fcaa4f427177b29f.step
def q104 := PerfectPower.CheckedSOE.Pdaaf5e6763a4a8a1b48749b45c39cc3fb197572a1fc92526fcaa4f427177b29f.q
def out104 := PerfectPower.CheckedSOE.Pdaaf5e6763a4a8a1b48749b45c39cc3fb197572a1fc92526fcaa4f427177b29f.out
def target104 := PerfectPower.CheckedSOE.Pdaaf5e6763a4a8a1b48749b45c39cc3fb197572a1fc92526fcaa4f427177b29f.target
theorem complete104 (s t : Fin 2) : SOESemantics.Equivalent step104 obs104 s t ↔ q104 s = q104 t := PerfectPower.CheckedSOE.Pdaaf5e6763a4a8a1b48749b45c39cc3fb197572a1fc92526fcaa4f427177b29f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P11cde437d204562ce766526cc6f6e07c47ca5623efcd90240b20cc5bb0f1f6b0
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 11cde437d204562ce766526cc6f6e07c47ca5623efcd90240b20cc5bb0f1f6b0; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P11cde437d204562ce766526cc6f6e07c47ca5623efcd90240b20cc5bb0f1f6b0

namespace PerfectPower.SOEModelPackets
def obs105 := PerfectPower.CheckedSOE.P11cde437d204562ce766526cc6f6e07c47ca5623efcd90240b20cc5bb0f1f6b0.obs
def step105 := PerfectPower.CheckedSOE.P11cde437d204562ce766526cc6f6e07c47ca5623efcd90240b20cc5bb0f1f6b0.step
def q105 := PerfectPower.CheckedSOE.P11cde437d204562ce766526cc6f6e07c47ca5623efcd90240b20cc5bb0f1f6b0.q
def out105 := PerfectPower.CheckedSOE.P11cde437d204562ce766526cc6f6e07c47ca5623efcd90240b20cc5bb0f1f6b0.out
def target105 := PerfectPower.CheckedSOE.P11cde437d204562ce766526cc6f6e07c47ca5623efcd90240b20cc5bb0f1f6b0.target
theorem complete105 (s t : Fin 2) : SOESemantics.Equivalent step105 obs105 s t ↔ q105 s = q105 t := PerfectPower.CheckedSOE.P11cde437d204562ce766526cc6f6e07c47ca5623efcd90240b20cc5bb0f1f6b0.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbe5e4da1e2b4a682e94e7ba8d7d0d254b10d0029c33717fd6094198971a50ee6
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: be5e4da1e2b4a682e94e7ba8d7d0d254b10d0029c33717fd6094198971a50ee6; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbe5e4da1e2b4a682e94e7ba8d7d0d254b10d0029c33717fd6094198971a50ee6

namespace PerfectPower.SOEModelPackets
def obs106 := PerfectPower.CheckedSOE.Pbe5e4da1e2b4a682e94e7ba8d7d0d254b10d0029c33717fd6094198971a50ee6.obs
def step106 := PerfectPower.CheckedSOE.Pbe5e4da1e2b4a682e94e7ba8d7d0d254b10d0029c33717fd6094198971a50ee6.step
def q106 := PerfectPower.CheckedSOE.Pbe5e4da1e2b4a682e94e7ba8d7d0d254b10d0029c33717fd6094198971a50ee6.q
def out106 := PerfectPower.CheckedSOE.Pbe5e4da1e2b4a682e94e7ba8d7d0d254b10d0029c33717fd6094198971a50ee6.out
def target106 := PerfectPower.CheckedSOE.Pbe5e4da1e2b4a682e94e7ba8d7d0d254b10d0029c33717fd6094198971a50ee6.target
theorem complete106 (s t : Fin 2) : SOESemantics.Equivalent step106 obs106 s t ↔ q106 s = q106 t := PerfectPower.CheckedSOE.Pbe5e4da1e2b4a682e94e7ba8d7d0d254b10d0029c33717fd6094198971a50ee6.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2412cc393b2c3aea03a2012e373d84c3656ac64fe74eaf61d95f08455317d549
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2412cc393b2c3aea03a2012e373d84c3656ac64fe74eaf61d95f08455317d549; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2412cc393b2c3aea03a2012e373d84c3656ac64fe74eaf61d95f08455317d549

namespace PerfectPower.SOEModelPackets
def obs107 := PerfectPower.CheckedSOE.P2412cc393b2c3aea03a2012e373d84c3656ac64fe74eaf61d95f08455317d549.obs
def step107 := PerfectPower.CheckedSOE.P2412cc393b2c3aea03a2012e373d84c3656ac64fe74eaf61d95f08455317d549.step
def q107 := PerfectPower.CheckedSOE.P2412cc393b2c3aea03a2012e373d84c3656ac64fe74eaf61d95f08455317d549.q
def out107 := PerfectPower.CheckedSOE.P2412cc393b2c3aea03a2012e373d84c3656ac64fe74eaf61d95f08455317d549.out
def target107 := PerfectPower.CheckedSOE.P2412cc393b2c3aea03a2012e373d84c3656ac64fe74eaf61d95f08455317d549.target
theorem complete107 (s t : Fin 2) : SOESemantics.Equivalent step107 obs107 s t ↔ q107 s = q107 t := PerfectPower.CheckedSOE.P2412cc393b2c3aea03a2012e373d84c3656ac64fe74eaf61d95f08455317d549.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P027708d40add346d7850882f8583f436c4a39fe9320c7824cbbc47a63a5210ad
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 027708d40add346d7850882f8583f436c4a39fe9320c7824cbbc47a63a5210ad; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P027708d40add346d7850882f8583f436c4a39fe9320c7824cbbc47a63a5210ad

namespace PerfectPower.SOEModelPackets
def obs108 := PerfectPower.CheckedSOE.P027708d40add346d7850882f8583f436c4a39fe9320c7824cbbc47a63a5210ad.obs
def step108 := PerfectPower.CheckedSOE.P027708d40add346d7850882f8583f436c4a39fe9320c7824cbbc47a63a5210ad.step
def q108 := PerfectPower.CheckedSOE.P027708d40add346d7850882f8583f436c4a39fe9320c7824cbbc47a63a5210ad.q
def out108 := PerfectPower.CheckedSOE.P027708d40add346d7850882f8583f436c4a39fe9320c7824cbbc47a63a5210ad.out
def target108 := PerfectPower.CheckedSOE.P027708d40add346d7850882f8583f436c4a39fe9320c7824cbbc47a63a5210ad.target
theorem complete108 (s t : Fin 2) : SOESemantics.Equivalent step108 obs108 s t ↔ q108 s = q108 t := PerfectPower.CheckedSOE.P027708d40add346d7850882f8583f436c4a39fe9320c7824cbbc47a63a5210ad.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P513369fee4a6fa144323229a7bfa89605b4bd5ed6191d7fb7499997b06f86c0e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 513369fee4a6fa144323229a7bfa89605b4bd5ed6191d7fb7499997b06f86c0e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P513369fee4a6fa144323229a7bfa89605b4bd5ed6191d7fb7499997b06f86c0e

namespace PerfectPower.SOEModelPackets
def obs109 := PerfectPower.CheckedSOE.P513369fee4a6fa144323229a7bfa89605b4bd5ed6191d7fb7499997b06f86c0e.obs
def step109 := PerfectPower.CheckedSOE.P513369fee4a6fa144323229a7bfa89605b4bd5ed6191d7fb7499997b06f86c0e.step
def q109 := PerfectPower.CheckedSOE.P513369fee4a6fa144323229a7bfa89605b4bd5ed6191d7fb7499997b06f86c0e.q
def out109 := PerfectPower.CheckedSOE.P513369fee4a6fa144323229a7bfa89605b4bd5ed6191d7fb7499997b06f86c0e.out
def target109 := PerfectPower.CheckedSOE.P513369fee4a6fa144323229a7bfa89605b4bd5ed6191d7fb7499997b06f86c0e.target
theorem complete109 (s t : Fin 2) : SOESemantics.Equivalent step109 obs109 s t ↔ q109 s = q109 t := PerfectPower.CheckedSOE.P513369fee4a6fa144323229a7bfa89605b4bd5ed6191d7fb7499997b06f86c0e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P29e9354364b34879df5e0cf5ee8a105d9806724b252e465f5302ffd30cabfa9a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 29e9354364b34879df5e0cf5ee8a105d9806724b252e465f5302ffd30cabfa9a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P29e9354364b34879df5e0cf5ee8a105d9806724b252e465f5302ffd30cabfa9a

namespace PerfectPower.SOEModelPackets
def obs110 := PerfectPower.CheckedSOE.P29e9354364b34879df5e0cf5ee8a105d9806724b252e465f5302ffd30cabfa9a.obs
def step110 := PerfectPower.CheckedSOE.P29e9354364b34879df5e0cf5ee8a105d9806724b252e465f5302ffd30cabfa9a.step
def q110 := PerfectPower.CheckedSOE.P29e9354364b34879df5e0cf5ee8a105d9806724b252e465f5302ffd30cabfa9a.q
def out110 := PerfectPower.CheckedSOE.P29e9354364b34879df5e0cf5ee8a105d9806724b252e465f5302ffd30cabfa9a.out
def target110 := PerfectPower.CheckedSOE.P29e9354364b34879df5e0cf5ee8a105d9806724b252e465f5302ffd30cabfa9a.target
theorem complete110 (s t : Fin 2) : SOESemantics.Equivalent step110 obs110 s t ↔ q110 s = q110 t := PerfectPower.CheckedSOE.P29e9354364b34879df5e0cf5ee8a105d9806724b252e465f5302ffd30cabfa9a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P93d4136a4623db4f33dcd1e2feb9ccdb0385c4e114fc14b3a01050d4b7569dd8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 93d4136a4623db4f33dcd1e2feb9ccdb0385c4e114fc14b3a01050d4b7569dd8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P93d4136a4623db4f33dcd1e2feb9ccdb0385c4e114fc14b3a01050d4b7569dd8

namespace PerfectPower.SOEModelPackets
def obs111 := PerfectPower.CheckedSOE.P93d4136a4623db4f33dcd1e2feb9ccdb0385c4e114fc14b3a01050d4b7569dd8.obs
def step111 := PerfectPower.CheckedSOE.P93d4136a4623db4f33dcd1e2feb9ccdb0385c4e114fc14b3a01050d4b7569dd8.step
def q111 := PerfectPower.CheckedSOE.P93d4136a4623db4f33dcd1e2feb9ccdb0385c4e114fc14b3a01050d4b7569dd8.q
def out111 := PerfectPower.CheckedSOE.P93d4136a4623db4f33dcd1e2feb9ccdb0385c4e114fc14b3a01050d4b7569dd8.out
def target111 := PerfectPower.CheckedSOE.P93d4136a4623db4f33dcd1e2feb9ccdb0385c4e114fc14b3a01050d4b7569dd8.target
theorem complete111 (s t : Fin 2) : SOESemantics.Equivalent step111 obs111 s t ↔ q111 s = q111 t := PerfectPower.CheckedSOE.P93d4136a4623db4f33dcd1e2feb9ccdb0385c4e114fc14b3a01050d4b7569dd8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa49efb1eb621b44432b4033828115a6c8568302689da4097786f76275a1c1de6
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a49efb1eb621b44432b4033828115a6c8568302689da4097786f76275a1c1de6; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa49efb1eb621b44432b4033828115a6c8568302689da4097786f76275a1c1de6

namespace PerfectPower.SOEModelPackets
def obs112 := PerfectPower.CheckedSOE.Pa49efb1eb621b44432b4033828115a6c8568302689da4097786f76275a1c1de6.obs
def step112 := PerfectPower.CheckedSOE.Pa49efb1eb621b44432b4033828115a6c8568302689da4097786f76275a1c1de6.step
def q112 := PerfectPower.CheckedSOE.Pa49efb1eb621b44432b4033828115a6c8568302689da4097786f76275a1c1de6.q
def out112 := PerfectPower.CheckedSOE.Pa49efb1eb621b44432b4033828115a6c8568302689da4097786f76275a1c1de6.out
def target112 := PerfectPower.CheckedSOE.Pa49efb1eb621b44432b4033828115a6c8568302689da4097786f76275a1c1de6.target
theorem complete112 (s t : Fin 2) : SOESemantics.Equivalent step112 obs112 s t ↔ q112 s = q112 t := PerfectPower.CheckedSOE.Pa49efb1eb621b44432b4033828115a6c8568302689da4097786f76275a1c1de6.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P9f7e951004a960d92ca931074900cbc1659401fbac05d49de9a0f1445ed11c4d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 9f7e951004a960d92ca931074900cbc1659401fbac05d49de9a0f1445ed11c4d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P9f7e951004a960d92ca931074900cbc1659401fbac05d49de9a0f1445ed11c4d

namespace PerfectPower.SOEModelPackets
def obs113 := PerfectPower.CheckedSOE.P9f7e951004a960d92ca931074900cbc1659401fbac05d49de9a0f1445ed11c4d.obs
def step113 := PerfectPower.CheckedSOE.P9f7e951004a960d92ca931074900cbc1659401fbac05d49de9a0f1445ed11c4d.step
def q113 := PerfectPower.CheckedSOE.P9f7e951004a960d92ca931074900cbc1659401fbac05d49de9a0f1445ed11c4d.q
def out113 := PerfectPower.CheckedSOE.P9f7e951004a960d92ca931074900cbc1659401fbac05d49de9a0f1445ed11c4d.out
def target113 := PerfectPower.CheckedSOE.P9f7e951004a960d92ca931074900cbc1659401fbac05d49de9a0f1445ed11c4d.target
theorem complete113 (s t : Fin 2) : SOESemantics.Equivalent step113 obs113 s t ↔ q113 s = q113 t := PerfectPower.CheckedSOE.P9f7e951004a960d92ca931074900cbc1659401fbac05d49de9a0f1445ed11c4d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbd5c903072af98108116993800370a2977668f5993410cd103f28f412ed16a79
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: bd5c903072af98108116993800370a2977668f5993410cd103f28f412ed16a79; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbd5c903072af98108116993800370a2977668f5993410cd103f28f412ed16a79

namespace PerfectPower.SOEModelPackets
def obs114 := PerfectPower.CheckedSOE.Pbd5c903072af98108116993800370a2977668f5993410cd103f28f412ed16a79.obs
def step114 := PerfectPower.CheckedSOE.Pbd5c903072af98108116993800370a2977668f5993410cd103f28f412ed16a79.step
def q114 := PerfectPower.CheckedSOE.Pbd5c903072af98108116993800370a2977668f5993410cd103f28f412ed16a79.q
def out114 := PerfectPower.CheckedSOE.Pbd5c903072af98108116993800370a2977668f5993410cd103f28f412ed16a79.out
def target114 := PerfectPower.CheckedSOE.Pbd5c903072af98108116993800370a2977668f5993410cd103f28f412ed16a79.target
theorem complete114 (s t : Fin 2) : SOESemantics.Equivalent step114 obs114 s t ↔ q114 s = q114 t := PerfectPower.CheckedSOE.Pbd5c903072af98108116993800370a2977668f5993410cd103f28f412ed16a79.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P5a2d59977935f04e5e64f80ce9beb330f3edd71ab0dac64656269cf5609a2b69
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 5a2d59977935f04e5e64f80ce9beb330f3edd71ab0dac64656269cf5609a2b69; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P5a2d59977935f04e5e64f80ce9beb330f3edd71ab0dac64656269cf5609a2b69

namespace PerfectPower.SOEModelPackets
def obs115 := PerfectPower.CheckedSOE.P5a2d59977935f04e5e64f80ce9beb330f3edd71ab0dac64656269cf5609a2b69.obs
def step115 := PerfectPower.CheckedSOE.P5a2d59977935f04e5e64f80ce9beb330f3edd71ab0dac64656269cf5609a2b69.step
def q115 := PerfectPower.CheckedSOE.P5a2d59977935f04e5e64f80ce9beb330f3edd71ab0dac64656269cf5609a2b69.q
def out115 := PerfectPower.CheckedSOE.P5a2d59977935f04e5e64f80ce9beb330f3edd71ab0dac64656269cf5609a2b69.out
def target115 := PerfectPower.CheckedSOE.P5a2d59977935f04e5e64f80ce9beb330f3edd71ab0dac64656269cf5609a2b69.target
theorem complete115 (s t : Fin 2) : SOESemantics.Equivalent step115 obs115 s t ↔ q115 s = q115 t := PerfectPower.CheckedSOE.P5a2d59977935f04e5e64f80ce9beb330f3edd71ab0dac64656269cf5609a2b69.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P78fcc38a640611ee6013349c5dc3a56132202360ebd53acfc765f242a10d2123
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 78fcc38a640611ee6013349c5dc3a56132202360ebd53acfc765f242a10d2123; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P78fcc38a640611ee6013349c5dc3a56132202360ebd53acfc765f242a10d2123

namespace PerfectPower.SOEModelPackets
def obs116 := PerfectPower.CheckedSOE.P78fcc38a640611ee6013349c5dc3a56132202360ebd53acfc765f242a10d2123.obs
def step116 := PerfectPower.CheckedSOE.P78fcc38a640611ee6013349c5dc3a56132202360ebd53acfc765f242a10d2123.step
def q116 := PerfectPower.CheckedSOE.P78fcc38a640611ee6013349c5dc3a56132202360ebd53acfc765f242a10d2123.q
def out116 := PerfectPower.CheckedSOE.P78fcc38a640611ee6013349c5dc3a56132202360ebd53acfc765f242a10d2123.out
def target116 := PerfectPower.CheckedSOE.P78fcc38a640611ee6013349c5dc3a56132202360ebd53acfc765f242a10d2123.target
theorem complete116 (s t : Fin 2) : SOESemantics.Equivalent step116 obs116 s t ↔ q116 s = q116 t := PerfectPower.CheckedSOE.P78fcc38a640611ee6013349c5dc3a56132202360ebd53acfc765f242a10d2123.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4d880382df609f1289da1c91fabb38c4c33a74467c3a8b646c0917a3e4ac2b7f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4d880382df609f1289da1c91fabb38c4c33a74467c3a8b646c0917a3e4ac2b7f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4d880382df609f1289da1c91fabb38c4c33a74467c3a8b646c0917a3e4ac2b7f

namespace PerfectPower.SOEModelPackets
def obs117 := PerfectPower.CheckedSOE.P4d880382df609f1289da1c91fabb38c4c33a74467c3a8b646c0917a3e4ac2b7f.obs
def step117 := PerfectPower.CheckedSOE.P4d880382df609f1289da1c91fabb38c4c33a74467c3a8b646c0917a3e4ac2b7f.step
def q117 := PerfectPower.CheckedSOE.P4d880382df609f1289da1c91fabb38c4c33a74467c3a8b646c0917a3e4ac2b7f.q
def out117 := PerfectPower.CheckedSOE.P4d880382df609f1289da1c91fabb38c4c33a74467c3a8b646c0917a3e4ac2b7f.out
def target117 := PerfectPower.CheckedSOE.P4d880382df609f1289da1c91fabb38c4c33a74467c3a8b646c0917a3e4ac2b7f.target
theorem complete117 (s t : Fin 2) : SOESemantics.Equivalent step117 obs117 s t ↔ q117 s = q117 t := PerfectPower.CheckedSOE.P4d880382df609f1289da1c91fabb38c4c33a74467c3a8b646c0917a3e4ac2b7f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P271f2768351bafd461645eaa2c07789914bc651c8101c61d5f86c29857e054f4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 271f2768351bafd461645eaa2c07789914bc651c8101c61d5f86c29857e054f4; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P271f2768351bafd461645eaa2c07789914bc651c8101c61d5f86c29857e054f4

namespace PerfectPower.SOEModelPackets
def obs118 := PerfectPower.CheckedSOE.P271f2768351bafd461645eaa2c07789914bc651c8101c61d5f86c29857e054f4.obs
def step118 := PerfectPower.CheckedSOE.P271f2768351bafd461645eaa2c07789914bc651c8101c61d5f86c29857e054f4.step
def q118 := PerfectPower.CheckedSOE.P271f2768351bafd461645eaa2c07789914bc651c8101c61d5f86c29857e054f4.q
def out118 := PerfectPower.CheckedSOE.P271f2768351bafd461645eaa2c07789914bc651c8101c61d5f86c29857e054f4.out
def target118 := PerfectPower.CheckedSOE.P271f2768351bafd461645eaa2c07789914bc651c8101c61d5f86c29857e054f4.target
theorem complete118 (s t : Fin 2) : SOESemantics.Equivalent step118 obs118 s t ↔ q118 s = q118 t := PerfectPower.CheckedSOE.P271f2768351bafd461645eaa2c07789914bc651c8101c61d5f86c29857e054f4.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P44bf8940fa266406db413e35deca9bbcab0dcbc8d29c10a8e98e8ce9d673e829
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 44bf8940fa266406db413e35deca9bbcab0dcbc8d29c10a8e98e8ce9d673e829; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P44bf8940fa266406db413e35deca9bbcab0dcbc8d29c10a8e98e8ce9d673e829

namespace PerfectPower.SOEModelPackets
def obs119 := PerfectPower.CheckedSOE.P44bf8940fa266406db413e35deca9bbcab0dcbc8d29c10a8e98e8ce9d673e829.obs
def step119 := PerfectPower.CheckedSOE.P44bf8940fa266406db413e35deca9bbcab0dcbc8d29c10a8e98e8ce9d673e829.step
def q119 := PerfectPower.CheckedSOE.P44bf8940fa266406db413e35deca9bbcab0dcbc8d29c10a8e98e8ce9d673e829.q
def out119 := PerfectPower.CheckedSOE.P44bf8940fa266406db413e35deca9bbcab0dcbc8d29c10a8e98e8ce9d673e829.out
def target119 := PerfectPower.CheckedSOE.P44bf8940fa266406db413e35deca9bbcab0dcbc8d29c10a8e98e8ce9d673e829.target
theorem complete119 (s t : Fin 2) : SOESemantics.Equivalent step119 obs119 s t ↔ q119 s = q119 t := PerfectPower.CheckedSOE.P44bf8940fa266406db413e35deca9bbcab0dcbc8d29c10a8e98e8ce9d673e829.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pdcd8d789415508d195a60090937e486fb7b6bb3ae41f4930118f45bc04096976
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: dcd8d789415508d195a60090937e486fb7b6bb3ae41f4930118f45bc04096976; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pdcd8d789415508d195a60090937e486fb7b6bb3ae41f4930118f45bc04096976

namespace PerfectPower.SOEModelPackets
def obs120 := PerfectPower.CheckedSOE.Pdcd8d789415508d195a60090937e486fb7b6bb3ae41f4930118f45bc04096976.obs
def step120 := PerfectPower.CheckedSOE.Pdcd8d789415508d195a60090937e486fb7b6bb3ae41f4930118f45bc04096976.step
def q120 := PerfectPower.CheckedSOE.Pdcd8d789415508d195a60090937e486fb7b6bb3ae41f4930118f45bc04096976.q
def out120 := PerfectPower.CheckedSOE.Pdcd8d789415508d195a60090937e486fb7b6bb3ae41f4930118f45bc04096976.out
def target120 := PerfectPower.CheckedSOE.Pdcd8d789415508d195a60090937e486fb7b6bb3ae41f4930118f45bc04096976.target
theorem complete120 (s t : Fin 2) : SOESemantics.Equivalent step120 obs120 s t ↔ q120 s = q120 t := PerfectPower.CheckedSOE.Pdcd8d789415508d195a60090937e486fb7b6bb3ae41f4930118f45bc04096976.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P248014c8c4d0e4580424f6045ef33ebc745957db45be82e4d52bdb42fcbdc93b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 248014c8c4d0e4580424f6045ef33ebc745957db45be82e4d52bdb42fcbdc93b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P248014c8c4d0e4580424f6045ef33ebc745957db45be82e4d52bdb42fcbdc93b

namespace PerfectPower.SOEModelPackets
def obs121 := PerfectPower.CheckedSOE.P248014c8c4d0e4580424f6045ef33ebc745957db45be82e4d52bdb42fcbdc93b.obs
def step121 := PerfectPower.CheckedSOE.P248014c8c4d0e4580424f6045ef33ebc745957db45be82e4d52bdb42fcbdc93b.step
def q121 := PerfectPower.CheckedSOE.P248014c8c4d0e4580424f6045ef33ebc745957db45be82e4d52bdb42fcbdc93b.q
def out121 := PerfectPower.CheckedSOE.P248014c8c4d0e4580424f6045ef33ebc745957db45be82e4d52bdb42fcbdc93b.out
def target121 := PerfectPower.CheckedSOE.P248014c8c4d0e4580424f6045ef33ebc745957db45be82e4d52bdb42fcbdc93b.target
theorem complete121 (s t : Fin 2) : SOESemantics.Equivalent step121 obs121 s t ↔ q121 s = q121 t := PerfectPower.CheckedSOE.P248014c8c4d0e4580424f6045ef33ebc745957db45be82e4d52bdb42fcbdc93b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P43d46ff1dbe9e76f573fd19f685bced5c0d92822763797c90dfd2e3a84b0f13b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 43d46ff1dbe9e76f573fd19f685bced5c0d92822763797c90dfd2e3a84b0f13b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P43d46ff1dbe9e76f573fd19f685bced5c0d92822763797c90dfd2e3a84b0f13b

namespace PerfectPower.SOEModelPackets
def obs122 := PerfectPower.CheckedSOE.P43d46ff1dbe9e76f573fd19f685bced5c0d92822763797c90dfd2e3a84b0f13b.obs
def step122 := PerfectPower.CheckedSOE.P43d46ff1dbe9e76f573fd19f685bced5c0d92822763797c90dfd2e3a84b0f13b.step
def q122 := PerfectPower.CheckedSOE.P43d46ff1dbe9e76f573fd19f685bced5c0d92822763797c90dfd2e3a84b0f13b.q
def out122 := PerfectPower.CheckedSOE.P43d46ff1dbe9e76f573fd19f685bced5c0d92822763797c90dfd2e3a84b0f13b.out
def target122 := PerfectPower.CheckedSOE.P43d46ff1dbe9e76f573fd19f685bced5c0d92822763797c90dfd2e3a84b0f13b.target
theorem complete122 (s t : Fin 2) : SOESemantics.Equivalent step122 obs122 s t ↔ q122 s = q122 t := PerfectPower.CheckedSOE.P43d46ff1dbe9e76f573fd19f685bced5c0d92822763797c90dfd2e3a84b0f13b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbffbf26d444ce319b3552afce55f684550bb31f2d544dbd547efd92a9efe7e49
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: bffbf26d444ce319b3552afce55f684550bb31f2d544dbd547efd92a9efe7e49; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbffbf26d444ce319b3552afce55f684550bb31f2d544dbd547efd92a9efe7e49

namespace PerfectPower.SOEModelPackets
def obs123 := PerfectPower.CheckedSOE.Pbffbf26d444ce319b3552afce55f684550bb31f2d544dbd547efd92a9efe7e49.obs
def step123 := PerfectPower.CheckedSOE.Pbffbf26d444ce319b3552afce55f684550bb31f2d544dbd547efd92a9efe7e49.step
def q123 := PerfectPower.CheckedSOE.Pbffbf26d444ce319b3552afce55f684550bb31f2d544dbd547efd92a9efe7e49.q
def out123 := PerfectPower.CheckedSOE.Pbffbf26d444ce319b3552afce55f684550bb31f2d544dbd547efd92a9efe7e49.out
def target123 := PerfectPower.CheckedSOE.Pbffbf26d444ce319b3552afce55f684550bb31f2d544dbd547efd92a9efe7e49.target
theorem complete123 (s t : Fin 2) : SOESemantics.Equivalent step123 obs123 s t ↔ q123 s = q123 t := PerfectPower.CheckedSOE.Pbffbf26d444ce319b3552afce55f684550bb31f2d544dbd547efd92a9efe7e49.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P89b078085a4af0b1fbddaeb2e0adb3398aea35c4e7e480f7e57e2ede0d4d35f3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 89b078085a4af0b1fbddaeb2e0adb3398aea35c4e7e480f7e57e2ede0d4d35f3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P89b078085a4af0b1fbddaeb2e0adb3398aea35c4e7e480f7e57e2ede0d4d35f3

namespace PerfectPower.SOEModelPackets
def obs124 := PerfectPower.CheckedSOE.P89b078085a4af0b1fbddaeb2e0adb3398aea35c4e7e480f7e57e2ede0d4d35f3.obs
def step124 := PerfectPower.CheckedSOE.P89b078085a4af0b1fbddaeb2e0adb3398aea35c4e7e480f7e57e2ede0d4d35f3.step
def q124 := PerfectPower.CheckedSOE.P89b078085a4af0b1fbddaeb2e0adb3398aea35c4e7e480f7e57e2ede0d4d35f3.q
def out124 := PerfectPower.CheckedSOE.P89b078085a4af0b1fbddaeb2e0adb3398aea35c4e7e480f7e57e2ede0d4d35f3.out
def target124 := PerfectPower.CheckedSOE.P89b078085a4af0b1fbddaeb2e0adb3398aea35c4e7e480f7e57e2ede0d4d35f3.target
theorem complete124 (s t : Fin 2) : SOESemantics.Equivalent step124 obs124 s t ↔ q124 s = q124 t := PerfectPower.CheckedSOE.P89b078085a4af0b1fbddaeb2e0adb3398aea35c4e7e480f7e57e2ede0d4d35f3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf08b8ce6577fa67dd2b8638507d1c76565b13b500db73ef5b00b88fb5fca2144
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f08b8ce6577fa67dd2b8638507d1c76565b13b500db73ef5b00b88fb5fca2144; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf08b8ce6577fa67dd2b8638507d1c76565b13b500db73ef5b00b88fb5fca2144

namespace PerfectPower.SOEModelPackets
def obs125 := PerfectPower.CheckedSOE.Pf08b8ce6577fa67dd2b8638507d1c76565b13b500db73ef5b00b88fb5fca2144.obs
def step125 := PerfectPower.CheckedSOE.Pf08b8ce6577fa67dd2b8638507d1c76565b13b500db73ef5b00b88fb5fca2144.step
def q125 := PerfectPower.CheckedSOE.Pf08b8ce6577fa67dd2b8638507d1c76565b13b500db73ef5b00b88fb5fca2144.q
def out125 := PerfectPower.CheckedSOE.Pf08b8ce6577fa67dd2b8638507d1c76565b13b500db73ef5b00b88fb5fca2144.out
def target125 := PerfectPower.CheckedSOE.Pf08b8ce6577fa67dd2b8638507d1c76565b13b500db73ef5b00b88fb5fca2144.target
theorem complete125 (s t : Fin 2) : SOESemantics.Equivalent step125 obs125 s t ↔ q125 s = q125 t := PerfectPower.CheckedSOE.Pf08b8ce6577fa67dd2b8638507d1c76565b13b500db73ef5b00b88fb5fca2144.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc02d34f4460bbc9008ff29af15c1055066d86a5f777d855fced176b42164be9b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c02d34f4460bbc9008ff29af15c1055066d86a5f777d855fced176b42164be9b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc02d34f4460bbc9008ff29af15c1055066d86a5f777d855fced176b42164be9b

namespace PerfectPower.SOEModelPackets
def obs126 := PerfectPower.CheckedSOE.Pc02d34f4460bbc9008ff29af15c1055066d86a5f777d855fced176b42164be9b.obs
def step126 := PerfectPower.CheckedSOE.Pc02d34f4460bbc9008ff29af15c1055066d86a5f777d855fced176b42164be9b.step
def q126 := PerfectPower.CheckedSOE.Pc02d34f4460bbc9008ff29af15c1055066d86a5f777d855fced176b42164be9b.q
def out126 := PerfectPower.CheckedSOE.Pc02d34f4460bbc9008ff29af15c1055066d86a5f777d855fced176b42164be9b.out
def target126 := PerfectPower.CheckedSOE.Pc02d34f4460bbc9008ff29af15c1055066d86a5f777d855fced176b42164be9b.target
theorem complete126 (s t : Fin 2) : SOESemantics.Equivalent step126 obs126 s t ↔ q126 s = q126 t := PerfectPower.CheckedSOE.Pc02d34f4460bbc9008ff29af15c1055066d86a5f777d855fced176b42164be9b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P866e953acb9338bcb54a1aece108b6f09cdf087526375218bb214c074c7294e8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 866e953acb9338bcb54a1aece108b6f09cdf087526375218bb214c074c7294e8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P866e953acb9338bcb54a1aece108b6f09cdf087526375218bb214c074c7294e8

namespace PerfectPower.SOEModelPackets
def obs127 := PerfectPower.CheckedSOE.P866e953acb9338bcb54a1aece108b6f09cdf087526375218bb214c074c7294e8.obs
def step127 := PerfectPower.CheckedSOE.P866e953acb9338bcb54a1aece108b6f09cdf087526375218bb214c074c7294e8.step
def q127 := PerfectPower.CheckedSOE.P866e953acb9338bcb54a1aece108b6f09cdf087526375218bb214c074c7294e8.q
def out127 := PerfectPower.CheckedSOE.P866e953acb9338bcb54a1aece108b6f09cdf087526375218bb214c074c7294e8.out
def target127 := PerfectPower.CheckedSOE.P866e953acb9338bcb54a1aece108b6f09cdf087526375218bb214c074c7294e8.target
theorem complete127 (s t : Fin 2) : SOESemantics.Equivalent step127 obs127 s t ↔ q127 s = q127 t := PerfectPower.CheckedSOE.P866e953acb9338bcb54a1aece108b6f09cdf087526375218bb214c074c7294e8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P9c06022428cdfdfde70f44616df6005b6805ec181fc5b20943f14344e82f2b3e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 9c06022428cdfdfde70f44616df6005b6805ec181fc5b20943f14344e82f2b3e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P9c06022428cdfdfde70f44616df6005b6805ec181fc5b20943f14344e82f2b3e

namespace PerfectPower.SOEModelPackets
def obs128 := PerfectPower.CheckedSOE.P9c06022428cdfdfde70f44616df6005b6805ec181fc5b20943f14344e82f2b3e.obs
def step128 := PerfectPower.CheckedSOE.P9c06022428cdfdfde70f44616df6005b6805ec181fc5b20943f14344e82f2b3e.step
def q128 := PerfectPower.CheckedSOE.P9c06022428cdfdfde70f44616df6005b6805ec181fc5b20943f14344e82f2b3e.q
def out128 := PerfectPower.CheckedSOE.P9c06022428cdfdfde70f44616df6005b6805ec181fc5b20943f14344e82f2b3e.out
def target128 := PerfectPower.CheckedSOE.P9c06022428cdfdfde70f44616df6005b6805ec181fc5b20943f14344e82f2b3e.target
theorem complete128 (s t : Fin 2) : SOESemantics.Equivalent step128 obs128 s t ↔ q128 s = q128 t := PerfectPower.CheckedSOE.P9c06022428cdfdfde70f44616df6005b6805ec181fc5b20943f14344e82f2b3e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pca4b1b6e72e692da8a7f4127db7cfeab161a0c8d37fb8b65cbb6acf61d4fa2d3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ca4b1b6e72e692da8a7f4127db7cfeab161a0c8d37fb8b65cbb6acf61d4fa2d3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pca4b1b6e72e692da8a7f4127db7cfeab161a0c8d37fb8b65cbb6acf61d4fa2d3

namespace PerfectPower.SOEModelPackets
def obs129 := PerfectPower.CheckedSOE.Pca4b1b6e72e692da8a7f4127db7cfeab161a0c8d37fb8b65cbb6acf61d4fa2d3.obs
def step129 := PerfectPower.CheckedSOE.Pca4b1b6e72e692da8a7f4127db7cfeab161a0c8d37fb8b65cbb6acf61d4fa2d3.step
def q129 := PerfectPower.CheckedSOE.Pca4b1b6e72e692da8a7f4127db7cfeab161a0c8d37fb8b65cbb6acf61d4fa2d3.q
def out129 := PerfectPower.CheckedSOE.Pca4b1b6e72e692da8a7f4127db7cfeab161a0c8d37fb8b65cbb6acf61d4fa2d3.out
def target129 := PerfectPower.CheckedSOE.Pca4b1b6e72e692da8a7f4127db7cfeab161a0c8d37fb8b65cbb6acf61d4fa2d3.target
theorem complete129 (s t : Fin 2) : SOESemantics.Equivalent step129 obs129 s t ↔ q129 s = q129 t := PerfectPower.CheckedSOE.Pca4b1b6e72e692da8a7f4127db7cfeab161a0c8d37fb8b65cbb6acf61d4fa2d3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Padfb886053a41910f275775e8f20843da8800d02c42886b08b2f018cdbf72d20
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: adfb886053a41910f275775e8f20843da8800d02c42886b08b2f018cdbf72d20; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Padfb886053a41910f275775e8f20843da8800d02c42886b08b2f018cdbf72d20

namespace PerfectPower.SOEModelPackets
def obs130 := PerfectPower.CheckedSOE.Padfb886053a41910f275775e8f20843da8800d02c42886b08b2f018cdbf72d20.obs
def step130 := PerfectPower.CheckedSOE.Padfb886053a41910f275775e8f20843da8800d02c42886b08b2f018cdbf72d20.step
def q130 := PerfectPower.CheckedSOE.Padfb886053a41910f275775e8f20843da8800d02c42886b08b2f018cdbf72d20.q
def out130 := PerfectPower.CheckedSOE.Padfb886053a41910f275775e8f20843da8800d02c42886b08b2f018cdbf72d20.out
def target130 := PerfectPower.CheckedSOE.Padfb886053a41910f275775e8f20843da8800d02c42886b08b2f018cdbf72d20.target
theorem complete130 (s t : Fin 2) : SOESemantics.Equivalent step130 obs130 s t ↔ q130 s = q130 t := PerfectPower.CheckedSOE.Padfb886053a41910f275775e8f20843da8800d02c42886b08b2f018cdbf72d20.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb544825edc17dc9413f26138cd3674435792becec003f8dc4e799c843c5f0bd1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b544825edc17dc9413f26138cd3674435792becec003f8dc4e799c843c5f0bd1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb544825edc17dc9413f26138cd3674435792becec003f8dc4e799c843c5f0bd1

namespace PerfectPower.SOEModelPackets
def obs131 := PerfectPower.CheckedSOE.Pb544825edc17dc9413f26138cd3674435792becec003f8dc4e799c843c5f0bd1.obs
def step131 := PerfectPower.CheckedSOE.Pb544825edc17dc9413f26138cd3674435792becec003f8dc4e799c843c5f0bd1.step
def q131 := PerfectPower.CheckedSOE.Pb544825edc17dc9413f26138cd3674435792becec003f8dc4e799c843c5f0bd1.q
def out131 := PerfectPower.CheckedSOE.Pb544825edc17dc9413f26138cd3674435792becec003f8dc4e799c843c5f0bd1.out
def target131 := PerfectPower.CheckedSOE.Pb544825edc17dc9413f26138cd3674435792becec003f8dc4e799c843c5f0bd1.target
theorem complete131 (s t : Fin 2) : SOESemantics.Equivalent step131 obs131 s t ↔ q131 s = q131 t := PerfectPower.CheckedSOE.Pb544825edc17dc9413f26138cd3674435792becec003f8dc4e799c843c5f0bd1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P1d3ded57829b5339c90758e4b0c87ae83622fc8bb467a71366f84dbac0172f43
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 1d3ded57829b5339c90758e4b0c87ae83622fc8bb467a71366f84dbac0172f43; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P1d3ded57829b5339c90758e4b0c87ae83622fc8bb467a71366f84dbac0172f43

namespace PerfectPower.SOEModelPackets
def obs132 := PerfectPower.CheckedSOE.P1d3ded57829b5339c90758e4b0c87ae83622fc8bb467a71366f84dbac0172f43.obs
def step132 := PerfectPower.CheckedSOE.P1d3ded57829b5339c90758e4b0c87ae83622fc8bb467a71366f84dbac0172f43.step
def q132 := PerfectPower.CheckedSOE.P1d3ded57829b5339c90758e4b0c87ae83622fc8bb467a71366f84dbac0172f43.q
def out132 := PerfectPower.CheckedSOE.P1d3ded57829b5339c90758e4b0c87ae83622fc8bb467a71366f84dbac0172f43.out
def target132 := PerfectPower.CheckedSOE.P1d3ded57829b5339c90758e4b0c87ae83622fc8bb467a71366f84dbac0172f43.target
theorem complete132 (s t : Fin 2) : SOESemantics.Equivalent step132 obs132 s t ↔ q132 s = q132 t := PerfectPower.CheckedSOE.P1d3ded57829b5339c90758e4b0c87ae83622fc8bb467a71366f84dbac0172f43.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf4551b0e4e58f58698d4ea1b79795a590c40de963dd6fd6b8c59af9b63afa32b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f4551b0e4e58f58698d4ea1b79795a590c40de963dd6fd6b8c59af9b63afa32b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf4551b0e4e58f58698d4ea1b79795a590c40de963dd6fd6b8c59af9b63afa32b

namespace PerfectPower.SOEModelPackets
def obs133 := PerfectPower.CheckedSOE.Pf4551b0e4e58f58698d4ea1b79795a590c40de963dd6fd6b8c59af9b63afa32b.obs
def step133 := PerfectPower.CheckedSOE.Pf4551b0e4e58f58698d4ea1b79795a590c40de963dd6fd6b8c59af9b63afa32b.step
def q133 := PerfectPower.CheckedSOE.Pf4551b0e4e58f58698d4ea1b79795a590c40de963dd6fd6b8c59af9b63afa32b.q
def out133 := PerfectPower.CheckedSOE.Pf4551b0e4e58f58698d4ea1b79795a590c40de963dd6fd6b8c59af9b63afa32b.out
def target133 := PerfectPower.CheckedSOE.Pf4551b0e4e58f58698d4ea1b79795a590c40de963dd6fd6b8c59af9b63afa32b.target
theorem complete133 (s t : Fin 2) : SOESemantics.Equivalent step133 obs133 s t ↔ q133 s = q133 t := PerfectPower.CheckedSOE.Pf4551b0e4e58f58698d4ea1b79795a590c40de963dd6fd6b8c59af9b63afa32b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6c817980589d3bc2c08ab64d3d19e5b17294d0380c69461e53eb559d78d48f72
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6c817980589d3bc2c08ab64d3d19e5b17294d0380c69461e53eb559d78d48f72; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6c817980589d3bc2c08ab64d3d19e5b17294d0380c69461e53eb559d78d48f72

namespace PerfectPower.SOEModelPackets
def obs134 := PerfectPower.CheckedSOE.P6c817980589d3bc2c08ab64d3d19e5b17294d0380c69461e53eb559d78d48f72.obs
def step134 := PerfectPower.CheckedSOE.P6c817980589d3bc2c08ab64d3d19e5b17294d0380c69461e53eb559d78d48f72.step
def q134 := PerfectPower.CheckedSOE.P6c817980589d3bc2c08ab64d3d19e5b17294d0380c69461e53eb559d78d48f72.q
def out134 := PerfectPower.CheckedSOE.P6c817980589d3bc2c08ab64d3d19e5b17294d0380c69461e53eb559d78d48f72.out
def target134 := PerfectPower.CheckedSOE.P6c817980589d3bc2c08ab64d3d19e5b17294d0380c69461e53eb559d78d48f72.target
theorem complete134 (s t : Fin 2) : SOESemantics.Equivalent step134 obs134 s t ↔ q134 s = q134 t := PerfectPower.CheckedSOE.P6c817980589d3bc2c08ab64d3d19e5b17294d0380c69461e53eb559d78d48f72.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbe1c447bbc9e7bcd25f79f5e537d160cd4e21456a13f09e4870aed3ace34cbe9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: be1c447bbc9e7bcd25f79f5e537d160cd4e21456a13f09e4870aed3ace34cbe9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbe1c447bbc9e7bcd25f79f5e537d160cd4e21456a13f09e4870aed3ace34cbe9

namespace PerfectPower.SOEModelPackets
def obs135 := PerfectPower.CheckedSOE.Pbe1c447bbc9e7bcd25f79f5e537d160cd4e21456a13f09e4870aed3ace34cbe9.obs
def step135 := PerfectPower.CheckedSOE.Pbe1c447bbc9e7bcd25f79f5e537d160cd4e21456a13f09e4870aed3ace34cbe9.step
def q135 := PerfectPower.CheckedSOE.Pbe1c447bbc9e7bcd25f79f5e537d160cd4e21456a13f09e4870aed3ace34cbe9.q
def out135 := PerfectPower.CheckedSOE.Pbe1c447bbc9e7bcd25f79f5e537d160cd4e21456a13f09e4870aed3ace34cbe9.out
def target135 := PerfectPower.CheckedSOE.Pbe1c447bbc9e7bcd25f79f5e537d160cd4e21456a13f09e4870aed3ace34cbe9.target
theorem complete135 (s t : Fin 2) : SOESemantics.Equivalent step135 obs135 s t ↔ q135 s = q135 t := PerfectPower.CheckedSOE.Pbe1c447bbc9e7bcd25f79f5e537d160cd4e21456a13f09e4870aed3ace34cbe9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0f05ae2246f68d99de0a900b1668a3688cd265b5217ec2262eb511c504503bb2
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0f05ae2246f68d99de0a900b1668a3688cd265b5217ec2262eb511c504503bb2; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0f05ae2246f68d99de0a900b1668a3688cd265b5217ec2262eb511c504503bb2

namespace PerfectPower.SOEModelPackets
def obs136 := PerfectPower.CheckedSOE.P0f05ae2246f68d99de0a900b1668a3688cd265b5217ec2262eb511c504503bb2.obs
def step136 := PerfectPower.CheckedSOE.P0f05ae2246f68d99de0a900b1668a3688cd265b5217ec2262eb511c504503bb2.step
def q136 := PerfectPower.CheckedSOE.P0f05ae2246f68d99de0a900b1668a3688cd265b5217ec2262eb511c504503bb2.q
def out136 := PerfectPower.CheckedSOE.P0f05ae2246f68d99de0a900b1668a3688cd265b5217ec2262eb511c504503bb2.out
def target136 := PerfectPower.CheckedSOE.P0f05ae2246f68d99de0a900b1668a3688cd265b5217ec2262eb511c504503bb2.target
theorem complete136 (s t : Fin 2) : SOESemantics.Equivalent step136 obs136 s t ↔ q136 s = q136 t := PerfectPower.CheckedSOE.P0f05ae2246f68d99de0a900b1668a3688cd265b5217ec2262eb511c504503bb2.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P11b831db10059e777d78c332a7641cca15d4e97f1fde53d7e830342a638555bd
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 11b831db10059e777d78c332a7641cca15d4e97f1fde53d7e830342a638555bd; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P11b831db10059e777d78c332a7641cca15d4e97f1fde53d7e830342a638555bd

namespace PerfectPower.SOEModelPackets
def obs137 := PerfectPower.CheckedSOE.P11b831db10059e777d78c332a7641cca15d4e97f1fde53d7e830342a638555bd.obs
def step137 := PerfectPower.CheckedSOE.P11b831db10059e777d78c332a7641cca15d4e97f1fde53d7e830342a638555bd.step
def q137 := PerfectPower.CheckedSOE.P11b831db10059e777d78c332a7641cca15d4e97f1fde53d7e830342a638555bd.q
def out137 := PerfectPower.CheckedSOE.P11b831db10059e777d78c332a7641cca15d4e97f1fde53d7e830342a638555bd.out
def target137 := PerfectPower.CheckedSOE.P11b831db10059e777d78c332a7641cca15d4e97f1fde53d7e830342a638555bd.target
theorem complete137 (s t : Fin 2) : SOESemantics.Equivalent step137 obs137 s t ↔ q137 s = q137 t := PerfectPower.CheckedSOE.P11b831db10059e777d78c332a7641cca15d4e97f1fde53d7e830342a638555bd.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P152d67a19d5dccc064eb9753ad79791b5bc531f6cb12fa45ca82f73ceebffafb
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 152d67a19d5dccc064eb9753ad79791b5bc531f6cb12fa45ca82f73ceebffafb; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P152d67a19d5dccc064eb9753ad79791b5bc531f6cb12fa45ca82f73ceebffafb

namespace PerfectPower.SOEModelPackets
def obs138 := PerfectPower.CheckedSOE.P152d67a19d5dccc064eb9753ad79791b5bc531f6cb12fa45ca82f73ceebffafb.obs
def step138 := PerfectPower.CheckedSOE.P152d67a19d5dccc064eb9753ad79791b5bc531f6cb12fa45ca82f73ceebffafb.step
def q138 := PerfectPower.CheckedSOE.P152d67a19d5dccc064eb9753ad79791b5bc531f6cb12fa45ca82f73ceebffafb.q
def out138 := PerfectPower.CheckedSOE.P152d67a19d5dccc064eb9753ad79791b5bc531f6cb12fa45ca82f73ceebffafb.out
def target138 := PerfectPower.CheckedSOE.P152d67a19d5dccc064eb9753ad79791b5bc531f6cb12fa45ca82f73ceebffafb.target
theorem complete138 (s t : Fin 2) : SOESemantics.Equivalent step138 obs138 s t ↔ q138 s = q138 t := PerfectPower.CheckedSOE.P152d67a19d5dccc064eb9753ad79791b5bc531f6cb12fa45ca82f73ceebffafb.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P1d39c2f9968cbf8fa1da1d4db6fd126e1118a1892c647dba37bb96ff7b20095c
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 1d39c2f9968cbf8fa1da1d4db6fd126e1118a1892c647dba37bb96ff7b20095c; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P1d39c2f9968cbf8fa1da1d4db6fd126e1118a1892c647dba37bb96ff7b20095c

namespace PerfectPower.SOEModelPackets
def obs139 := PerfectPower.CheckedSOE.P1d39c2f9968cbf8fa1da1d4db6fd126e1118a1892c647dba37bb96ff7b20095c.obs
def step139 := PerfectPower.CheckedSOE.P1d39c2f9968cbf8fa1da1d4db6fd126e1118a1892c647dba37bb96ff7b20095c.step
def q139 := PerfectPower.CheckedSOE.P1d39c2f9968cbf8fa1da1d4db6fd126e1118a1892c647dba37bb96ff7b20095c.q
def out139 := PerfectPower.CheckedSOE.P1d39c2f9968cbf8fa1da1d4db6fd126e1118a1892c647dba37bb96ff7b20095c.out
def target139 := PerfectPower.CheckedSOE.P1d39c2f9968cbf8fa1da1d4db6fd126e1118a1892c647dba37bb96ff7b20095c.target
theorem complete139 (s t : Fin 2) : SOESemantics.Equivalent step139 obs139 s t ↔ q139 s = q139 t := PerfectPower.CheckedSOE.P1d39c2f9968cbf8fa1da1d4db6fd126e1118a1892c647dba37bb96ff7b20095c.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P941cb158f65bc3a912469a3c8309ad3ade8c26084be25c69de7e8569bbc7b9a0
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 941cb158f65bc3a912469a3c8309ad3ade8c26084be25c69de7e8569bbc7b9a0; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P941cb158f65bc3a912469a3c8309ad3ade8c26084be25c69de7e8569bbc7b9a0

namespace PerfectPower.SOEModelPackets
def obs140 := PerfectPower.CheckedSOE.P941cb158f65bc3a912469a3c8309ad3ade8c26084be25c69de7e8569bbc7b9a0.obs
def step140 := PerfectPower.CheckedSOE.P941cb158f65bc3a912469a3c8309ad3ade8c26084be25c69de7e8569bbc7b9a0.step
def q140 := PerfectPower.CheckedSOE.P941cb158f65bc3a912469a3c8309ad3ade8c26084be25c69de7e8569bbc7b9a0.q
def out140 := PerfectPower.CheckedSOE.P941cb158f65bc3a912469a3c8309ad3ade8c26084be25c69de7e8569bbc7b9a0.out
def target140 := PerfectPower.CheckedSOE.P941cb158f65bc3a912469a3c8309ad3ade8c26084be25c69de7e8569bbc7b9a0.target
theorem complete140 (s t : Fin 2) : SOESemantics.Equivalent step140 obs140 s t ↔ q140 s = q140 t := PerfectPower.CheckedSOE.P941cb158f65bc3a912469a3c8309ad3ade8c26084be25c69de7e8569bbc7b9a0.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0a665e50d88365e7b87b5ee141c10489c300ecff91d11e7fe7120d245f0ea095
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0a665e50d88365e7b87b5ee141c10489c300ecff91d11e7fe7120d245f0ea095; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0a665e50d88365e7b87b5ee141c10489c300ecff91d11e7fe7120d245f0ea095

namespace PerfectPower.SOEModelPackets
def obs141 := PerfectPower.CheckedSOE.P0a665e50d88365e7b87b5ee141c10489c300ecff91d11e7fe7120d245f0ea095.obs
def step141 := PerfectPower.CheckedSOE.P0a665e50d88365e7b87b5ee141c10489c300ecff91d11e7fe7120d245f0ea095.step
def q141 := PerfectPower.CheckedSOE.P0a665e50d88365e7b87b5ee141c10489c300ecff91d11e7fe7120d245f0ea095.q
def out141 := PerfectPower.CheckedSOE.P0a665e50d88365e7b87b5ee141c10489c300ecff91d11e7fe7120d245f0ea095.out
def target141 := PerfectPower.CheckedSOE.P0a665e50d88365e7b87b5ee141c10489c300ecff91d11e7fe7120d245f0ea095.target
theorem complete141 (s t : Fin 2) : SOESemantics.Equivalent step141 obs141 s t ↔ q141 s = q141 t := PerfectPower.CheckedSOE.P0a665e50d88365e7b87b5ee141c10489c300ecff91d11e7fe7120d245f0ea095.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb98983310fe95f246f2595457fe7ece684b0ed19cf6a766050f072a9b4988a82
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b98983310fe95f246f2595457fe7ece684b0ed19cf6a766050f072a9b4988a82; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb98983310fe95f246f2595457fe7ece684b0ed19cf6a766050f072a9b4988a82

namespace PerfectPower.SOEModelPackets
def obs142 := PerfectPower.CheckedSOE.Pb98983310fe95f246f2595457fe7ece684b0ed19cf6a766050f072a9b4988a82.obs
def step142 := PerfectPower.CheckedSOE.Pb98983310fe95f246f2595457fe7ece684b0ed19cf6a766050f072a9b4988a82.step
def q142 := PerfectPower.CheckedSOE.Pb98983310fe95f246f2595457fe7ece684b0ed19cf6a766050f072a9b4988a82.q
def out142 := PerfectPower.CheckedSOE.Pb98983310fe95f246f2595457fe7ece684b0ed19cf6a766050f072a9b4988a82.out
def target142 := PerfectPower.CheckedSOE.Pb98983310fe95f246f2595457fe7ece684b0ed19cf6a766050f072a9b4988a82.target
theorem complete142 (s t : Fin 2) : SOESemantics.Equivalent step142 obs142 s t ↔ q142 s = q142 t := PerfectPower.CheckedSOE.Pb98983310fe95f246f2595457fe7ece684b0ed19cf6a766050f072a9b4988a82.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd0241c57d846289ad91922c97dce251b6632ae492fa8723ebd7cf12b560dcb6a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d0241c57d846289ad91922c97dce251b6632ae492fa8723ebd7cf12b560dcb6a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd0241c57d846289ad91922c97dce251b6632ae492fa8723ebd7cf12b560dcb6a

namespace PerfectPower.SOEModelPackets
def obs143 := PerfectPower.CheckedSOE.Pd0241c57d846289ad91922c97dce251b6632ae492fa8723ebd7cf12b560dcb6a.obs
def step143 := PerfectPower.CheckedSOE.Pd0241c57d846289ad91922c97dce251b6632ae492fa8723ebd7cf12b560dcb6a.step
def q143 := PerfectPower.CheckedSOE.Pd0241c57d846289ad91922c97dce251b6632ae492fa8723ebd7cf12b560dcb6a.q
def out143 := PerfectPower.CheckedSOE.Pd0241c57d846289ad91922c97dce251b6632ae492fa8723ebd7cf12b560dcb6a.out
def target143 := PerfectPower.CheckedSOE.Pd0241c57d846289ad91922c97dce251b6632ae492fa8723ebd7cf12b560dcb6a.target
theorem complete143 (s t : Fin 2) : SOESemantics.Equivalent step143 obs143 s t ↔ q143 s = q143 t := PerfectPower.CheckedSOE.Pd0241c57d846289ad91922c97dce251b6632ae492fa8723ebd7cf12b560dcb6a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2c7277f7086b54773e0d9279f65c7d012e89e20292fae22d35b2f7d9f5e280f6
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2c7277f7086b54773e0d9279f65c7d012e89e20292fae22d35b2f7d9f5e280f6; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2c7277f7086b54773e0d9279f65c7d012e89e20292fae22d35b2f7d9f5e280f6

namespace PerfectPower.SOEModelPackets
def obs144 := PerfectPower.CheckedSOE.P2c7277f7086b54773e0d9279f65c7d012e89e20292fae22d35b2f7d9f5e280f6.obs
def step144 := PerfectPower.CheckedSOE.P2c7277f7086b54773e0d9279f65c7d012e89e20292fae22d35b2f7d9f5e280f6.step
def q144 := PerfectPower.CheckedSOE.P2c7277f7086b54773e0d9279f65c7d012e89e20292fae22d35b2f7d9f5e280f6.q
def out144 := PerfectPower.CheckedSOE.P2c7277f7086b54773e0d9279f65c7d012e89e20292fae22d35b2f7d9f5e280f6.out
def target144 := PerfectPower.CheckedSOE.P2c7277f7086b54773e0d9279f65c7d012e89e20292fae22d35b2f7d9f5e280f6.target
theorem complete144 (s t : Fin 2) : SOESemantics.Equivalent step144 obs144 s t ↔ q144 s = q144 t := PerfectPower.CheckedSOE.P2c7277f7086b54773e0d9279f65c7d012e89e20292fae22d35b2f7d9f5e280f6.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbdafc2354bafb308cdfae36eb2fd6c61fc58a9e1823f51647840fe070d9452ea
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: bdafc2354bafb308cdfae36eb2fd6c61fc58a9e1823f51647840fe070d9452ea; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbdafc2354bafb308cdfae36eb2fd6c61fc58a9e1823f51647840fe070d9452ea

namespace PerfectPower.SOEModelPackets
def obs145 := PerfectPower.CheckedSOE.Pbdafc2354bafb308cdfae36eb2fd6c61fc58a9e1823f51647840fe070d9452ea.obs
def step145 := PerfectPower.CheckedSOE.Pbdafc2354bafb308cdfae36eb2fd6c61fc58a9e1823f51647840fe070d9452ea.step
def q145 := PerfectPower.CheckedSOE.Pbdafc2354bafb308cdfae36eb2fd6c61fc58a9e1823f51647840fe070d9452ea.q
def out145 := PerfectPower.CheckedSOE.Pbdafc2354bafb308cdfae36eb2fd6c61fc58a9e1823f51647840fe070d9452ea.out
def target145 := PerfectPower.CheckedSOE.Pbdafc2354bafb308cdfae36eb2fd6c61fc58a9e1823f51647840fe070d9452ea.target
theorem complete145 (s t : Fin 2) : SOESemantics.Equivalent step145 obs145 s t ↔ q145 s = q145 t := PerfectPower.CheckedSOE.Pbdafc2354bafb308cdfae36eb2fd6c61fc58a9e1823f51647840fe070d9452ea.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2acf01dc1328ffbda2aacc9f522e60cc4a0f47f25871d52d6cedfc725b099c5e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2acf01dc1328ffbda2aacc9f522e60cc4a0f47f25871d52d6cedfc725b099c5e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2acf01dc1328ffbda2aacc9f522e60cc4a0f47f25871d52d6cedfc725b099c5e

namespace PerfectPower.SOEModelPackets
def obs146 := PerfectPower.CheckedSOE.P2acf01dc1328ffbda2aacc9f522e60cc4a0f47f25871d52d6cedfc725b099c5e.obs
def step146 := PerfectPower.CheckedSOE.P2acf01dc1328ffbda2aacc9f522e60cc4a0f47f25871d52d6cedfc725b099c5e.step
def q146 := PerfectPower.CheckedSOE.P2acf01dc1328ffbda2aacc9f522e60cc4a0f47f25871d52d6cedfc725b099c5e.q
def out146 := PerfectPower.CheckedSOE.P2acf01dc1328ffbda2aacc9f522e60cc4a0f47f25871d52d6cedfc725b099c5e.out
def target146 := PerfectPower.CheckedSOE.P2acf01dc1328ffbda2aacc9f522e60cc4a0f47f25871d52d6cedfc725b099c5e.target
theorem complete146 (s t : Fin 2) : SOESemantics.Equivalent step146 obs146 s t ↔ q146 s = q146 t := PerfectPower.CheckedSOE.P2acf01dc1328ffbda2aacc9f522e60cc4a0f47f25871d52d6cedfc725b099c5e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P60d313b7fe81ed8909828e41c121602097a69ad6ee0b2f2ac7f0071496be562c
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 60d313b7fe81ed8909828e41c121602097a69ad6ee0b2f2ac7f0071496be562c; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P60d313b7fe81ed8909828e41c121602097a69ad6ee0b2f2ac7f0071496be562c

namespace PerfectPower.SOEModelPackets
def obs147 := PerfectPower.CheckedSOE.P60d313b7fe81ed8909828e41c121602097a69ad6ee0b2f2ac7f0071496be562c.obs
def step147 := PerfectPower.CheckedSOE.P60d313b7fe81ed8909828e41c121602097a69ad6ee0b2f2ac7f0071496be562c.step
def q147 := PerfectPower.CheckedSOE.P60d313b7fe81ed8909828e41c121602097a69ad6ee0b2f2ac7f0071496be562c.q
def out147 := PerfectPower.CheckedSOE.P60d313b7fe81ed8909828e41c121602097a69ad6ee0b2f2ac7f0071496be562c.out
def target147 := PerfectPower.CheckedSOE.P60d313b7fe81ed8909828e41c121602097a69ad6ee0b2f2ac7f0071496be562c.target
theorem complete147 (s t : Fin 2) : SOESemantics.Equivalent step147 obs147 s t ↔ q147 s = q147 t := PerfectPower.CheckedSOE.P60d313b7fe81ed8909828e41c121602097a69ad6ee0b2f2ac7f0071496be562c.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa3fc6a39bf495e4596a20486e3bf5300f0eba22c5a811900519214b3ed62e9ac
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a3fc6a39bf495e4596a20486e3bf5300f0eba22c5a811900519214b3ed62e9ac; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa3fc6a39bf495e4596a20486e3bf5300f0eba22c5a811900519214b3ed62e9ac

namespace PerfectPower.SOEModelPackets
def obs148 := PerfectPower.CheckedSOE.Pa3fc6a39bf495e4596a20486e3bf5300f0eba22c5a811900519214b3ed62e9ac.obs
def step148 := PerfectPower.CheckedSOE.Pa3fc6a39bf495e4596a20486e3bf5300f0eba22c5a811900519214b3ed62e9ac.step
def q148 := PerfectPower.CheckedSOE.Pa3fc6a39bf495e4596a20486e3bf5300f0eba22c5a811900519214b3ed62e9ac.q
def out148 := PerfectPower.CheckedSOE.Pa3fc6a39bf495e4596a20486e3bf5300f0eba22c5a811900519214b3ed62e9ac.out
def target148 := PerfectPower.CheckedSOE.Pa3fc6a39bf495e4596a20486e3bf5300f0eba22c5a811900519214b3ed62e9ac.target
theorem complete148 (s t : Fin 2) : SOESemantics.Equivalent step148 obs148 s t ↔ q148 s = q148 t := PerfectPower.CheckedSOE.Pa3fc6a39bf495e4596a20486e3bf5300f0eba22c5a811900519214b3ed62e9ac.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P3117c57705dc58b7698292eb90a7943a215998a98bd3becbeb1be7f5d25e8353
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3117c57705dc58b7698292eb90a7943a215998a98bd3becbeb1be7f5d25e8353; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P3117c57705dc58b7698292eb90a7943a215998a98bd3becbeb1be7f5d25e8353

namespace PerfectPower.SOEModelPackets
def obs149 := PerfectPower.CheckedSOE.P3117c57705dc58b7698292eb90a7943a215998a98bd3becbeb1be7f5d25e8353.obs
def step149 := PerfectPower.CheckedSOE.P3117c57705dc58b7698292eb90a7943a215998a98bd3becbeb1be7f5d25e8353.step
def q149 := PerfectPower.CheckedSOE.P3117c57705dc58b7698292eb90a7943a215998a98bd3becbeb1be7f5d25e8353.q
def out149 := PerfectPower.CheckedSOE.P3117c57705dc58b7698292eb90a7943a215998a98bd3becbeb1be7f5d25e8353.out
def target149 := PerfectPower.CheckedSOE.P3117c57705dc58b7698292eb90a7943a215998a98bd3becbeb1be7f5d25e8353.target
theorem complete149 (s t : Fin 2) : SOESemantics.Equivalent step149 obs149 s t ↔ q149 s = q149 t := PerfectPower.CheckedSOE.P3117c57705dc58b7698292eb90a7943a215998a98bd3becbeb1be7f5d25e8353.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf4f36e302c94cfee92bdd8b0f0d6046d91cce0914e066d9ee7010ee643909627
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f4f36e302c94cfee92bdd8b0f0d6046d91cce0914e066d9ee7010ee643909627; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf4f36e302c94cfee92bdd8b0f0d6046d91cce0914e066d9ee7010ee643909627

namespace PerfectPower.SOEModelPackets
def obs150 := PerfectPower.CheckedSOE.Pf4f36e302c94cfee92bdd8b0f0d6046d91cce0914e066d9ee7010ee643909627.obs
def step150 := PerfectPower.CheckedSOE.Pf4f36e302c94cfee92bdd8b0f0d6046d91cce0914e066d9ee7010ee643909627.step
def q150 := PerfectPower.CheckedSOE.Pf4f36e302c94cfee92bdd8b0f0d6046d91cce0914e066d9ee7010ee643909627.q
def out150 := PerfectPower.CheckedSOE.Pf4f36e302c94cfee92bdd8b0f0d6046d91cce0914e066d9ee7010ee643909627.out
def target150 := PerfectPower.CheckedSOE.Pf4f36e302c94cfee92bdd8b0f0d6046d91cce0914e066d9ee7010ee643909627.target
theorem complete150 (s t : Fin 2) : SOESemantics.Equivalent step150 obs150 s t ↔ q150 s = q150 t := PerfectPower.CheckedSOE.Pf4f36e302c94cfee92bdd8b0f0d6046d91cce0914e066d9ee7010ee643909627.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc21436683f25d2a65dec1c1697eada5252191527d0cba974a847da0b29bde073
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c21436683f25d2a65dec1c1697eada5252191527d0cba974a847da0b29bde073; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc21436683f25d2a65dec1c1697eada5252191527d0cba974a847da0b29bde073

namespace PerfectPower.SOEModelPackets
def obs151 := PerfectPower.CheckedSOE.Pc21436683f25d2a65dec1c1697eada5252191527d0cba974a847da0b29bde073.obs
def step151 := PerfectPower.CheckedSOE.Pc21436683f25d2a65dec1c1697eada5252191527d0cba974a847da0b29bde073.step
def q151 := PerfectPower.CheckedSOE.Pc21436683f25d2a65dec1c1697eada5252191527d0cba974a847da0b29bde073.q
def out151 := PerfectPower.CheckedSOE.Pc21436683f25d2a65dec1c1697eada5252191527d0cba974a847da0b29bde073.out
def target151 := PerfectPower.CheckedSOE.Pc21436683f25d2a65dec1c1697eada5252191527d0cba974a847da0b29bde073.target
theorem complete151 (s t : Fin 2) : SOESemantics.Equivalent step151 obs151 s t ↔ q151 s = q151 t := PerfectPower.CheckedSOE.Pc21436683f25d2a65dec1c1697eada5252191527d0cba974a847da0b29bde073.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6e4c393bcf15edd4ddeae5bc6d30caa6ef54155214c9c6783dac9a09a63269f7
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6e4c393bcf15edd4ddeae5bc6d30caa6ef54155214c9c6783dac9a09a63269f7; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6e4c393bcf15edd4ddeae5bc6d30caa6ef54155214c9c6783dac9a09a63269f7

namespace PerfectPower.SOEModelPackets
def obs152 := PerfectPower.CheckedSOE.P6e4c393bcf15edd4ddeae5bc6d30caa6ef54155214c9c6783dac9a09a63269f7.obs
def step152 := PerfectPower.CheckedSOE.P6e4c393bcf15edd4ddeae5bc6d30caa6ef54155214c9c6783dac9a09a63269f7.step
def q152 := PerfectPower.CheckedSOE.P6e4c393bcf15edd4ddeae5bc6d30caa6ef54155214c9c6783dac9a09a63269f7.q
def out152 := PerfectPower.CheckedSOE.P6e4c393bcf15edd4ddeae5bc6d30caa6ef54155214c9c6783dac9a09a63269f7.out
def target152 := PerfectPower.CheckedSOE.P6e4c393bcf15edd4ddeae5bc6d30caa6ef54155214c9c6783dac9a09a63269f7.target
theorem complete152 (s t : Fin 2) : SOESemantics.Equivalent step152 obs152 s t ↔ q152 s = q152 t := PerfectPower.CheckedSOE.P6e4c393bcf15edd4ddeae5bc6d30caa6ef54155214c9c6783dac9a09a63269f7.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe24962fdaf34d64920db3c6126a165881638dc26c4f607c111e3f10bd42f91b7
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e24962fdaf34d64920db3c6126a165881638dc26c4f607c111e3f10bd42f91b7; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe24962fdaf34d64920db3c6126a165881638dc26c4f607c111e3f10bd42f91b7

namespace PerfectPower.SOEModelPackets
def obs153 := PerfectPower.CheckedSOE.Pe24962fdaf34d64920db3c6126a165881638dc26c4f607c111e3f10bd42f91b7.obs
def step153 := PerfectPower.CheckedSOE.Pe24962fdaf34d64920db3c6126a165881638dc26c4f607c111e3f10bd42f91b7.step
def q153 := PerfectPower.CheckedSOE.Pe24962fdaf34d64920db3c6126a165881638dc26c4f607c111e3f10bd42f91b7.q
def out153 := PerfectPower.CheckedSOE.Pe24962fdaf34d64920db3c6126a165881638dc26c4f607c111e3f10bd42f91b7.out
def target153 := PerfectPower.CheckedSOE.Pe24962fdaf34d64920db3c6126a165881638dc26c4f607c111e3f10bd42f91b7.target
theorem complete153 (s t : Fin 2) : SOESemantics.Equivalent step153 obs153 s t ↔ q153 s = q153 t := PerfectPower.CheckedSOE.Pe24962fdaf34d64920db3c6126a165881638dc26c4f607c111e3f10bd42f91b7.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P7057729d72890b087e93a2e1b8a7aff068c56cb6f88bf8def9481c841c80f783
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 7057729d72890b087e93a2e1b8a7aff068c56cb6f88bf8def9481c841c80f783; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P7057729d72890b087e93a2e1b8a7aff068c56cb6f88bf8def9481c841c80f783

namespace PerfectPower.SOEModelPackets
def obs154 := PerfectPower.CheckedSOE.P7057729d72890b087e93a2e1b8a7aff068c56cb6f88bf8def9481c841c80f783.obs
def step154 := PerfectPower.CheckedSOE.P7057729d72890b087e93a2e1b8a7aff068c56cb6f88bf8def9481c841c80f783.step
def q154 := PerfectPower.CheckedSOE.P7057729d72890b087e93a2e1b8a7aff068c56cb6f88bf8def9481c841c80f783.q
def out154 := PerfectPower.CheckedSOE.P7057729d72890b087e93a2e1b8a7aff068c56cb6f88bf8def9481c841c80f783.out
def target154 := PerfectPower.CheckedSOE.P7057729d72890b087e93a2e1b8a7aff068c56cb6f88bf8def9481c841c80f783.target
theorem complete154 (s t : Fin 2) : SOESemantics.Equivalent step154 obs154 s t ↔ q154 s = q154 t := PerfectPower.CheckedSOE.P7057729d72890b087e93a2e1b8a7aff068c56cb6f88bf8def9481c841c80f783.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd50b02f6763a3f75d122a2bb5ec2740eee71af011afa5841b805e4fad9f39994
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d50b02f6763a3f75d122a2bb5ec2740eee71af011afa5841b805e4fad9f39994; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd50b02f6763a3f75d122a2bb5ec2740eee71af011afa5841b805e4fad9f39994

namespace PerfectPower.SOEModelPackets
def obs155 := PerfectPower.CheckedSOE.Pd50b02f6763a3f75d122a2bb5ec2740eee71af011afa5841b805e4fad9f39994.obs
def step155 := PerfectPower.CheckedSOE.Pd50b02f6763a3f75d122a2bb5ec2740eee71af011afa5841b805e4fad9f39994.step
def q155 := PerfectPower.CheckedSOE.Pd50b02f6763a3f75d122a2bb5ec2740eee71af011afa5841b805e4fad9f39994.q
def out155 := PerfectPower.CheckedSOE.Pd50b02f6763a3f75d122a2bb5ec2740eee71af011afa5841b805e4fad9f39994.out
def target155 := PerfectPower.CheckedSOE.Pd50b02f6763a3f75d122a2bb5ec2740eee71af011afa5841b805e4fad9f39994.target
theorem complete155 (s t : Fin 2) : SOESemantics.Equivalent step155 obs155 s t ↔ q155 s = q155 t := PerfectPower.CheckedSOE.Pd50b02f6763a3f75d122a2bb5ec2740eee71af011afa5841b805e4fad9f39994.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P980ffff21468c0898eb905c3e72bb7856399eba10c5d8b65179be00a15fb3cc1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 980ffff21468c0898eb905c3e72bb7856399eba10c5d8b65179be00a15fb3cc1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P980ffff21468c0898eb905c3e72bb7856399eba10c5d8b65179be00a15fb3cc1

namespace PerfectPower.SOEModelPackets
def obs156 := PerfectPower.CheckedSOE.P980ffff21468c0898eb905c3e72bb7856399eba10c5d8b65179be00a15fb3cc1.obs
def step156 := PerfectPower.CheckedSOE.P980ffff21468c0898eb905c3e72bb7856399eba10c5d8b65179be00a15fb3cc1.step
def q156 := PerfectPower.CheckedSOE.P980ffff21468c0898eb905c3e72bb7856399eba10c5d8b65179be00a15fb3cc1.q
def out156 := PerfectPower.CheckedSOE.P980ffff21468c0898eb905c3e72bb7856399eba10c5d8b65179be00a15fb3cc1.out
def target156 := PerfectPower.CheckedSOE.P980ffff21468c0898eb905c3e72bb7856399eba10c5d8b65179be00a15fb3cc1.target
theorem complete156 (s t : Fin 2) : SOESemantics.Equivalent step156 obs156 s t ↔ q156 s = q156 t := PerfectPower.CheckedSOE.P980ffff21468c0898eb905c3e72bb7856399eba10c5d8b65179be00a15fb3cc1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6c1c5d928cb4e21d0a40db6f4fb72b0bfbedc9a0e03334a41707ad7f8f2ef468
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6c1c5d928cb4e21d0a40db6f4fb72b0bfbedc9a0e03334a41707ad7f8f2ef468; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6c1c5d928cb4e21d0a40db6f4fb72b0bfbedc9a0e03334a41707ad7f8f2ef468

namespace PerfectPower.SOEModelPackets
def obs157 := PerfectPower.CheckedSOE.P6c1c5d928cb4e21d0a40db6f4fb72b0bfbedc9a0e03334a41707ad7f8f2ef468.obs
def step157 := PerfectPower.CheckedSOE.P6c1c5d928cb4e21d0a40db6f4fb72b0bfbedc9a0e03334a41707ad7f8f2ef468.step
def q157 := PerfectPower.CheckedSOE.P6c1c5d928cb4e21d0a40db6f4fb72b0bfbedc9a0e03334a41707ad7f8f2ef468.q
def out157 := PerfectPower.CheckedSOE.P6c1c5d928cb4e21d0a40db6f4fb72b0bfbedc9a0e03334a41707ad7f8f2ef468.out
def target157 := PerfectPower.CheckedSOE.P6c1c5d928cb4e21d0a40db6f4fb72b0bfbedc9a0e03334a41707ad7f8f2ef468.target
theorem complete157 (s t : Fin 2) : SOESemantics.Equivalent step157 obs157 s t ↔ q157 s = q157 t := PerfectPower.CheckedSOE.P6c1c5d928cb4e21d0a40db6f4fb72b0bfbedc9a0e03334a41707ad7f8f2ef468.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P42efb6c0b14291bde016d9cb3ea1b6f0faed939844ebfcdbccdf1b1e4391b911
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 42efb6c0b14291bde016d9cb3ea1b6f0faed939844ebfcdbccdf1b1e4391b911; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P42efb6c0b14291bde016d9cb3ea1b6f0faed939844ebfcdbccdf1b1e4391b911

namespace PerfectPower.SOEModelPackets
def obs158 := PerfectPower.CheckedSOE.P42efb6c0b14291bde016d9cb3ea1b6f0faed939844ebfcdbccdf1b1e4391b911.obs
def step158 := PerfectPower.CheckedSOE.P42efb6c0b14291bde016d9cb3ea1b6f0faed939844ebfcdbccdf1b1e4391b911.step
def q158 := PerfectPower.CheckedSOE.P42efb6c0b14291bde016d9cb3ea1b6f0faed939844ebfcdbccdf1b1e4391b911.q
def out158 := PerfectPower.CheckedSOE.P42efb6c0b14291bde016d9cb3ea1b6f0faed939844ebfcdbccdf1b1e4391b911.out
def target158 := PerfectPower.CheckedSOE.P42efb6c0b14291bde016d9cb3ea1b6f0faed939844ebfcdbccdf1b1e4391b911.target
theorem complete158 (s t : Fin 2) : SOESemantics.Equivalent step158 obs158 s t ↔ q158 s = q158 t := PerfectPower.CheckedSOE.P42efb6c0b14291bde016d9cb3ea1b6f0faed939844ebfcdbccdf1b1e4391b911.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2e6f322ba69d5d8b4e12914a1de782ec2511fedd2ca3915724589043a2a78ada
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2e6f322ba69d5d8b4e12914a1de782ec2511fedd2ca3915724589043a2a78ada; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2e6f322ba69d5d8b4e12914a1de782ec2511fedd2ca3915724589043a2a78ada

namespace PerfectPower.SOEModelPackets
def obs159 := PerfectPower.CheckedSOE.P2e6f322ba69d5d8b4e12914a1de782ec2511fedd2ca3915724589043a2a78ada.obs
def step159 := PerfectPower.CheckedSOE.P2e6f322ba69d5d8b4e12914a1de782ec2511fedd2ca3915724589043a2a78ada.step
def q159 := PerfectPower.CheckedSOE.P2e6f322ba69d5d8b4e12914a1de782ec2511fedd2ca3915724589043a2a78ada.q
def out159 := PerfectPower.CheckedSOE.P2e6f322ba69d5d8b4e12914a1de782ec2511fedd2ca3915724589043a2a78ada.out
def target159 := PerfectPower.CheckedSOE.P2e6f322ba69d5d8b4e12914a1de782ec2511fedd2ca3915724589043a2a78ada.target
theorem complete159 (s t : Fin 2) : SOESemantics.Equivalent step159 obs159 s t ↔ q159 s = q159 t := PerfectPower.CheckedSOE.P2e6f322ba69d5d8b4e12914a1de782ec2511fedd2ca3915724589043a2a78ada.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2f439bec5aee33beccd19a9316bdfe0b3f73882112dbe4d60ae359b77e17b531
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2f439bec5aee33beccd19a9316bdfe0b3f73882112dbe4d60ae359b77e17b531; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2f439bec5aee33beccd19a9316bdfe0b3f73882112dbe4d60ae359b77e17b531

namespace PerfectPower.SOEModelPackets
def obs160 := PerfectPower.CheckedSOE.P2f439bec5aee33beccd19a9316bdfe0b3f73882112dbe4d60ae359b77e17b531.obs
def step160 := PerfectPower.CheckedSOE.P2f439bec5aee33beccd19a9316bdfe0b3f73882112dbe4d60ae359b77e17b531.step
def q160 := PerfectPower.CheckedSOE.P2f439bec5aee33beccd19a9316bdfe0b3f73882112dbe4d60ae359b77e17b531.q
def out160 := PerfectPower.CheckedSOE.P2f439bec5aee33beccd19a9316bdfe0b3f73882112dbe4d60ae359b77e17b531.out
def target160 := PerfectPower.CheckedSOE.P2f439bec5aee33beccd19a9316bdfe0b3f73882112dbe4d60ae359b77e17b531.target
theorem complete160 (s t : Fin 2) : SOESemantics.Equivalent step160 obs160 s t ↔ q160 s = q160 t := PerfectPower.CheckedSOE.P2f439bec5aee33beccd19a9316bdfe0b3f73882112dbe4d60ae359b77e17b531.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6f6b6fa025fa4cb0382ede4e693796c021aa5969da5647fc9b5e39ba39cf761b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6f6b6fa025fa4cb0382ede4e693796c021aa5969da5647fc9b5e39ba39cf761b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6f6b6fa025fa4cb0382ede4e693796c021aa5969da5647fc9b5e39ba39cf761b

namespace PerfectPower.SOEModelPackets
def obs161 := PerfectPower.CheckedSOE.P6f6b6fa025fa4cb0382ede4e693796c021aa5969da5647fc9b5e39ba39cf761b.obs
def step161 := PerfectPower.CheckedSOE.P6f6b6fa025fa4cb0382ede4e693796c021aa5969da5647fc9b5e39ba39cf761b.step
def q161 := PerfectPower.CheckedSOE.P6f6b6fa025fa4cb0382ede4e693796c021aa5969da5647fc9b5e39ba39cf761b.q
def out161 := PerfectPower.CheckedSOE.P6f6b6fa025fa4cb0382ede4e693796c021aa5969da5647fc9b5e39ba39cf761b.out
def target161 := PerfectPower.CheckedSOE.P6f6b6fa025fa4cb0382ede4e693796c021aa5969da5647fc9b5e39ba39cf761b.target
theorem complete161 (s t : Fin 2) : SOESemantics.Equivalent step161 obs161 s t ↔ q161 s = q161 t := PerfectPower.CheckedSOE.P6f6b6fa025fa4cb0382ede4e693796c021aa5969da5647fc9b5e39ba39cf761b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P59ccd7fbee335cfd144a8b804911232d71691ad0dc9277467b617b41563150ee
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 59ccd7fbee335cfd144a8b804911232d71691ad0dc9277467b617b41563150ee; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P59ccd7fbee335cfd144a8b804911232d71691ad0dc9277467b617b41563150ee

namespace PerfectPower.SOEModelPackets
def obs162 := PerfectPower.CheckedSOE.P59ccd7fbee335cfd144a8b804911232d71691ad0dc9277467b617b41563150ee.obs
def step162 := PerfectPower.CheckedSOE.P59ccd7fbee335cfd144a8b804911232d71691ad0dc9277467b617b41563150ee.step
def q162 := PerfectPower.CheckedSOE.P59ccd7fbee335cfd144a8b804911232d71691ad0dc9277467b617b41563150ee.q
def out162 := PerfectPower.CheckedSOE.P59ccd7fbee335cfd144a8b804911232d71691ad0dc9277467b617b41563150ee.out
def target162 := PerfectPower.CheckedSOE.P59ccd7fbee335cfd144a8b804911232d71691ad0dc9277467b617b41563150ee.target
theorem complete162 (s t : Fin 2) : SOESemantics.Equivalent step162 obs162 s t ↔ q162 s = q162 t := PerfectPower.CheckedSOE.P59ccd7fbee335cfd144a8b804911232d71691ad0dc9277467b617b41563150ee.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4f3e00d8566fde5339415ec8103eb73c2e562ec3ec28c8442bd544523594e300
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4f3e00d8566fde5339415ec8103eb73c2e562ec3ec28c8442bd544523594e300; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4f3e00d8566fde5339415ec8103eb73c2e562ec3ec28c8442bd544523594e300

namespace PerfectPower.SOEModelPackets
def obs163 := PerfectPower.CheckedSOE.P4f3e00d8566fde5339415ec8103eb73c2e562ec3ec28c8442bd544523594e300.obs
def step163 := PerfectPower.CheckedSOE.P4f3e00d8566fde5339415ec8103eb73c2e562ec3ec28c8442bd544523594e300.step
def q163 := PerfectPower.CheckedSOE.P4f3e00d8566fde5339415ec8103eb73c2e562ec3ec28c8442bd544523594e300.q
def out163 := PerfectPower.CheckedSOE.P4f3e00d8566fde5339415ec8103eb73c2e562ec3ec28c8442bd544523594e300.out
def target163 := PerfectPower.CheckedSOE.P4f3e00d8566fde5339415ec8103eb73c2e562ec3ec28c8442bd544523594e300.target
theorem complete163 (s t : Fin 2) : SOESemantics.Equivalent step163 obs163 s t ↔ q163 s = q163 t := PerfectPower.CheckedSOE.P4f3e00d8566fde5339415ec8103eb73c2e562ec3ec28c8442bd544523594e300.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pded693c7dd0889b7cfb86ae0c80663b7bfe30da35df98814f429952374c0730a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ded693c7dd0889b7cfb86ae0c80663b7bfe30da35df98814f429952374c0730a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pded693c7dd0889b7cfb86ae0c80663b7bfe30da35df98814f429952374c0730a

namespace PerfectPower.SOEModelPackets
def obs164 := PerfectPower.CheckedSOE.Pded693c7dd0889b7cfb86ae0c80663b7bfe30da35df98814f429952374c0730a.obs
def step164 := PerfectPower.CheckedSOE.Pded693c7dd0889b7cfb86ae0c80663b7bfe30da35df98814f429952374c0730a.step
def q164 := PerfectPower.CheckedSOE.Pded693c7dd0889b7cfb86ae0c80663b7bfe30da35df98814f429952374c0730a.q
def out164 := PerfectPower.CheckedSOE.Pded693c7dd0889b7cfb86ae0c80663b7bfe30da35df98814f429952374c0730a.out
def target164 := PerfectPower.CheckedSOE.Pded693c7dd0889b7cfb86ae0c80663b7bfe30da35df98814f429952374c0730a.target
theorem complete164 (s t : Fin 2) : SOESemantics.Equivalent step164 obs164 s t ↔ q164 s = q164 t := PerfectPower.CheckedSOE.Pded693c7dd0889b7cfb86ae0c80663b7bfe30da35df98814f429952374c0730a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe7acaa4ec2c3c03d3da5e945bd00cba730bec78b7d1a5326ac6dd27a0f6047c0
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e7acaa4ec2c3c03d3da5e945bd00cba730bec78b7d1a5326ac6dd27a0f6047c0; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe7acaa4ec2c3c03d3da5e945bd00cba730bec78b7d1a5326ac6dd27a0f6047c0

namespace PerfectPower.SOEModelPackets
def obs165 := PerfectPower.CheckedSOE.Pe7acaa4ec2c3c03d3da5e945bd00cba730bec78b7d1a5326ac6dd27a0f6047c0.obs
def step165 := PerfectPower.CheckedSOE.Pe7acaa4ec2c3c03d3da5e945bd00cba730bec78b7d1a5326ac6dd27a0f6047c0.step
def q165 := PerfectPower.CheckedSOE.Pe7acaa4ec2c3c03d3da5e945bd00cba730bec78b7d1a5326ac6dd27a0f6047c0.q
def out165 := PerfectPower.CheckedSOE.Pe7acaa4ec2c3c03d3da5e945bd00cba730bec78b7d1a5326ac6dd27a0f6047c0.out
def target165 := PerfectPower.CheckedSOE.Pe7acaa4ec2c3c03d3da5e945bd00cba730bec78b7d1a5326ac6dd27a0f6047c0.target
theorem complete165 (s t : Fin 2) : SOESemantics.Equivalent step165 obs165 s t ↔ q165 s = q165 t := PerfectPower.CheckedSOE.Pe7acaa4ec2c3c03d3da5e945bd00cba730bec78b7d1a5326ac6dd27a0f6047c0.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P3202d5764d75936e77fb9c866c1929d625d713c7e0b9167a490a0b613ebf868b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3202d5764d75936e77fb9c866c1929d625d713c7e0b9167a490a0b613ebf868b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P3202d5764d75936e77fb9c866c1929d625d713c7e0b9167a490a0b613ebf868b

namespace PerfectPower.SOEModelPackets
def obs166 := PerfectPower.CheckedSOE.P3202d5764d75936e77fb9c866c1929d625d713c7e0b9167a490a0b613ebf868b.obs
def step166 := PerfectPower.CheckedSOE.P3202d5764d75936e77fb9c866c1929d625d713c7e0b9167a490a0b613ebf868b.step
def q166 := PerfectPower.CheckedSOE.P3202d5764d75936e77fb9c866c1929d625d713c7e0b9167a490a0b613ebf868b.q
def out166 := PerfectPower.CheckedSOE.P3202d5764d75936e77fb9c866c1929d625d713c7e0b9167a490a0b613ebf868b.out
def target166 := PerfectPower.CheckedSOE.P3202d5764d75936e77fb9c866c1929d625d713c7e0b9167a490a0b613ebf868b.target
theorem complete166 (s t : Fin 2) : SOESemantics.Equivalent step166 obs166 s t ↔ q166 s = q166 t := PerfectPower.CheckedSOE.P3202d5764d75936e77fb9c866c1929d625d713c7e0b9167a490a0b613ebf868b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P108aa5c08e39f6462d89f2011db727efd00ff660e0af7da646bb7aa9894590dd
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 108aa5c08e39f6462d89f2011db727efd00ff660e0af7da646bb7aa9894590dd; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P108aa5c08e39f6462d89f2011db727efd00ff660e0af7da646bb7aa9894590dd

namespace PerfectPower.SOEModelPackets
def obs167 := PerfectPower.CheckedSOE.P108aa5c08e39f6462d89f2011db727efd00ff660e0af7da646bb7aa9894590dd.obs
def step167 := PerfectPower.CheckedSOE.P108aa5c08e39f6462d89f2011db727efd00ff660e0af7da646bb7aa9894590dd.step
def q167 := PerfectPower.CheckedSOE.P108aa5c08e39f6462d89f2011db727efd00ff660e0af7da646bb7aa9894590dd.q
def out167 := PerfectPower.CheckedSOE.P108aa5c08e39f6462d89f2011db727efd00ff660e0af7da646bb7aa9894590dd.out
def target167 := PerfectPower.CheckedSOE.P108aa5c08e39f6462d89f2011db727efd00ff660e0af7da646bb7aa9894590dd.target
theorem complete167 (s t : Fin 2) : SOESemantics.Equivalent step167 obs167 s t ↔ q167 s = q167 t := PerfectPower.CheckedSOE.P108aa5c08e39f6462d89f2011db727efd00ff660e0af7da646bb7aa9894590dd.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4146488599c8ffbb09e6f886224c8a797920c930fe84ad83536907fe413c4186
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4146488599c8ffbb09e6f886224c8a797920c930fe84ad83536907fe413c4186; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4146488599c8ffbb09e6f886224c8a797920c930fe84ad83536907fe413c4186

namespace PerfectPower.SOEModelPackets
def obs168 := PerfectPower.CheckedSOE.P4146488599c8ffbb09e6f886224c8a797920c930fe84ad83536907fe413c4186.obs
def step168 := PerfectPower.CheckedSOE.P4146488599c8ffbb09e6f886224c8a797920c930fe84ad83536907fe413c4186.step
def q168 := PerfectPower.CheckedSOE.P4146488599c8ffbb09e6f886224c8a797920c930fe84ad83536907fe413c4186.q
def out168 := PerfectPower.CheckedSOE.P4146488599c8ffbb09e6f886224c8a797920c930fe84ad83536907fe413c4186.out
def target168 := PerfectPower.CheckedSOE.P4146488599c8ffbb09e6f886224c8a797920c930fe84ad83536907fe413c4186.target
theorem complete168 (s t : Fin 2) : SOESemantics.Equivalent step168 obs168 s t ↔ q168 s = q168 t := PerfectPower.CheckedSOE.P4146488599c8ffbb09e6f886224c8a797920c930fe84ad83536907fe413c4186.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P565cb4bb7a0bd9e50f47d35209957f0e92ba95ff87f3493f1c121a9574350b93
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 565cb4bb7a0bd9e50f47d35209957f0e92ba95ff87f3493f1c121a9574350b93; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P565cb4bb7a0bd9e50f47d35209957f0e92ba95ff87f3493f1c121a9574350b93

namespace PerfectPower.SOEModelPackets
def obs169 := PerfectPower.CheckedSOE.P565cb4bb7a0bd9e50f47d35209957f0e92ba95ff87f3493f1c121a9574350b93.obs
def step169 := PerfectPower.CheckedSOE.P565cb4bb7a0bd9e50f47d35209957f0e92ba95ff87f3493f1c121a9574350b93.step
def q169 := PerfectPower.CheckedSOE.P565cb4bb7a0bd9e50f47d35209957f0e92ba95ff87f3493f1c121a9574350b93.q
def out169 := PerfectPower.CheckedSOE.P565cb4bb7a0bd9e50f47d35209957f0e92ba95ff87f3493f1c121a9574350b93.out
def target169 := PerfectPower.CheckedSOE.P565cb4bb7a0bd9e50f47d35209957f0e92ba95ff87f3493f1c121a9574350b93.target
theorem complete169 (s t : Fin 2) : SOESemantics.Equivalent step169 obs169 s t ↔ q169 s = q169 t := PerfectPower.CheckedSOE.P565cb4bb7a0bd9e50f47d35209957f0e92ba95ff87f3493f1c121a9574350b93.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P400705ec2501cea0b8b72dbc6696e34a5a2a052c31b5a9f007c0b34df9b82a61
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 400705ec2501cea0b8b72dbc6696e34a5a2a052c31b5a9f007c0b34df9b82a61; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P400705ec2501cea0b8b72dbc6696e34a5a2a052c31b5a9f007c0b34df9b82a61

namespace PerfectPower.SOEModelPackets
def obs170 := PerfectPower.CheckedSOE.P400705ec2501cea0b8b72dbc6696e34a5a2a052c31b5a9f007c0b34df9b82a61.obs
def step170 := PerfectPower.CheckedSOE.P400705ec2501cea0b8b72dbc6696e34a5a2a052c31b5a9f007c0b34df9b82a61.step
def q170 := PerfectPower.CheckedSOE.P400705ec2501cea0b8b72dbc6696e34a5a2a052c31b5a9f007c0b34df9b82a61.q
def out170 := PerfectPower.CheckedSOE.P400705ec2501cea0b8b72dbc6696e34a5a2a052c31b5a9f007c0b34df9b82a61.out
def target170 := PerfectPower.CheckedSOE.P400705ec2501cea0b8b72dbc6696e34a5a2a052c31b5a9f007c0b34df9b82a61.target
theorem complete170 (s t : Fin 2) : SOESemantics.Equivalent step170 obs170 s t ↔ q170 s = q170 t := PerfectPower.CheckedSOE.P400705ec2501cea0b8b72dbc6696e34a5a2a052c31b5a9f007c0b34df9b82a61.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0537a99a884e61176d61a9fd606535f75c80e864ac928da0ed3b7d51e78519b7
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0537a99a884e61176d61a9fd606535f75c80e864ac928da0ed3b7d51e78519b7; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0537a99a884e61176d61a9fd606535f75c80e864ac928da0ed3b7d51e78519b7

namespace PerfectPower.SOEModelPackets
def obs171 := PerfectPower.CheckedSOE.P0537a99a884e61176d61a9fd606535f75c80e864ac928da0ed3b7d51e78519b7.obs
def step171 := PerfectPower.CheckedSOE.P0537a99a884e61176d61a9fd606535f75c80e864ac928da0ed3b7d51e78519b7.step
def q171 := PerfectPower.CheckedSOE.P0537a99a884e61176d61a9fd606535f75c80e864ac928da0ed3b7d51e78519b7.q
def out171 := PerfectPower.CheckedSOE.P0537a99a884e61176d61a9fd606535f75c80e864ac928da0ed3b7d51e78519b7.out
def target171 := PerfectPower.CheckedSOE.P0537a99a884e61176d61a9fd606535f75c80e864ac928da0ed3b7d51e78519b7.target
theorem complete171 (s t : Fin 2) : SOESemantics.Equivalent step171 obs171 s t ↔ q171 s = q171 t := PerfectPower.CheckedSOE.P0537a99a884e61176d61a9fd606535f75c80e864ac928da0ed3b7d51e78519b7.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P3b8e29d3420bfc3a94169b087c86f09749b82af02137ed57969fa912ce007683
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3b8e29d3420bfc3a94169b087c86f09749b82af02137ed57969fa912ce007683; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P3b8e29d3420bfc3a94169b087c86f09749b82af02137ed57969fa912ce007683

namespace PerfectPower.SOEModelPackets
def obs172 := PerfectPower.CheckedSOE.P3b8e29d3420bfc3a94169b087c86f09749b82af02137ed57969fa912ce007683.obs
def step172 := PerfectPower.CheckedSOE.P3b8e29d3420bfc3a94169b087c86f09749b82af02137ed57969fa912ce007683.step
def q172 := PerfectPower.CheckedSOE.P3b8e29d3420bfc3a94169b087c86f09749b82af02137ed57969fa912ce007683.q
def out172 := PerfectPower.CheckedSOE.P3b8e29d3420bfc3a94169b087c86f09749b82af02137ed57969fa912ce007683.out
def target172 := PerfectPower.CheckedSOE.P3b8e29d3420bfc3a94169b087c86f09749b82af02137ed57969fa912ce007683.target
theorem complete172 (s t : Fin 2) : SOESemantics.Equivalent step172 obs172 s t ↔ q172 s = q172 t := PerfectPower.CheckedSOE.P3b8e29d3420bfc3a94169b087c86f09749b82af02137ed57969fa912ce007683.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf41b1881a7a3bb43edb5e6adb53629858286a971eacda3e7264e233e506f92ab
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f41b1881a7a3bb43edb5e6adb53629858286a971eacda3e7264e233e506f92ab; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf41b1881a7a3bb43edb5e6adb53629858286a971eacda3e7264e233e506f92ab

namespace PerfectPower.SOEModelPackets
def obs173 := PerfectPower.CheckedSOE.Pf41b1881a7a3bb43edb5e6adb53629858286a971eacda3e7264e233e506f92ab.obs
def step173 := PerfectPower.CheckedSOE.Pf41b1881a7a3bb43edb5e6adb53629858286a971eacda3e7264e233e506f92ab.step
def q173 := PerfectPower.CheckedSOE.Pf41b1881a7a3bb43edb5e6adb53629858286a971eacda3e7264e233e506f92ab.q
def out173 := PerfectPower.CheckedSOE.Pf41b1881a7a3bb43edb5e6adb53629858286a971eacda3e7264e233e506f92ab.out
def target173 := PerfectPower.CheckedSOE.Pf41b1881a7a3bb43edb5e6adb53629858286a971eacda3e7264e233e506f92ab.target
theorem complete173 (s t : Fin 2) : SOESemantics.Equivalent step173 obs173 s t ↔ q173 s = q173 t := PerfectPower.CheckedSOE.Pf41b1881a7a3bb43edb5e6adb53629858286a971eacda3e7264e233e506f92ab.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe3de7072fca5cb8b185204da5447a6b3318024b9062abd90a6277a56ac493dae
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e3de7072fca5cb8b185204da5447a6b3318024b9062abd90a6277a56ac493dae; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe3de7072fca5cb8b185204da5447a6b3318024b9062abd90a6277a56ac493dae

namespace PerfectPower.SOEModelPackets
def obs174 := PerfectPower.CheckedSOE.Pe3de7072fca5cb8b185204da5447a6b3318024b9062abd90a6277a56ac493dae.obs
def step174 := PerfectPower.CheckedSOE.Pe3de7072fca5cb8b185204da5447a6b3318024b9062abd90a6277a56ac493dae.step
def q174 := PerfectPower.CheckedSOE.Pe3de7072fca5cb8b185204da5447a6b3318024b9062abd90a6277a56ac493dae.q
def out174 := PerfectPower.CheckedSOE.Pe3de7072fca5cb8b185204da5447a6b3318024b9062abd90a6277a56ac493dae.out
def target174 := PerfectPower.CheckedSOE.Pe3de7072fca5cb8b185204da5447a6b3318024b9062abd90a6277a56ac493dae.target
theorem complete174 (s t : Fin 2) : SOESemantics.Equivalent step174 obs174 s t ↔ q174 s = q174 t := PerfectPower.CheckedSOE.Pe3de7072fca5cb8b185204da5447a6b3318024b9062abd90a6277a56ac493dae.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P54990c7ecefdf78da83c87eda89e4820cff47490b9d1e9870a38cd49941d3436
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 54990c7ecefdf78da83c87eda89e4820cff47490b9d1e9870a38cd49941d3436; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P54990c7ecefdf78da83c87eda89e4820cff47490b9d1e9870a38cd49941d3436

namespace PerfectPower.SOEModelPackets
def obs175 := PerfectPower.CheckedSOE.P54990c7ecefdf78da83c87eda89e4820cff47490b9d1e9870a38cd49941d3436.obs
def step175 := PerfectPower.CheckedSOE.P54990c7ecefdf78da83c87eda89e4820cff47490b9d1e9870a38cd49941d3436.step
def q175 := PerfectPower.CheckedSOE.P54990c7ecefdf78da83c87eda89e4820cff47490b9d1e9870a38cd49941d3436.q
def out175 := PerfectPower.CheckedSOE.P54990c7ecefdf78da83c87eda89e4820cff47490b9d1e9870a38cd49941d3436.out
def target175 := PerfectPower.CheckedSOE.P54990c7ecefdf78da83c87eda89e4820cff47490b9d1e9870a38cd49941d3436.target
theorem complete175 (s t : Fin 2) : SOESemantics.Equivalent step175 obs175 s t ↔ q175 s = q175 t := PerfectPower.CheckedSOE.P54990c7ecefdf78da83c87eda89e4820cff47490b9d1e9870a38cd49941d3436.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa5e234da6d6c4138b66a3be3e8ddf803fff21d6d54e2d3e61c3d3a93b7d86a1e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a5e234da6d6c4138b66a3be3e8ddf803fff21d6d54e2d3e61c3d3a93b7d86a1e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa5e234da6d6c4138b66a3be3e8ddf803fff21d6d54e2d3e61c3d3a93b7d86a1e

namespace PerfectPower.SOEModelPackets
def obs176 := PerfectPower.CheckedSOE.Pa5e234da6d6c4138b66a3be3e8ddf803fff21d6d54e2d3e61c3d3a93b7d86a1e.obs
def step176 := PerfectPower.CheckedSOE.Pa5e234da6d6c4138b66a3be3e8ddf803fff21d6d54e2d3e61c3d3a93b7d86a1e.step
def q176 := PerfectPower.CheckedSOE.Pa5e234da6d6c4138b66a3be3e8ddf803fff21d6d54e2d3e61c3d3a93b7d86a1e.q
def out176 := PerfectPower.CheckedSOE.Pa5e234da6d6c4138b66a3be3e8ddf803fff21d6d54e2d3e61c3d3a93b7d86a1e.out
def target176 := PerfectPower.CheckedSOE.Pa5e234da6d6c4138b66a3be3e8ddf803fff21d6d54e2d3e61c3d3a93b7d86a1e.target
theorem complete176 (s t : Fin 2) : SOESemantics.Equivalent step176 obs176 s t ↔ q176 s = q176 t := PerfectPower.CheckedSOE.Pa5e234da6d6c4138b66a3be3e8ddf803fff21d6d54e2d3e61c3d3a93b7d86a1e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pcd69dc7fafcc5c44fe7f7fb338fdb045f1ef1f1ef02303060fb6721f5faf34e5
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: cd69dc7fafcc5c44fe7f7fb338fdb045f1ef1f1ef02303060fb6721f5faf34e5; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pcd69dc7fafcc5c44fe7f7fb338fdb045f1ef1f1ef02303060fb6721f5faf34e5

namespace PerfectPower.SOEModelPackets
def obs177 := PerfectPower.CheckedSOE.Pcd69dc7fafcc5c44fe7f7fb338fdb045f1ef1f1ef02303060fb6721f5faf34e5.obs
def step177 := PerfectPower.CheckedSOE.Pcd69dc7fafcc5c44fe7f7fb338fdb045f1ef1f1ef02303060fb6721f5faf34e5.step
def q177 := PerfectPower.CheckedSOE.Pcd69dc7fafcc5c44fe7f7fb338fdb045f1ef1f1ef02303060fb6721f5faf34e5.q
def out177 := PerfectPower.CheckedSOE.Pcd69dc7fafcc5c44fe7f7fb338fdb045f1ef1f1ef02303060fb6721f5faf34e5.out
def target177 := PerfectPower.CheckedSOE.Pcd69dc7fafcc5c44fe7f7fb338fdb045f1ef1f1ef02303060fb6721f5faf34e5.target
theorem complete177 (s t : Fin 2) : SOESemantics.Equivalent step177 obs177 s t ↔ q177 s = q177 t := PerfectPower.CheckedSOE.Pcd69dc7fafcc5c44fe7f7fb338fdb045f1ef1f1ef02303060fb6721f5faf34e5.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd7bdb12fe31ed9d4acabe7ebaa3dcbd61c4af6e5a9d56675ef495fc17512319d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d7bdb12fe31ed9d4acabe7ebaa3dcbd61c4af6e5a9d56675ef495fc17512319d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd7bdb12fe31ed9d4acabe7ebaa3dcbd61c4af6e5a9d56675ef495fc17512319d

namespace PerfectPower.SOEModelPackets
def obs178 := PerfectPower.CheckedSOE.Pd7bdb12fe31ed9d4acabe7ebaa3dcbd61c4af6e5a9d56675ef495fc17512319d.obs
def step178 := PerfectPower.CheckedSOE.Pd7bdb12fe31ed9d4acabe7ebaa3dcbd61c4af6e5a9d56675ef495fc17512319d.step
def q178 := PerfectPower.CheckedSOE.Pd7bdb12fe31ed9d4acabe7ebaa3dcbd61c4af6e5a9d56675ef495fc17512319d.q
def out178 := PerfectPower.CheckedSOE.Pd7bdb12fe31ed9d4acabe7ebaa3dcbd61c4af6e5a9d56675ef495fc17512319d.out
def target178 := PerfectPower.CheckedSOE.Pd7bdb12fe31ed9d4acabe7ebaa3dcbd61c4af6e5a9d56675ef495fc17512319d.target
theorem complete178 (s t : Fin 2) : SOESemantics.Equivalent step178 obs178 s t ↔ q178 s = q178 t := PerfectPower.CheckedSOE.Pd7bdb12fe31ed9d4acabe7ebaa3dcbd61c4af6e5a9d56675ef495fc17512319d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb955ff01d7c76c708dbfc9152e363b26c430ccedf71171abf18c69fc25eb4b5c
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b955ff01d7c76c708dbfc9152e363b26c430ccedf71171abf18c69fc25eb4b5c; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb955ff01d7c76c708dbfc9152e363b26c430ccedf71171abf18c69fc25eb4b5c

namespace PerfectPower.SOEModelPackets
def obs179 := PerfectPower.CheckedSOE.Pb955ff01d7c76c708dbfc9152e363b26c430ccedf71171abf18c69fc25eb4b5c.obs
def step179 := PerfectPower.CheckedSOE.Pb955ff01d7c76c708dbfc9152e363b26c430ccedf71171abf18c69fc25eb4b5c.step
def q179 := PerfectPower.CheckedSOE.Pb955ff01d7c76c708dbfc9152e363b26c430ccedf71171abf18c69fc25eb4b5c.q
def out179 := PerfectPower.CheckedSOE.Pb955ff01d7c76c708dbfc9152e363b26c430ccedf71171abf18c69fc25eb4b5c.out
def target179 := PerfectPower.CheckedSOE.Pb955ff01d7c76c708dbfc9152e363b26c430ccedf71171abf18c69fc25eb4b5c.target
theorem complete179 (s t : Fin 2) : SOESemantics.Equivalent step179 obs179 s t ↔ q179 s = q179 t := PerfectPower.CheckedSOE.Pb955ff01d7c76c708dbfc9152e363b26c430ccedf71171abf18c69fc25eb4b5c.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pab0db5a809c798882f42dd706b67ad6ffb2e5222b4b239fa4a1330ee4ab9f5c1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ab0db5a809c798882f42dd706b67ad6ffb2e5222b4b239fa4a1330ee4ab9f5c1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pab0db5a809c798882f42dd706b67ad6ffb2e5222b4b239fa4a1330ee4ab9f5c1

namespace PerfectPower.SOEModelPackets
def obs180 := PerfectPower.CheckedSOE.Pab0db5a809c798882f42dd706b67ad6ffb2e5222b4b239fa4a1330ee4ab9f5c1.obs
def step180 := PerfectPower.CheckedSOE.Pab0db5a809c798882f42dd706b67ad6ffb2e5222b4b239fa4a1330ee4ab9f5c1.step
def q180 := PerfectPower.CheckedSOE.Pab0db5a809c798882f42dd706b67ad6ffb2e5222b4b239fa4a1330ee4ab9f5c1.q
def out180 := PerfectPower.CheckedSOE.Pab0db5a809c798882f42dd706b67ad6ffb2e5222b4b239fa4a1330ee4ab9f5c1.out
def target180 := PerfectPower.CheckedSOE.Pab0db5a809c798882f42dd706b67ad6ffb2e5222b4b239fa4a1330ee4ab9f5c1.target
theorem complete180 (s t : Fin 2) : SOESemantics.Equivalent step180 obs180 s t ↔ q180 s = q180 t := PerfectPower.CheckedSOE.Pab0db5a809c798882f42dd706b67ad6ffb2e5222b4b239fa4a1330ee4ab9f5c1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P74e6e0ce951d8e3626353d54e63c914f52421de76029be0cae0a5b34f4e89929
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 74e6e0ce951d8e3626353d54e63c914f52421de76029be0cae0a5b34f4e89929; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P74e6e0ce951d8e3626353d54e63c914f52421de76029be0cae0a5b34f4e89929

namespace PerfectPower.SOEModelPackets
def obs181 := PerfectPower.CheckedSOE.P74e6e0ce951d8e3626353d54e63c914f52421de76029be0cae0a5b34f4e89929.obs
def step181 := PerfectPower.CheckedSOE.P74e6e0ce951d8e3626353d54e63c914f52421de76029be0cae0a5b34f4e89929.step
def q181 := PerfectPower.CheckedSOE.P74e6e0ce951d8e3626353d54e63c914f52421de76029be0cae0a5b34f4e89929.q
def out181 := PerfectPower.CheckedSOE.P74e6e0ce951d8e3626353d54e63c914f52421de76029be0cae0a5b34f4e89929.out
def target181 := PerfectPower.CheckedSOE.P74e6e0ce951d8e3626353d54e63c914f52421de76029be0cae0a5b34f4e89929.target
theorem complete181 (s t : Fin 2) : SOESemantics.Equivalent step181 obs181 s t ↔ q181 s = q181 t := PerfectPower.CheckedSOE.P74e6e0ce951d8e3626353d54e63c914f52421de76029be0cae0a5b34f4e89929.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P854c5d4d00c42ab8ca6fc07d1c2805a846f7caa0f68deacde90f6c014fb799e1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 854c5d4d00c42ab8ca6fc07d1c2805a846f7caa0f68deacde90f6c014fb799e1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P854c5d4d00c42ab8ca6fc07d1c2805a846f7caa0f68deacde90f6c014fb799e1

namespace PerfectPower.SOEModelPackets
def obs182 := PerfectPower.CheckedSOE.P854c5d4d00c42ab8ca6fc07d1c2805a846f7caa0f68deacde90f6c014fb799e1.obs
def step182 := PerfectPower.CheckedSOE.P854c5d4d00c42ab8ca6fc07d1c2805a846f7caa0f68deacde90f6c014fb799e1.step
def q182 := PerfectPower.CheckedSOE.P854c5d4d00c42ab8ca6fc07d1c2805a846f7caa0f68deacde90f6c014fb799e1.q
def out182 := PerfectPower.CheckedSOE.P854c5d4d00c42ab8ca6fc07d1c2805a846f7caa0f68deacde90f6c014fb799e1.out
def target182 := PerfectPower.CheckedSOE.P854c5d4d00c42ab8ca6fc07d1c2805a846f7caa0f68deacde90f6c014fb799e1.target
theorem complete182 (s t : Fin 2) : SOESemantics.Equivalent step182 obs182 s t ↔ q182 s = q182 t := PerfectPower.CheckedSOE.P854c5d4d00c42ab8ca6fc07d1c2805a846f7caa0f68deacde90f6c014fb799e1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf9b8d24d8259f5fc190108baed230504d5eced93c21d4e00402febb1fe8911b2
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f9b8d24d8259f5fc190108baed230504d5eced93c21d4e00402febb1fe8911b2; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf9b8d24d8259f5fc190108baed230504d5eced93c21d4e00402febb1fe8911b2

namespace PerfectPower.SOEModelPackets
def obs183 := PerfectPower.CheckedSOE.Pf9b8d24d8259f5fc190108baed230504d5eced93c21d4e00402febb1fe8911b2.obs
def step183 := PerfectPower.CheckedSOE.Pf9b8d24d8259f5fc190108baed230504d5eced93c21d4e00402febb1fe8911b2.step
def q183 := PerfectPower.CheckedSOE.Pf9b8d24d8259f5fc190108baed230504d5eced93c21d4e00402febb1fe8911b2.q
def out183 := PerfectPower.CheckedSOE.Pf9b8d24d8259f5fc190108baed230504d5eced93c21d4e00402febb1fe8911b2.out
def target183 := PerfectPower.CheckedSOE.Pf9b8d24d8259f5fc190108baed230504d5eced93c21d4e00402febb1fe8911b2.target
theorem complete183 (s t : Fin 2) : SOESemantics.Equivalent step183 obs183 s t ↔ q183 s = q183 t := PerfectPower.CheckedSOE.Pf9b8d24d8259f5fc190108baed230504d5eced93c21d4e00402febb1fe8911b2.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0467f08ed74d1e93a9f9d7ed9af3ee9cbefe02f3b3c3fb06146622e165e5a314
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0467f08ed74d1e93a9f9d7ed9af3ee9cbefe02f3b3c3fb06146622e165e5a314; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0467f08ed74d1e93a9f9d7ed9af3ee9cbefe02f3b3c3fb06146622e165e5a314

namespace PerfectPower.SOEModelPackets
def obs184 := PerfectPower.CheckedSOE.P0467f08ed74d1e93a9f9d7ed9af3ee9cbefe02f3b3c3fb06146622e165e5a314.obs
def step184 := PerfectPower.CheckedSOE.P0467f08ed74d1e93a9f9d7ed9af3ee9cbefe02f3b3c3fb06146622e165e5a314.step
def q184 := PerfectPower.CheckedSOE.P0467f08ed74d1e93a9f9d7ed9af3ee9cbefe02f3b3c3fb06146622e165e5a314.q
def out184 := PerfectPower.CheckedSOE.P0467f08ed74d1e93a9f9d7ed9af3ee9cbefe02f3b3c3fb06146622e165e5a314.out
def target184 := PerfectPower.CheckedSOE.P0467f08ed74d1e93a9f9d7ed9af3ee9cbefe02f3b3c3fb06146622e165e5a314.target
theorem complete184 (s t : Fin 2) : SOESemantics.Equivalent step184 obs184 s t ↔ q184 s = q184 t := PerfectPower.CheckedSOE.P0467f08ed74d1e93a9f9d7ed9af3ee9cbefe02f3b3c3fb06146622e165e5a314.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pf36f3cb548325eb759ef2795a68fe5dfec0bac4c2e478ac875acddb013faa12a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: f36f3cb548325eb759ef2795a68fe5dfec0bac4c2e478ac875acddb013faa12a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pf36f3cb548325eb759ef2795a68fe5dfec0bac4c2e478ac875acddb013faa12a

namespace PerfectPower.SOEModelPackets
def obs185 := PerfectPower.CheckedSOE.Pf36f3cb548325eb759ef2795a68fe5dfec0bac4c2e478ac875acddb013faa12a.obs
def step185 := PerfectPower.CheckedSOE.Pf36f3cb548325eb759ef2795a68fe5dfec0bac4c2e478ac875acddb013faa12a.step
def q185 := PerfectPower.CheckedSOE.Pf36f3cb548325eb759ef2795a68fe5dfec0bac4c2e478ac875acddb013faa12a.q
def out185 := PerfectPower.CheckedSOE.Pf36f3cb548325eb759ef2795a68fe5dfec0bac4c2e478ac875acddb013faa12a.out
def target185 := PerfectPower.CheckedSOE.Pf36f3cb548325eb759ef2795a68fe5dfec0bac4c2e478ac875acddb013faa12a.target
theorem complete185 (s t : Fin 2) : SOESemantics.Equivalent step185 obs185 s t ↔ q185 s = q185 t := PerfectPower.CheckedSOE.Pf36f3cb548325eb759ef2795a68fe5dfec0bac4c2e478ac875acddb013faa12a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe5108ae8ae50fc7665272cbf79f8fba2db7e54baeca45a8abda3f01def339051
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e5108ae8ae50fc7665272cbf79f8fba2db7e54baeca45a8abda3f01def339051; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe5108ae8ae50fc7665272cbf79f8fba2db7e54baeca45a8abda3f01def339051

namespace PerfectPower.SOEModelPackets
def obs186 := PerfectPower.CheckedSOE.Pe5108ae8ae50fc7665272cbf79f8fba2db7e54baeca45a8abda3f01def339051.obs
def step186 := PerfectPower.CheckedSOE.Pe5108ae8ae50fc7665272cbf79f8fba2db7e54baeca45a8abda3f01def339051.step
def q186 := PerfectPower.CheckedSOE.Pe5108ae8ae50fc7665272cbf79f8fba2db7e54baeca45a8abda3f01def339051.q
def out186 := PerfectPower.CheckedSOE.Pe5108ae8ae50fc7665272cbf79f8fba2db7e54baeca45a8abda3f01def339051.out
def target186 := PerfectPower.CheckedSOE.Pe5108ae8ae50fc7665272cbf79f8fba2db7e54baeca45a8abda3f01def339051.target
theorem complete186 (s t : Fin 2) : SOESemantics.Equivalent step186 obs186 s t ↔ q186 s = q186 t := PerfectPower.CheckedSOE.Pe5108ae8ae50fc7665272cbf79f8fba2db7e54baeca45a8abda3f01def339051.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa296285ad4a2150a25232a20e55d6624432d0d3740136a42b95bc913841c626f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a296285ad4a2150a25232a20e55d6624432d0d3740136a42b95bc913841c626f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa296285ad4a2150a25232a20e55d6624432d0d3740136a42b95bc913841c626f

namespace PerfectPower.SOEModelPackets
def obs187 := PerfectPower.CheckedSOE.Pa296285ad4a2150a25232a20e55d6624432d0d3740136a42b95bc913841c626f.obs
def step187 := PerfectPower.CheckedSOE.Pa296285ad4a2150a25232a20e55d6624432d0d3740136a42b95bc913841c626f.step
def q187 := PerfectPower.CheckedSOE.Pa296285ad4a2150a25232a20e55d6624432d0d3740136a42b95bc913841c626f.q
def out187 := PerfectPower.CheckedSOE.Pa296285ad4a2150a25232a20e55d6624432d0d3740136a42b95bc913841c626f.out
def target187 := PerfectPower.CheckedSOE.Pa296285ad4a2150a25232a20e55d6624432d0d3740136a42b95bc913841c626f.target
theorem complete187 (s t : Fin 2) : SOESemantics.Equivalent step187 obs187 s t ↔ q187 s = q187 t := PerfectPower.CheckedSOE.Pa296285ad4a2150a25232a20e55d6624432d0d3740136a42b95bc913841c626f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbafc39ede9290f0a768f91131ed9568091e2ba60385ab91276c7ac3638d5d83c
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: bafc39ede9290f0a768f91131ed9568091e2ba60385ab91276c7ac3638d5d83c; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbafc39ede9290f0a768f91131ed9568091e2ba60385ab91276c7ac3638d5d83c

namespace PerfectPower.SOEModelPackets
def obs188 := PerfectPower.CheckedSOE.Pbafc39ede9290f0a768f91131ed9568091e2ba60385ab91276c7ac3638d5d83c.obs
def step188 := PerfectPower.CheckedSOE.Pbafc39ede9290f0a768f91131ed9568091e2ba60385ab91276c7ac3638d5d83c.step
def q188 := PerfectPower.CheckedSOE.Pbafc39ede9290f0a768f91131ed9568091e2ba60385ab91276c7ac3638d5d83c.q
def out188 := PerfectPower.CheckedSOE.Pbafc39ede9290f0a768f91131ed9568091e2ba60385ab91276c7ac3638d5d83c.out
def target188 := PerfectPower.CheckedSOE.Pbafc39ede9290f0a768f91131ed9568091e2ba60385ab91276c7ac3638d5d83c.target
theorem complete188 (s t : Fin 2) : SOESemantics.Equivalent step188 obs188 s t ↔ q188 s = q188 t := PerfectPower.CheckedSOE.Pbafc39ede9290f0a768f91131ed9568091e2ba60385ab91276c7ac3638d5d83c.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P03b8b49d7990f031eeabf74507585f3be4b70bfd114a36b21677646f782fd32d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 03b8b49d7990f031eeabf74507585f3be4b70bfd114a36b21677646f782fd32d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P03b8b49d7990f031eeabf74507585f3be4b70bfd114a36b21677646f782fd32d

namespace PerfectPower.SOEModelPackets
def obs189 := PerfectPower.CheckedSOE.P03b8b49d7990f031eeabf74507585f3be4b70bfd114a36b21677646f782fd32d.obs
def step189 := PerfectPower.CheckedSOE.P03b8b49d7990f031eeabf74507585f3be4b70bfd114a36b21677646f782fd32d.step
def q189 := PerfectPower.CheckedSOE.P03b8b49d7990f031eeabf74507585f3be4b70bfd114a36b21677646f782fd32d.q
def out189 := PerfectPower.CheckedSOE.P03b8b49d7990f031eeabf74507585f3be4b70bfd114a36b21677646f782fd32d.out
def target189 := PerfectPower.CheckedSOE.P03b8b49d7990f031eeabf74507585f3be4b70bfd114a36b21677646f782fd32d.target
theorem complete189 (s t : Fin 2) : SOESemantics.Equivalent step189 obs189 s t ↔ q189 s = q189 t := PerfectPower.CheckedSOE.P03b8b49d7990f031eeabf74507585f3be4b70bfd114a36b21677646f782fd32d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P1833b12bb310b59aa654d1c6c85c0c794de6622f03260097b088e218886d6113
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 1833b12bb310b59aa654d1c6c85c0c794de6622f03260097b088e218886d6113; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P1833b12bb310b59aa654d1c6c85c0c794de6622f03260097b088e218886d6113

namespace PerfectPower.SOEModelPackets
def obs190 := PerfectPower.CheckedSOE.P1833b12bb310b59aa654d1c6c85c0c794de6622f03260097b088e218886d6113.obs
def step190 := PerfectPower.CheckedSOE.P1833b12bb310b59aa654d1c6c85c0c794de6622f03260097b088e218886d6113.step
def q190 := PerfectPower.CheckedSOE.P1833b12bb310b59aa654d1c6c85c0c794de6622f03260097b088e218886d6113.q
def out190 := PerfectPower.CheckedSOE.P1833b12bb310b59aa654d1c6c85c0c794de6622f03260097b088e218886d6113.out
def target190 := PerfectPower.CheckedSOE.P1833b12bb310b59aa654d1c6c85c0c794de6622f03260097b088e218886d6113.target
theorem complete190 (s t : Fin 2) : SOESemantics.Equivalent step190 obs190 s t ↔ q190 s = q190 t := PerfectPower.CheckedSOE.P1833b12bb310b59aa654d1c6c85c0c794de6622f03260097b088e218886d6113.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P489075c8cba1c0ad41e376c110843cd25dfe5173283892523cbbdac9ca3bad9e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 489075c8cba1c0ad41e376c110843cd25dfe5173283892523cbbdac9ca3bad9e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P489075c8cba1c0ad41e376c110843cd25dfe5173283892523cbbdac9ca3bad9e

namespace PerfectPower.SOEModelPackets
def obs191 := PerfectPower.CheckedSOE.P489075c8cba1c0ad41e376c110843cd25dfe5173283892523cbbdac9ca3bad9e.obs
def step191 := PerfectPower.CheckedSOE.P489075c8cba1c0ad41e376c110843cd25dfe5173283892523cbbdac9ca3bad9e.step
def q191 := PerfectPower.CheckedSOE.P489075c8cba1c0ad41e376c110843cd25dfe5173283892523cbbdac9ca3bad9e.q
def out191 := PerfectPower.CheckedSOE.P489075c8cba1c0ad41e376c110843cd25dfe5173283892523cbbdac9ca3bad9e.out
def target191 := PerfectPower.CheckedSOE.P489075c8cba1c0ad41e376c110843cd25dfe5173283892523cbbdac9ca3bad9e.target
theorem complete191 (s t : Fin 2) : SOESemantics.Equivalent step191 obs191 s t ↔ q191 s = q191 t := PerfectPower.CheckedSOE.P489075c8cba1c0ad41e376c110843cd25dfe5173283892523cbbdac9ca3bad9e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pda28a365ed65d9fe1bae6c7d97d089eecefc0a07fce448853244c3909a0cdc4e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: da28a365ed65d9fe1bae6c7d97d089eecefc0a07fce448853244c3909a0cdc4e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pda28a365ed65d9fe1bae6c7d97d089eecefc0a07fce448853244c3909a0cdc4e

namespace PerfectPower.SOEModelPackets
def obs192 := PerfectPower.CheckedSOE.Pda28a365ed65d9fe1bae6c7d97d089eecefc0a07fce448853244c3909a0cdc4e.obs
def step192 := PerfectPower.CheckedSOE.Pda28a365ed65d9fe1bae6c7d97d089eecefc0a07fce448853244c3909a0cdc4e.step
def q192 := PerfectPower.CheckedSOE.Pda28a365ed65d9fe1bae6c7d97d089eecefc0a07fce448853244c3909a0cdc4e.q
def out192 := PerfectPower.CheckedSOE.Pda28a365ed65d9fe1bae6c7d97d089eecefc0a07fce448853244c3909a0cdc4e.out
def target192 := PerfectPower.CheckedSOE.Pda28a365ed65d9fe1bae6c7d97d089eecefc0a07fce448853244c3909a0cdc4e.target
theorem complete192 (s t : Fin 2) : SOESemantics.Equivalent step192 obs192 s t ↔ q192 s = q192 t := PerfectPower.CheckedSOE.Pda28a365ed65d9fe1bae6c7d97d089eecefc0a07fce448853244c3909a0cdc4e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P1cd565f00d081d12522e8aeb7affa2265389cf9b47c564e256850227e3768edc
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 1cd565f00d081d12522e8aeb7affa2265389cf9b47c564e256850227e3768edc; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P1cd565f00d081d12522e8aeb7affa2265389cf9b47c564e256850227e3768edc

namespace PerfectPower.SOEModelPackets
def obs193 := PerfectPower.CheckedSOE.P1cd565f00d081d12522e8aeb7affa2265389cf9b47c564e256850227e3768edc.obs
def step193 := PerfectPower.CheckedSOE.P1cd565f00d081d12522e8aeb7affa2265389cf9b47c564e256850227e3768edc.step
def q193 := PerfectPower.CheckedSOE.P1cd565f00d081d12522e8aeb7affa2265389cf9b47c564e256850227e3768edc.q
def out193 := PerfectPower.CheckedSOE.P1cd565f00d081d12522e8aeb7affa2265389cf9b47c564e256850227e3768edc.out
def target193 := PerfectPower.CheckedSOE.P1cd565f00d081d12522e8aeb7affa2265389cf9b47c564e256850227e3768edc.target
theorem complete193 (s t : Fin 2) : SOESemantics.Equivalent step193 obs193 s t ↔ q193 s = q193 t := PerfectPower.CheckedSOE.P1cd565f00d081d12522e8aeb7affa2265389cf9b47c564e256850227e3768edc.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd63a46e80cfd4ceffe56c4b3c75f84bc48db2eff4b9e2f7656bae914562f4922
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d63a46e80cfd4ceffe56c4b3c75f84bc48db2eff4b9e2f7656bae914562f4922; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd63a46e80cfd4ceffe56c4b3c75f84bc48db2eff4b9e2f7656bae914562f4922

namespace PerfectPower.SOEModelPackets
def obs194 := PerfectPower.CheckedSOE.Pd63a46e80cfd4ceffe56c4b3c75f84bc48db2eff4b9e2f7656bae914562f4922.obs
def step194 := PerfectPower.CheckedSOE.Pd63a46e80cfd4ceffe56c4b3c75f84bc48db2eff4b9e2f7656bae914562f4922.step
def q194 := PerfectPower.CheckedSOE.Pd63a46e80cfd4ceffe56c4b3c75f84bc48db2eff4b9e2f7656bae914562f4922.q
def out194 := PerfectPower.CheckedSOE.Pd63a46e80cfd4ceffe56c4b3c75f84bc48db2eff4b9e2f7656bae914562f4922.out
def target194 := PerfectPower.CheckedSOE.Pd63a46e80cfd4ceffe56c4b3c75f84bc48db2eff4b9e2f7656bae914562f4922.target
theorem complete194 (s t : Fin 2) : SOESemantics.Equivalent step194 obs194 s t ↔ q194 s = q194 t := PerfectPower.CheckedSOE.Pd63a46e80cfd4ceffe56c4b3c75f84bc48db2eff4b9e2f7656bae914562f4922.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P56ce857c21cbaee25cef22107635502c18cc87f39b8a234d690ff95ee976f1d6
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 56ce857c21cbaee25cef22107635502c18cc87f39b8a234d690ff95ee976f1d6; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P56ce857c21cbaee25cef22107635502c18cc87f39b8a234d690ff95ee976f1d6

namespace PerfectPower.SOEModelPackets
def obs195 := PerfectPower.CheckedSOE.P56ce857c21cbaee25cef22107635502c18cc87f39b8a234d690ff95ee976f1d6.obs
def step195 := PerfectPower.CheckedSOE.P56ce857c21cbaee25cef22107635502c18cc87f39b8a234d690ff95ee976f1d6.step
def q195 := PerfectPower.CheckedSOE.P56ce857c21cbaee25cef22107635502c18cc87f39b8a234d690ff95ee976f1d6.q
def out195 := PerfectPower.CheckedSOE.P56ce857c21cbaee25cef22107635502c18cc87f39b8a234d690ff95ee976f1d6.out
def target195 := PerfectPower.CheckedSOE.P56ce857c21cbaee25cef22107635502c18cc87f39b8a234d690ff95ee976f1d6.target
theorem complete195 (s t : Fin 2) : SOESemantics.Equivalent step195 obs195 s t ↔ q195 s = q195 t := PerfectPower.CheckedSOE.P56ce857c21cbaee25cef22107635502c18cc87f39b8a234d690ff95ee976f1d6.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P3068334745171ebe346a7874df14424d6d28487cd6a585606c891c6f29396033
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3068334745171ebe346a7874df14424d6d28487cd6a585606c891c6f29396033; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P3068334745171ebe346a7874df14424d6d28487cd6a585606c891c6f29396033

namespace PerfectPower.SOEModelPackets
def obs196 := PerfectPower.CheckedSOE.P3068334745171ebe346a7874df14424d6d28487cd6a585606c891c6f29396033.obs
def step196 := PerfectPower.CheckedSOE.P3068334745171ebe346a7874df14424d6d28487cd6a585606c891c6f29396033.step
def q196 := PerfectPower.CheckedSOE.P3068334745171ebe346a7874df14424d6d28487cd6a585606c891c6f29396033.q
def out196 := PerfectPower.CheckedSOE.P3068334745171ebe346a7874df14424d6d28487cd6a585606c891c6f29396033.out
def target196 := PerfectPower.CheckedSOE.P3068334745171ebe346a7874df14424d6d28487cd6a585606c891c6f29396033.target
theorem complete196 (s t : Fin 2) : SOESemantics.Equivalent step196 obs196 s t ↔ q196 s = q196 t := PerfectPower.CheckedSOE.P3068334745171ebe346a7874df14424d6d28487cd6a585606c891c6f29396033.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P72f13ba24a8b95d152c7f53061027be8cbf53ca47df16a5d978137050b2c21bb
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 72f13ba24a8b95d152c7f53061027be8cbf53ca47df16a5d978137050b2c21bb; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P72f13ba24a8b95d152c7f53061027be8cbf53ca47df16a5d978137050b2c21bb

namespace PerfectPower.SOEModelPackets
def obs197 := PerfectPower.CheckedSOE.P72f13ba24a8b95d152c7f53061027be8cbf53ca47df16a5d978137050b2c21bb.obs
def step197 := PerfectPower.CheckedSOE.P72f13ba24a8b95d152c7f53061027be8cbf53ca47df16a5d978137050b2c21bb.step
def q197 := PerfectPower.CheckedSOE.P72f13ba24a8b95d152c7f53061027be8cbf53ca47df16a5d978137050b2c21bb.q
def out197 := PerfectPower.CheckedSOE.P72f13ba24a8b95d152c7f53061027be8cbf53ca47df16a5d978137050b2c21bb.out
def target197 := PerfectPower.CheckedSOE.P72f13ba24a8b95d152c7f53061027be8cbf53ca47df16a5d978137050b2c21bb.target
theorem complete197 (s t : Fin 2) : SOESemantics.Equivalent step197 obs197 s t ↔ q197 s = q197 t := PerfectPower.CheckedSOE.P72f13ba24a8b95d152c7f53061027be8cbf53ca47df16a5d978137050b2c21bb.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pce1ae5f4a099fb8d36818c3d51dd95be71b88723cc8de18f39e25f8618dc27de
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ce1ae5f4a099fb8d36818c3d51dd95be71b88723cc8de18f39e25f8618dc27de; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pce1ae5f4a099fb8d36818c3d51dd95be71b88723cc8de18f39e25f8618dc27de

namespace PerfectPower.SOEModelPackets
def obs198 := PerfectPower.CheckedSOE.Pce1ae5f4a099fb8d36818c3d51dd95be71b88723cc8de18f39e25f8618dc27de.obs
def step198 := PerfectPower.CheckedSOE.Pce1ae5f4a099fb8d36818c3d51dd95be71b88723cc8de18f39e25f8618dc27de.step
def q198 := PerfectPower.CheckedSOE.Pce1ae5f4a099fb8d36818c3d51dd95be71b88723cc8de18f39e25f8618dc27de.q
def out198 := PerfectPower.CheckedSOE.Pce1ae5f4a099fb8d36818c3d51dd95be71b88723cc8de18f39e25f8618dc27de.out
def target198 := PerfectPower.CheckedSOE.Pce1ae5f4a099fb8d36818c3d51dd95be71b88723cc8de18f39e25f8618dc27de.target
theorem complete198 (s t : Fin 2) : SOESemantics.Equivalent step198 obs198 s t ↔ q198 s = q198 t := PerfectPower.CheckedSOE.Pce1ae5f4a099fb8d36818c3d51dd95be71b88723cc8de18f39e25f8618dc27de.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pfd9252d3014a8ab17f5b23a49e9e88fce5e0d286fed9e3be6ec0db9a48e4d2c0
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: fd9252d3014a8ab17f5b23a49e9e88fce5e0d286fed9e3be6ec0db9a48e4d2c0; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pfd9252d3014a8ab17f5b23a49e9e88fce5e0d286fed9e3be6ec0db9a48e4d2c0

namespace PerfectPower.SOEModelPackets
def obs199 := PerfectPower.CheckedSOE.Pfd9252d3014a8ab17f5b23a49e9e88fce5e0d286fed9e3be6ec0db9a48e4d2c0.obs
def step199 := PerfectPower.CheckedSOE.Pfd9252d3014a8ab17f5b23a49e9e88fce5e0d286fed9e3be6ec0db9a48e4d2c0.step
def q199 := PerfectPower.CheckedSOE.Pfd9252d3014a8ab17f5b23a49e9e88fce5e0d286fed9e3be6ec0db9a48e4d2c0.q
def out199 := PerfectPower.CheckedSOE.Pfd9252d3014a8ab17f5b23a49e9e88fce5e0d286fed9e3be6ec0db9a48e4d2c0.out
def target199 := PerfectPower.CheckedSOE.Pfd9252d3014a8ab17f5b23a49e9e88fce5e0d286fed9e3be6ec0db9a48e4d2c0.target
theorem complete199 (s t : Fin 2) : SOESemantics.Equivalent step199 obs199 s t ↔ q199 s = q199 t := PerfectPower.CheckedSOE.Pfd9252d3014a8ab17f5b23a49e9e88fce5e0d286fed9e3be6ec0db9a48e4d2c0.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P3199f8b7dae04fb4268e617c8e6e90d430663e0ae994ede3fca1fbeafe5440d1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 3199f8b7dae04fb4268e617c8e6e90d430663e0ae994ede3fca1fbeafe5440d1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P3199f8b7dae04fb4268e617c8e6e90d430663e0ae994ede3fca1fbeafe5440d1

namespace PerfectPower.SOEModelPackets
def obs200 := PerfectPower.CheckedSOE.P3199f8b7dae04fb4268e617c8e6e90d430663e0ae994ede3fca1fbeafe5440d1.obs
def step200 := PerfectPower.CheckedSOE.P3199f8b7dae04fb4268e617c8e6e90d430663e0ae994ede3fca1fbeafe5440d1.step
def q200 := PerfectPower.CheckedSOE.P3199f8b7dae04fb4268e617c8e6e90d430663e0ae994ede3fca1fbeafe5440d1.q
def out200 := PerfectPower.CheckedSOE.P3199f8b7dae04fb4268e617c8e6e90d430663e0ae994ede3fca1fbeafe5440d1.out
def target200 := PerfectPower.CheckedSOE.P3199f8b7dae04fb4268e617c8e6e90d430663e0ae994ede3fca1fbeafe5440d1.target
theorem complete200 (s t : Fin 2) : SOESemantics.Equivalent step200 obs200 s t ↔ q200 s = q200 t := PerfectPower.CheckedSOE.P3199f8b7dae04fb4268e617c8e6e90d430663e0ae994ede3fca1fbeafe5440d1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P8ad5b318047535db11a30d3f82e2969ec30a804913ed22678058731621997862
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 8ad5b318047535db11a30d3f82e2969ec30a804913ed22678058731621997862; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P8ad5b318047535db11a30d3f82e2969ec30a804913ed22678058731621997862

namespace PerfectPower.SOEModelPackets
def obs201 := PerfectPower.CheckedSOE.P8ad5b318047535db11a30d3f82e2969ec30a804913ed22678058731621997862.obs
def step201 := PerfectPower.CheckedSOE.P8ad5b318047535db11a30d3f82e2969ec30a804913ed22678058731621997862.step
def q201 := PerfectPower.CheckedSOE.P8ad5b318047535db11a30d3f82e2969ec30a804913ed22678058731621997862.q
def out201 := PerfectPower.CheckedSOE.P8ad5b318047535db11a30d3f82e2969ec30a804913ed22678058731621997862.out
def target201 := PerfectPower.CheckedSOE.P8ad5b318047535db11a30d3f82e2969ec30a804913ed22678058731621997862.target
theorem complete201 (s t : Fin 2) : SOESemantics.Equivalent step201 obs201 s t ↔ q201 s = q201 t := PerfectPower.CheckedSOE.P8ad5b318047535db11a30d3f82e2969ec30a804913ed22678058731621997862.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6d50da6b9b4a8cc5ecae5823fe75a83a14d2896215a3d12ec750d4427f15203e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6d50da6b9b4a8cc5ecae5823fe75a83a14d2896215a3d12ec750d4427f15203e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6d50da6b9b4a8cc5ecae5823fe75a83a14d2896215a3d12ec750d4427f15203e

namespace PerfectPower.SOEModelPackets
def obs202 := PerfectPower.CheckedSOE.P6d50da6b9b4a8cc5ecae5823fe75a83a14d2896215a3d12ec750d4427f15203e.obs
def step202 := PerfectPower.CheckedSOE.P6d50da6b9b4a8cc5ecae5823fe75a83a14d2896215a3d12ec750d4427f15203e.step
def q202 := PerfectPower.CheckedSOE.P6d50da6b9b4a8cc5ecae5823fe75a83a14d2896215a3d12ec750d4427f15203e.q
def out202 := PerfectPower.CheckedSOE.P6d50da6b9b4a8cc5ecae5823fe75a83a14d2896215a3d12ec750d4427f15203e.out
def target202 := PerfectPower.CheckedSOE.P6d50da6b9b4a8cc5ecae5823fe75a83a14d2896215a3d12ec750d4427f15203e.target
theorem complete202 (s t : Fin 2) : SOESemantics.Equivalent step202 obs202 s t ↔ q202 s = q202 t := PerfectPower.CheckedSOE.P6d50da6b9b4a8cc5ecae5823fe75a83a14d2896215a3d12ec750d4427f15203e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P76f5275104ed7de179c3d0e079e4b1330426acb6490fb927d073e239ec390798
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 76f5275104ed7de179c3d0e079e4b1330426acb6490fb927d073e239ec390798; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P76f5275104ed7de179c3d0e079e4b1330426acb6490fb927d073e239ec390798

namespace PerfectPower.SOEModelPackets
def obs203 := PerfectPower.CheckedSOE.P76f5275104ed7de179c3d0e079e4b1330426acb6490fb927d073e239ec390798.obs
def step203 := PerfectPower.CheckedSOE.P76f5275104ed7de179c3d0e079e4b1330426acb6490fb927d073e239ec390798.step
def q203 := PerfectPower.CheckedSOE.P76f5275104ed7de179c3d0e079e4b1330426acb6490fb927d073e239ec390798.q
def out203 := PerfectPower.CheckedSOE.P76f5275104ed7de179c3d0e079e4b1330426acb6490fb927d073e239ec390798.out
def target203 := PerfectPower.CheckedSOE.P76f5275104ed7de179c3d0e079e4b1330426acb6490fb927d073e239ec390798.target
theorem complete203 (s t : Fin 2) : SOESemantics.Equivalent step203 obs203 s t ↔ q203 s = q203 t := PerfectPower.CheckedSOE.P76f5275104ed7de179c3d0e079e4b1330426acb6490fb927d073e239ec390798.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pcf21e322afc68a3374a8e026f0726d78a40fb3776190b8318ea0ec951f3c57c9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: cf21e322afc68a3374a8e026f0726d78a40fb3776190b8318ea0ec951f3c57c9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pcf21e322afc68a3374a8e026f0726d78a40fb3776190b8318ea0ec951f3c57c9

namespace PerfectPower.SOEModelPackets
def obs204 := PerfectPower.CheckedSOE.Pcf21e322afc68a3374a8e026f0726d78a40fb3776190b8318ea0ec951f3c57c9.obs
def step204 := PerfectPower.CheckedSOE.Pcf21e322afc68a3374a8e026f0726d78a40fb3776190b8318ea0ec951f3c57c9.step
def q204 := PerfectPower.CheckedSOE.Pcf21e322afc68a3374a8e026f0726d78a40fb3776190b8318ea0ec951f3c57c9.q
def out204 := PerfectPower.CheckedSOE.Pcf21e322afc68a3374a8e026f0726d78a40fb3776190b8318ea0ec951f3c57c9.out
def target204 := PerfectPower.CheckedSOE.Pcf21e322afc68a3374a8e026f0726d78a40fb3776190b8318ea0ec951f3c57c9.target
theorem complete204 (s t : Fin 2) : SOESemantics.Equivalent step204 obs204 s t ↔ q204 s = q204 t := PerfectPower.CheckedSOE.Pcf21e322afc68a3374a8e026f0726d78a40fb3776190b8318ea0ec951f3c57c9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb61096515fc2ce3042f7917de1fc042ff2477f67fd96fb34d86a2db2a0fa63ab
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b61096515fc2ce3042f7917de1fc042ff2477f67fd96fb34d86a2db2a0fa63ab; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb61096515fc2ce3042f7917de1fc042ff2477f67fd96fb34d86a2db2a0fa63ab

namespace PerfectPower.SOEModelPackets
def obs205 := PerfectPower.CheckedSOE.Pb61096515fc2ce3042f7917de1fc042ff2477f67fd96fb34d86a2db2a0fa63ab.obs
def step205 := PerfectPower.CheckedSOE.Pb61096515fc2ce3042f7917de1fc042ff2477f67fd96fb34d86a2db2a0fa63ab.step
def q205 := PerfectPower.CheckedSOE.Pb61096515fc2ce3042f7917de1fc042ff2477f67fd96fb34d86a2db2a0fa63ab.q
def out205 := PerfectPower.CheckedSOE.Pb61096515fc2ce3042f7917de1fc042ff2477f67fd96fb34d86a2db2a0fa63ab.out
def target205 := PerfectPower.CheckedSOE.Pb61096515fc2ce3042f7917de1fc042ff2477f67fd96fb34d86a2db2a0fa63ab.target
theorem complete205 (s t : Fin 2) : SOESemantics.Equivalent step205 obs205 s t ↔ q205 s = q205 t := PerfectPower.CheckedSOE.Pb61096515fc2ce3042f7917de1fc042ff2477f67fd96fb34d86a2db2a0fa63ab.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6d1a822bdcff671201465bb2505e8ca7ad7ca9f6b6628f97f2f3ef52acb98a88
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6d1a822bdcff671201465bb2505e8ca7ad7ca9f6b6628f97f2f3ef52acb98a88; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6d1a822bdcff671201465bb2505e8ca7ad7ca9f6b6628f97f2f3ef52acb98a88

namespace PerfectPower.SOEModelPackets
def obs206 := PerfectPower.CheckedSOE.P6d1a822bdcff671201465bb2505e8ca7ad7ca9f6b6628f97f2f3ef52acb98a88.obs
def step206 := PerfectPower.CheckedSOE.P6d1a822bdcff671201465bb2505e8ca7ad7ca9f6b6628f97f2f3ef52acb98a88.step
def q206 := PerfectPower.CheckedSOE.P6d1a822bdcff671201465bb2505e8ca7ad7ca9f6b6628f97f2f3ef52acb98a88.q
def out206 := PerfectPower.CheckedSOE.P6d1a822bdcff671201465bb2505e8ca7ad7ca9f6b6628f97f2f3ef52acb98a88.out
def target206 := PerfectPower.CheckedSOE.P6d1a822bdcff671201465bb2505e8ca7ad7ca9f6b6628f97f2f3ef52acb98a88.target
theorem complete206 (s t : Fin 2) : SOESemantics.Equivalent step206 obs206 s t ↔ q206 s = q206 t := PerfectPower.CheckedSOE.P6d1a822bdcff671201465bb2505e8ca7ad7ca9f6b6628f97f2f3ef52acb98a88.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P696df3992ff8ab5a1f5575c21e5881c766f01a3f531581118d58abe467d41554
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 696df3992ff8ab5a1f5575c21e5881c766f01a3f531581118d58abe467d41554; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P696df3992ff8ab5a1f5575c21e5881c766f01a3f531581118d58abe467d41554

namespace PerfectPower.SOEModelPackets
def obs207 := PerfectPower.CheckedSOE.P696df3992ff8ab5a1f5575c21e5881c766f01a3f531581118d58abe467d41554.obs
def step207 := PerfectPower.CheckedSOE.P696df3992ff8ab5a1f5575c21e5881c766f01a3f531581118d58abe467d41554.step
def q207 := PerfectPower.CheckedSOE.P696df3992ff8ab5a1f5575c21e5881c766f01a3f531581118d58abe467d41554.q
def out207 := PerfectPower.CheckedSOE.P696df3992ff8ab5a1f5575c21e5881c766f01a3f531581118d58abe467d41554.out
def target207 := PerfectPower.CheckedSOE.P696df3992ff8ab5a1f5575c21e5881c766f01a3f531581118d58abe467d41554.target
theorem complete207 (s t : Fin 2) : SOESemantics.Equivalent step207 obs207 s t ↔ q207 s = q207 t := PerfectPower.CheckedSOE.P696df3992ff8ab5a1f5575c21e5881c766f01a3f531581118d58abe467d41554.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P94d8b61175a6e002b490130855a0f96fae4fb657834eec9c8b44ba1130b82aa0
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 94d8b61175a6e002b490130855a0f96fae4fb657834eec9c8b44ba1130b82aa0; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P94d8b61175a6e002b490130855a0f96fae4fb657834eec9c8b44ba1130b82aa0

namespace PerfectPower.SOEModelPackets
def obs208 := PerfectPower.CheckedSOE.P94d8b61175a6e002b490130855a0f96fae4fb657834eec9c8b44ba1130b82aa0.obs
def step208 := PerfectPower.CheckedSOE.P94d8b61175a6e002b490130855a0f96fae4fb657834eec9c8b44ba1130b82aa0.step
def q208 := PerfectPower.CheckedSOE.P94d8b61175a6e002b490130855a0f96fae4fb657834eec9c8b44ba1130b82aa0.q
def out208 := PerfectPower.CheckedSOE.P94d8b61175a6e002b490130855a0f96fae4fb657834eec9c8b44ba1130b82aa0.out
def target208 := PerfectPower.CheckedSOE.P94d8b61175a6e002b490130855a0f96fae4fb657834eec9c8b44ba1130b82aa0.target
theorem complete208 (s t : Fin 2) : SOESemantics.Equivalent step208 obs208 s t ↔ q208 s = q208 t := PerfectPower.CheckedSOE.P94d8b61175a6e002b490130855a0f96fae4fb657834eec9c8b44ba1130b82aa0.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2b141716131ae036a6e3a108a0252caef64952606d84d81bd4b5bb79b61f9512
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2b141716131ae036a6e3a108a0252caef64952606d84d81bd4b5bb79b61f9512; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2b141716131ae036a6e3a108a0252caef64952606d84d81bd4b5bb79b61f9512

namespace PerfectPower.SOEModelPackets
def obs209 := PerfectPower.CheckedSOE.P2b141716131ae036a6e3a108a0252caef64952606d84d81bd4b5bb79b61f9512.obs
def step209 := PerfectPower.CheckedSOE.P2b141716131ae036a6e3a108a0252caef64952606d84d81bd4b5bb79b61f9512.step
def q209 := PerfectPower.CheckedSOE.P2b141716131ae036a6e3a108a0252caef64952606d84d81bd4b5bb79b61f9512.q
def out209 := PerfectPower.CheckedSOE.P2b141716131ae036a6e3a108a0252caef64952606d84d81bd4b5bb79b61f9512.out
def target209 := PerfectPower.CheckedSOE.P2b141716131ae036a6e3a108a0252caef64952606d84d81bd4b5bb79b61f9512.target
theorem complete209 (s t : Fin 2) : SOESemantics.Equivalent step209 obs209 s t ↔ q209 s = q209 t := PerfectPower.CheckedSOE.P2b141716131ae036a6e3a108a0252caef64952606d84d81bd4b5bb79b61f9512.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe3c81e22d4bfaaa0246f5d01a1d96ad0022d499bd76c0223b82dc475d23757c4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e3c81e22d4bfaaa0246f5d01a1d96ad0022d499bd76c0223b82dc475d23757c4; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe3c81e22d4bfaaa0246f5d01a1d96ad0022d499bd76c0223b82dc475d23757c4

namespace PerfectPower.SOEModelPackets
def obs210 := PerfectPower.CheckedSOE.Pe3c81e22d4bfaaa0246f5d01a1d96ad0022d499bd76c0223b82dc475d23757c4.obs
def step210 := PerfectPower.CheckedSOE.Pe3c81e22d4bfaaa0246f5d01a1d96ad0022d499bd76c0223b82dc475d23757c4.step
def q210 := PerfectPower.CheckedSOE.Pe3c81e22d4bfaaa0246f5d01a1d96ad0022d499bd76c0223b82dc475d23757c4.q
def out210 := PerfectPower.CheckedSOE.Pe3c81e22d4bfaaa0246f5d01a1d96ad0022d499bd76c0223b82dc475d23757c4.out
def target210 := PerfectPower.CheckedSOE.Pe3c81e22d4bfaaa0246f5d01a1d96ad0022d499bd76c0223b82dc475d23757c4.target
theorem complete210 (s t : Fin 2) : SOESemantics.Equivalent step210 obs210 s t ↔ q210 s = q210 t := PerfectPower.CheckedSOE.Pe3c81e22d4bfaaa0246f5d01a1d96ad0022d499bd76c0223b82dc475d23757c4.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P9784f3eddb7ec2fde194884d61f6a42d862062018837b263cfe7d9c381d44517
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 9784f3eddb7ec2fde194884d61f6a42d862062018837b263cfe7d9c381d44517; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P9784f3eddb7ec2fde194884d61f6a42d862062018837b263cfe7d9c381d44517

namespace PerfectPower.SOEModelPackets
def obs211 := PerfectPower.CheckedSOE.P9784f3eddb7ec2fde194884d61f6a42d862062018837b263cfe7d9c381d44517.obs
def step211 := PerfectPower.CheckedSOE.P9784f3eddb7ec2fde194884d61f6a42d862062018837b263cfe7d9c381d44517.step
def q211 := PerfectPower.CheckedSOE.P9784f3eddb7ec2fde194884d61f6a42d862062018837b263cfe7d9c381d44517.q
def out211 := PerfectPower.CheckedSOE.P9784f3eddb7ec2fde194884d61f6a42d862062018837b263cfe7d9c381d44517.out
def target211 := PerfectPower.CheckedSOE.P9784f3eddb7ec2fde194884d61f6a42d862062018837b263cfe7d9c381d44517.target
theorem complete211 (s t : Fin 2) : SOESemantics.Equivalent step211 obs211 s t ↔ q211 s = q211 t := PerfectPower.CheckedSOE.P9784f3eddb7ec2fde194884d61f6a42d862062018837b263cfe7d9c381d44517.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P980c2adca0798139eef84edf77f547be799a9d3de40e187b28e966dbbcaa21e0
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 980c2adca0798139eef84edf77f547be799a9d3de40e187b28e966dbbcaa21e0; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P980c2adca0798139eef84edf77f547be799a9d3de40e187b28e966dbbcaa21e0

namespace PerfectPower.SOEModelPackets
def obs212 := PerfectPower.CheckedSOE.P980c2adca0798139eef84edf77f547be799a9d3de40e187b28e966dbbcaa21e0.obs
def step212 := PerfectPower.CheckedSOE.P980c2adca0798139eef84edf77f547be799a9d3de40e187b28e966dbbcaa21e0.step
def q212 := PerfectPower.CheckedSOE.P980c2adca0798139eef84edf77f547be799a9d3de40e187b28e966dbbcaa21e0.q
def out212 := PerfectPower.CheckedSOE.P980c2adca0798139eef84edf77f547be799a9d3de40e187b28e966dbbcaa21e0.out
def target212 := PerfectPower.CheckedSOE.P980c2adca0798139eef84edf77f547be799a9d3de40e187b28e966dbbcaa21e0.target
theorem complete212 (s t : Fin 2) : SOESemantics.Equivalent step212 obs212 s t ↔ q212 s = q212 t := PerfectPower.CheckedSOE.P980c2adca0798139eef84edf77f547be799a9d3de40e187b28e966dbbcaa21e0.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P40c030ea352aa09007d0814e459243171cf27de919394dc0ca95a525a255941e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 40c030ea352aa09007d0814e459243171cf27de919394dc0ca95a525a255941e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P40c030ea352aa09007d0814e459243171cf27de919394dc0ca95a525a255941e

namespace PerfectPower.SOEModelPackets
def obs213 := PerfectPower.CheckedSOE.P40c030ea352aa09007d0814e459243171cf27de919394dc0ca95a525a255941e.obs
def step213 := PerfectPower.CheckedSOE.P40c030ea352aa09007d0814e459243171cf27de919394dc0ca95a525a255941e.step
def q213 := PerfectPower.CheckedSOE.P40c030ea352aa09007d0814e459243171cf27de919394dc0ca95a525a255941e.q
def out213 := PerfectPower.CheckedSOE.P40c030ea352aa09007d0814e459243171cf27de919394dc0ca95a525a255941e.out
def target213 := PerfectPower.CheckedSOE.P40c030ea352aa09007d0814e459243171cf27de919394dc0ca95a525a255941e.target
theorem complete213 (s t : Fin 2) : SOESemantics.Equivalent step213 obs213 s t ↔ q213 s = q213 t := PerfectPower.CheckedSOE.P40c030ea352aa09007d0814e459243171cf27de919394dc0ca95a525a255941e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P8445de5c29b16a751314b15c9cc62c94cd47dcbc66f11dbbf2add845ebaacde6
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 8445de5c29b16a751314b15c9cc62c94cd47dcbc66f11dbbf2add845ebaacde6; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P8445de5c29b16a751314b15c9cc62c94cd47dcbc66f11dbbf2add845ebaacde6

namespace PerfectPower.SOEModelPackets
def obs214 := PerfectPower.CheckedSOE.P8445de5c29b16a751314b15c9cc62c94cd47dcbc66f11dbbf2add845ebaacde6.obs
def step214 := PerfectPower.CheckedSOE.P8445de5c29b16a751314b15c9cc62c94cd47dcbc66f11dbbf2add845ebaacde6.step
def q214 := PerfectPower.CheckedSOE.P8445de5c29b16a751314b15c9cc62c94cd47dcbc66f11dbbf2add845ebaacde6.q
def out214 := PerfectPower.CheckedSOE.P8445de5c29b16a751314b15c9cc62c94cd47dcbc66f11dbbf2add845ebaacde6.out
def target214 := PerfectPower.CheckedSOE.P8445de5c29b16a751314b15c9cc62c94cd47dcbc66f11dbbf2add845ebaacde6.target
theorem complete214 (s t : Fin 2) : SOESemantics.Equivalent step214 obs214 s t ↔ q214 s = q214 t := PerfectPower.CheckedSOE.P8445de5c29b16a751314b15c9cc62c94cd47dcbc66f11dbbf2add845ebaacde6.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P5f570fc809374715c75e5ecef8444fa0fd0841fdf09f753fdbf2a13c3425e582
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 5f570fc809374715c75e5ecef8444fa0fd0841fdf09f753fdbf2a13c3425e582; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P5f570fc809374715c75e5ecef8444fa0fd0841fdf09f753fdbf2a13c3425e582

namespace PerfectPower.SOEModelPackets
def obs215 := PerfectPower.CheckedSOE.P5f570fc809374715c75e5ecef8444fa0fd0841fdf09f753fdbf2a13c3425e582.obs
def step215 := PerfectPower.CheckedSOE.P5f570fc809374715c75e5ecef8444fa0fd0841fdf09f753fdbf2a13c3425e582.step
def q215 := PerfectPower.CheckedSOE.P5f570fc809374715c75e5ecef8444fa0fd0841fdf09f753fdbf2a13c3425e582.q
def out215 := PerfectPower.CheckedSOE.P5f570fc809374715c75e5ecef8444fa0fd0841fdf09f753fdbf2a13c3425e582.out
def target215 := PerfectPower.CheckedSOE.P5f570fc809374715c75e5ecef8444fa0fd0841fdf09f753fdbf2a13c3425e582.target
theorem complete215 (s t : Fin 2) : SOESemantics.Equivalent step215 obs215 s t ↔ q215 s = q215 t := PerfectPower.CheckedSOE.P5f570fc809374715c75e5ecef8444fa0fd0841fdf09f753fdbf2a13c3425e582.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P096a62dd8413158811a9148db8721884b87da7db453922931060f106e5663a4c
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 096a62dd8413158811a9148db8721884b87da7db453922931060f106e5663a4c; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P096a62dd8413158811a9148db8721884b87da7db453922931060f106e5663a4c

namespace PerfectPower.SOEModelPackets
def obs216 := PerfectPower.CheckedSOE.P096a62dd8413158811a9148db8721884b87da7db453922931060f106e5663a4c.obs
def step216 := PerfectPower.CheckedSOE.P096a62dd8413158811a9148db8721884b87da7db453922931060f106e5663a4c.step
def q216 := PerfectPower.CheckedSOE.P096a62dd8413158811a9148db8721884b87da7db453922931060f106e5663a4c.q
def out216 := PerfectPower.CheckedSOE.P096a62dd8413158811a9148db8721884b87da7db453922931060f106e5663a4c.out
def target216 := PerfectPower.CheckedSOE.P096a62dd8413158811a9148db8721884b87da7db453922931060f106e5663a4c.target
theorem complete216 (s t : Fin 2) : SOESemantics.Equivalent step216 obs216 s t ↔ q216 s = q216 t := PerfectPower.CheckedSOE.P096a62dd8413158811a9148db8721884b87da7db453922931060f106e5663a4c.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb6a777fc4b9bce007ab683c6ac52f317891729995cbb68bcc0af580e1c635d36
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b6a777fc4b9bce007ab683c6ac52f317891729995cbb68bcc0af580e1c635d36; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb6a777fc4b9bce007ab683c6ac52f317891729995cbb68bcc0af580e1c635d36

namespace PerfectPower.SOEModelPackets
def obs217 := PerfectPower.CheckedSOE.Pb6a777fc4b9bce007ab683c6ac52f317891729995cbb68bcc0af580e1c635d36.obs
def step217 := PerfectPower.CheckedSOE.Pb6a777fc4b9bce007ab683c6ac52f317891729995cbb68bcc0af580e1c635d36.step
def q217 := PerfectPower.CheckedSOE.Pb6a777fc4b9bce007ab683c6ac52f317891729995cbb68bcc0af580e1c635d36.q
def out217 := PerfectPower.CheckedSOE.Pb6a777fc4b9bce007ab683c6ac52f317891729995cbb68bcc0af580e1c635d36.out
def target217 := PerfectPower.CheckedSOE.Pb6a777fc4b9bce007ab683c6ac52f317891729995cbb68bcc0af580e1c635d36.target
theorem complete217 (s t : Fin 2) : SOESemantics.Equivalent step217 obs217 s t ↔ q217 s = q217 t := PerfectPower.CheckedSOE.Pb6a777fc4b9bce007ab683c6ac52f317891729995cbb68bcc0af580e1c635d36.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbd7edac3a41626748701fefda6d851ddece0fc00d78bd202fa5e3b878e156d87
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: bd7edac3a41626748701fefda6d851ddece0fc00d78bd202fa5e3b878e156d87; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbd7edac3a41626748701fefda6d851ddece0fc00d78bd202fa5e3b878e156d87

namespace PerfectPower.SOEModelPackets
def obs218 := PerfectPower.CheckedSOE.Pbd7edac3a41626748701fefda6d851ddece0fc00d78bd202fa5e3b878e156d87.obs
def step218 := PerfectPower.CheckedSOE.Pbd7edac3a41626748701fefda6d851ddece0fc00d78bd202fa5e3b878e156d87.step
def q218 := PerfectPower.CheckedSOE.Pbd7edac3a41626748701fefda6d851ddece0fc00d78bd202fa5e3b878e156d87.q
def out218 := PerfectPower.CheckedSOE.Pbd7edac3a41626748701fefda6d851ddece0fc00d78bd202fa5e3b878e156d87.out
def target218 := PerfectPower.CheckedSOE.Pbd7edac3a41626748701fefda6d851ddece0fc00d78bd202fa5e3b878e156d87.target
theorem complete218 (s t : Fin 2) : SOESemantics.Equivalent step218 obs218 s t ↔ q218 s = q218 t := PerfectPower.CheckedSOE.Pbd7edac3a41626748701fefda6d851ddece0fc00d78bd202fa5e3b878e156d87.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pcc1cc7d70b7d24d2bb12b040ba1bb7ed7c871cb61ef29cf1fab5c5e757d20f49
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: cc1cc7d70b7d24d2bb12b040ba1bb7ed7c871cb61ef29cf1fab5c5e757d20f49; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pcc1cc7d70b7d24d2bb12b040ba1bb7ed7c871cb61ef29cf1fab5c5e757d20f49

namespace PerfectPower.SOEModelPackets
def obs219 := PerfectPower.CheckedSOE.Pcc1cc7d70b7d24d2bb12b040ba1bb7ed7c871cb61ef29cf1fab5c5e757d20f49.obs
def step219 := PerfectPower.CheckedSOE.Pcc1cc7d70b7d24d2bb12b040ba1bb7ed7c871cb61ef29cf1fab5c5e757d20f49.step
def q219 := PerfectPower.CheckedSOE.Pcc1cc7d70b7d24d2bb12b040ba1bb7ed7c871cb61ef29cf1fab5c5e757d20f49.q
def out219 := PerfectPower.CheckedSOE.Pcc1cc7d70b7d24d2bb12b040ba1bb7ed7c871cb61ef29cf1fab5c5e757d20f49.out
def target219 := PerfectPower.CheckedSOE.Pcc1cc7d70b7d24d2bb12b040ba1bb7ed7c871cb61ef29cf1fab5c5e757d20f49.target
theorem complete219 (s t : Fin 2) : SOESemantics.Equivalent step219 obs219 s t ↔ q219 s = q219 t := PerfectPower.CheckedSOE.Pcc1cc7d70b7d24d2bb12b040ba1bb7ed7c871cb61ef29cf1fab5c5e757d20f49.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pfe6229dd31be9dd8174d690a8de6f25ebe6184946be84620efe87755dc010975
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: fe6229dd31be9dd8174d690a8de6f25ebe6184946be84620efe87755dc010975; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pfe6229dd31be9dd8174d690a8de6f25ebe6184946be84620efe87755dc010975

namespace PerfectPower.SOEModelPackets
def obs220 := PerfectPower.CheckedSOE.Pfe6229dd31be9dd8174d690a8de6f25ebe6184946be84620efe87755dc010975.obs
def step220 := PerfectPower.CheckedSOE.Pfe6229dd31be9dd8174d690a8de6f25ebe6184946be84620efe87755dc010975.step
def q220 := PerfectPower.CheckedSOE.Pfe6229dd31be9dd8174d690a8de6f25ebe6184946be84620efe87755dc010975.q
def out220 := PerfectPower.CheckedSOE.Pfe6229dd31be9dd8174d690a8de6f25ebe6184946be84620efe87755dc010975.out
def target220 := PerfectPower.CheckedSOE.Pfe6229dd31be9dd8174d690a8de6f25ebe6184946be84620efe87755dc010975.target
theorem complete220 (s t : Fin 2) : SOESemantics.Equivalent step220 obs220 s t ↔ q220 s = q220 t := PerfectPower.CheckedSOE.Pfe6229dd31be9dd8174d690a8de6f25ebe6184946be84620efe87755dc010975.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb670b381922c4231324ca718b3781a07e5f0c6f1398bcf022e1a87ac07bb1b0a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b670b381922c4231324ca718b3781a07e5f0c6f1398bcf022e1a87ac07bb1b0a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb670b381922c4231324ca718b3781a07e5f0c6f1398bcf022e1a87ac07bb1b0a

namespace PerfectPower.SOEModelPackets
def obs221 := PerfectPower.CheckedSOE.Pb670b381922c4231324ca718b3781a07e5f0c6f1398bcf022e1a87ac07bb1b0a.obs
def step221 := PerfectPower.CheckedSOE.Pb670b381922c4231324ca718b3781a07e5f0c6f1398bcf022e1a87ac07bb1b0a.step
def q221 := PerfectPower.CheckedSOE.Pb670b381922c4231324ca718b3781a07e5f0c6f1398bcf022e1a87ac07bb1b0a.q
def out221 := PerfectPower.CheckedSOE.Pb670b381922c4231324ca718b3781a07e5f0c6f1398bcf022e1a87ac07bb1b0a.out
def target221 := PerfectPower.CheckedSOE.Pb670b381922c4231324ca718b3781a07e5f0c6f1398bcf022e1a87ac07bb1b0a.target
theorem complete221 (s t : Fin 2) : SOESemantics.Equivalent step221 obs221 s t ↔ q221 s = q221 t := PerfectPower.CheckedSOE.Pb670b381922c4231324ca718b3781a07e5f0c6f1398bcf022e1a87ac07bb1b0a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd7c18516480126668fce3a5611a15105468b94490978e95a85f1a7061e715855
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d7c18516480126668fce3a5611a15105468b94490978e95a85f1a7061e715855; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd7c18516480126668fce3a5611a15105468b94490978e95a85f1a7061e715855

namespace PerfectPower.SOEModelPackets
def obs222 := PerfectPower.CheckedSOE.Pd7c18516480126668fce3a5611a15105468b94490978e95a85f1a7061e715855.obs
def step222 := PerfectPower.CheckedSOE.Pd7c18516480126668fce3a5611a15105468b94490978e95a85f1a7061e715855.step
def q222 := PerfectPower.CheckedSOE.Pd7c18516480126668fce3a5611a15105468b94490978e95a85f1a7061e715855.q
def out222 := PerfectPower.CheckedSOE.Pd7c18516480126668fce3a5611a15105468b94490978e95a85f1a7061e715855.out
def target222 := PerfectPower.CheckedSOE.Pd7c18516480126668fce3a5611a15105468b94490978e95a85f1a7061e715855.target
theorem complete222 (s t : Fin 2) : SOESemantics.Equivalent step222 obs222 s t ↔ q222 s = q222 t := PerfectPower.CheckedSOE.Pd7c18516480126668fce3a5611a15105468b94490978e95a85f1a7061e715855.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb3aea781cf1cd514b2fa29507ea3dfd12037479e27441caa94875b921550239f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b3aea781cf1cd514b2fa29507ea3dfd12037479e27441caa94875b921550239f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb3aea781cf1cd514b2fa29507ea3dfd12037479e27441caa94875b921550239f

namespace PerfectPower.SOEModelPackets
def obs223 := PerfectPower.CheckedSOE.Pb3aea781cf1cd514b2fa29507ea3dfd12037479e27441caa94875b921550239f.obs
def step223 := PerfectPower.CheckedSOE.Pb3aea781cf1cd514b2fa29507ea3dfd12037479e27441caa94875b921550239f.step
def q223 := PerfectPower.CheckedSOE.Pb3aea781cf1cd514b2fa29507ea3dfd12037479e27441caa94875b921550239f.q
def out223 := PerfectPower.CheckedSOE.Pb3aea781cf1cd514b2fa29507ea3dfd12037479e27441caa94875b921550239f.out
def target223 := PerfectPower.CheckedSOE.Pb3aea781cf1cd514b2fa29507ea3dfd12037479e27441caa94875b921550239f.target
theorem complete223 (s t : Fin 2) : SOESemantics.Equivalent step223 obs223 s t ↔ q223 s = q223 t := PerfectPower.CheckedSOE.Pb3aea781cf1cd514b2fa29507ea3dfd12037479e27441caa94875b921550239f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa79da9b109af909c31a6f91e95f1859cb7b53f445318885e7a0334774a628fe7
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a79da9b109af909c31a6f91e95f1859cb7b53f445318885e7a0334774a628fe7; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa79da9b109af909c31a6f91e95f1859cb7b53f445318885e7a0334774a628fe7

namespace PerfectPower.SOEModelPackets
def obs224 := PerfectPower.CheckedSOE.Pa79da9b109af909c31a6f91e95f1859cb7b53f445318885e7a0334774a628fe7.obs
def step224 := PerfectPower.CheckedSOE.Pa79da9b109af909c31a6f91e95f1859cb7b53f445318885e7a0334774a628fe7.step
def q224 := PerfectPower.CheckedSOE.Pa79da9b109af909c31a6f91e95f1859cb7b53f445318885e7a0334774a628fe7.q
def out224 := PerfectPower.CheckedSOE.Pa79da9b109af909c31a6f91e95f1859cb7b53f445318885e7a0334774a628fe7.out
def target224 := PerfectPower.CheckedSOE.Pa79da9b109af909c31a6f91e95f1859cb7b53f445318885e7a0334774a628fe7.target
theorem complete224 (s t : Fin 2) : SOESemantics.Equivalent step224 obs224 s t ↔ q224 s = q224 t := PerfectPower.CheckedSOE.Pa79da9b109af909c31a6f91e95f1859cb7b53f445318885e7a0334774a628fe7.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4c5cd7589ebb92d8559adb48b033a5a3b6c036ba0558bc15ea5befe80e3256b0
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4c5cd7589ebb92d8559adb48b033a5a3b6c036ba0558bc15ea5befe80e3256b0; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4c5cd7589ebb92d8559adb48b033a5a3b6c036ba0558bc15ea5befe80e3256b0

namespace PerfectPower.SOEModelPackets
def obs225 := PerfectPower.CheckedSOE.P4c5cd7589ebb92d8559adb48b033a5a3b6c036ba0558bc15ea5befe80e3256b0.obs
def step225 := PerfectPower.CheckedSOE.P4c5cd7589ebb92d8559adb48b033a5a3b6c036ba0558bc15ea5befe80e3256b0.step
def q225 := PerfectPower.CheckedSOE.P4c5cd7589ebb92d8559adb48b033a5a3b6c036ba0558bc15ea5befe80e3256b0.q
def out225 := PerfectPower.CheckedSOE.P4c5cd7589ebb92d8559adb48b033a5a3b6c036ba0558bc15ea5befe80e3256b0.out
def target225 := PerfectPower.CheckedSOE.P4c5cd7589ebb92d8559adb48b033a5a3b6c036ba0558bc15ea5befe80e3256b0.target
theorem complete225 (s t : Fin 2) : SOESemantics.Equivalent step225 obs225 s t ↔ q225 s = q225 t := PerfectPower.CheckedSOE.P4c5cd7589ebb92d8559adb48b033a5a3b6c036ba0558bc15ea5befe80e3256b0.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd6dba27f982d6b66952844a727a83ea21dd3df256984c426f2484b1ace3a2de1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d6dba27f982d6b66952844a727a83ea21dd3df256984c426f2484b1ace3a2de1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd6dba27f982d6b66952844a727a83ea21dd3df256984c426f2484b1ace3a2de1

namespace PerfectPower.SOEModelPackets
def obs226 := PerfectPower.CheckedSOE.Pd6dba27f982d6b66952844a727a83ea21dd3df256984c426f2484b1ace3a2de1.obs
def step226 := PerfectPower.CheckedSOE.Pd6dba27f982d6b66952844a727a83ea21dd3df256984c426f2484b1ace3a2de1.step
def q226 := PerfectPower.CheckedSOE.Pd6dba27f982d6b66952844a727a83ea21dd3df256984c426f2484b1ace3a2de1.q
def out226 := PerfectPower.CheckedSOE.Pd6dba27f982d6b66952844a727a83ea21dd3df256984c426f2484b1ace3a2de1.out
def target226 := PerfectPower.CheckedSOE.Pd6dba27f982d6b66952844a727a83ea21dd3df256984c426f2484b1ace3a2de1.target
theorem complete226 (s t : Fin 2) : SOESemantics.Equivalent step226 obs226 s t ↔ q226 s = q226 t := PerfectPower.CheckedSOE.Pd6dba27f982d6b66952844a727a83ea21dd3df256984c426f2484b1ace3a2de1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P1552bdfd0d06e564b892aeb90c27287727f31c88127601a46b6fd0543caedc01
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 1552bdfd0d06e564b892aeb90c27287727f31c88127601a46b6fd0543caedc01; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P1552bdfd0d06e564b892aeb90c27287727f31c88127601a46b6fd0543caedc01

namespace PerfectPower.SOEModelPackets
def obs227 := PerfectPower.CheckedSOE.P1552bdfd0d06e564b892aeb90c27287727f31c88127601a46b6fd0543caedc01.obs
def step227 := PerfectPower.CheckedSOE.P1552bdfd0d06e564b892aeb90c27287727f31c88127601a46b6fd0543caedc01.step
def q227 := PerfectPower.CheckedSOE.P1552bdfd0d06e564b892aeb90c27287727f31c88127601a46b6fd0543caedc01.q
def out227 := PerfectPower.CheckedSOE.P1552bdfd0d06e564b892aeb90c27287727f31c88127601a46b6fd0543caedc01.out
def target227 := PerfectPower.CheckedSOE.P1552bdfd0d06e564b892aeb90c27287727f31c88127601a46b6fd0543caedc01.target
theorem complete227 (s t : Fin 2) : SOESemantics.Equivalent step227 obs227 s t ↔ q227 s = q227 t := PerfectPower.CheckedSOE.P1552bdfd0d06e564b892aeb90c27287727f31c88127601a46b6fd0543caedc01.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbbb4c8323d77320df946adc83feb3d78da70e1e7e11ff33208d88e83fcbb0c60
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: bbb4c8323d77320df946adc83feb3d78da70e1e7e11ff33208d88e83fcbb0c60; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbbb4c8323d77320df946adc83feb3d78da70e1e7e11ff33208d88e83fcbb0c60

namespace PerfectPower.SOEModelPackets
def obs228 := PerfectPower.CheckedSOE.Pbbb4c8323d77320df946adc83feb3d78da70e1e7e11ff33208d88e83fcbb0c60.obs
def step228 := PerfectPower.CheckedSOE.Pbbb4c8323d77320df946adc83feb3d78da70e1e7e11ff33208d88e83fcbb0c60.step
def q228 := PerfectPower.CheckedSOE.Pbbb4c8323d77320df946adc83feb3d78da70e1e7e11ff33208d88e83fcbb0c60.q
def out228 := PerfectPower.CheckedSOE.Pbbb4c8323d77320df946adc83feb3d78da70e1e7e11ff33208d88e83fcbb0c60.out
def target228 := PerfectPower.CheckedSOE.Pbbb4c8323d77320df946adc83feb3d78da70e1e7e11ff33208d88e83fcbb0c60.target
theorem complete228 (s t : Fin 2) : SOESemantics.Equivalent step228 obs228 s t ↔ q228 s = q228 t := PerfectPower.CheckedSOE.Pbbb4c8323d77320df946adc83feb3d78da70e1e7e11ff33208d88e83fcbb0c60.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pfbf8c8c13e4e0862f5d82170dde92c3bfa9096e30a30e23197a8e8d54f3f1e1b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: fbf8c8c13e4e0862f5d82170dde92c3bfa9096e30a30e23197a8e8d54f3f1e1b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pfbf8c8c13e4e0862f5d82170dde92c3bfa9096e30a30e23197a8e8d54f3f1e1b

namespace PerfectPower.SOEModelPackets
def obs229 := PerfectPower.CheckedSOE.Pfbf8c8c13e4e0862f5d82170dde92c3bfa9096e30a30e23197a8e8d54f3f1e1b.obs
def step229 := PerfectPower.CheckedSOE.Pfbf8c8c13e4e0862f5d82170dde92c3bfa9096e30a30e23197a8e8d54f3f1e1b.step
def q229 := PerfectPower.CheckedSOE.Pfbf8c8c13e4e0862f5d82170dde92c3bfa9096e30a30e23197a8e8d54f3f1e1b.q
def out229 := PerfectPower.CheckedSOE.Pfbf8c8c13e4e0862f5d82170dde92c3bfa9096e30a30e23197a8e8d54f3f1e1b.out
def target229 := PerfectPower.CheckedSOE.Pfbf8c8c13e4e0862f5d82170dde92c3bfa9096e30a30e23197a8e8d54f3f1e1b.target
theorem complete229 (s t : Fin 2) : SOESemantics.Equivalent step229 obs229 s t ↔ q229 s = q229 t := PerfectPower.CheckedSOE.Pfbf8c8c13e4e0862f5d82170dde92c3bfa9096e30a30e23197a8e8d54f3f1e1b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd44515c59df3fd760947e4a3515aa94cb4227d746aea57351ab9e203aaefb9ad
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d44515c59df3fd760947e4a3515aa94cb4227d746aea57351ab9e203aaefb9ad; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd44515c59df3fd760947e4a3515aa94cb4227d746aea57351ab9e203aaefb9ad

namespace PerfectPower.SOEModelPackets
def obs230 := PerfectPower.CheckedSOE.Pd44515c59df3fd760947e4a3515aa94cb4227d746aea57351ab9e203aaefb9ad.obs
def step230 := PerfectPower.CheckedSOE.Pd44515c59df3fd760947e4a3515aa94cb4227d746aea57351ab9e203aaefb9ad.step
def q230 := PerfectPower.CheckedSOE.Pd44515c59df3fd760947e4a3515aa94cb4227d746aea57351ab9e203aaefb9ad.q
def out230 := PerfectPower.CheckedSOE.Pd44515c59df3fd760947e4a3515aa94cb4227d746aea57351ab9e203aaefb9ad.out
def target230 := PerfectPower.CheckedSOE.Pd44515c59df3fd760947e4a3515aa94cb4227d746aea57351ab9e203aaefb9ad.target
theorem complete230 (s t : Fin 2) : SOESemantics.Equivalent step230 obs230 s t ↔ q230 s = q230 t := PerfectPower.CheckedSOE.Pd44515c59df3fd760947e4a3515aa94cb4227d746aea57351ab9e203aaefb9ad.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P8ea77d0399df155c3f9a34762ecc274991f6b5c3febe9325805788af21096621
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 8ea77d0399df155c3f9a34762ecc274991f6b5c3febe9325805788af21096621; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P8ea77d0399df155c3f9a34762ecc274991f6b5c3febe9325805788af21096621

namespace PerfectPower.SOEModelPackets
def obs231 := PerfectPower.CheckedSOE.P8ea77d0399df155c3f9a34762ecc274991f6b5c3febe9325805788af21096621.obs
def step231 := PerfectPower.CheckedSOE.P8ea77d0399df155c3f9a34762ecc274991f6b5c3febe9325805788af21096621.step
def q231 := PerfectPower.CheckedSOE.P8ea77d0399df155c3f9a34762ecc274991f6b5c3febe9325805788af21096621.q
def out231 := PerfectPower.CheckedSOE.P8ea77d0399df155c3f9a34762ecc274991f6b5c3febe9325805788af21096621.out
def target231 := PerfectPower.CheckedSOE.P8ea77d0399df155c3f9a34762ecc274991f6b5c3febe9325805788af21096621.target
theorem complete231 (s t : Fin 2) : SOESemantics.Equivalent step231 obs231 s t ↔ q231 s = q231 t := PerfectPower.CheckedSOE.P8ea77d0399df155c3f9a34762ecc274991f6b5c3febe9325805788af21096621.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pfe3c37fe4df80184652d4965e7dd11781050eb346fe37566127ead51d1f1f74f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: fe3c37fe4df80184652d4965e7dd11781050eb346fe37566127ead51d1f1f74f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pfe3c37fe4df80184652d4965e7dd11781050eb346fe37566127ead51d1f1f74f

namespace PerfectPower.SOEModelPackets
def obs232 := PerfectPower.CheckedSOE.Pfe3c37fe4df80184652d4965e7dd11781050eb346fe37566127ead51d1f1f74f.obs
def step232 := PerfectPower.CheckedSOE.Pfe3c37fe4df80184652d4965e7dd11781050eb346fe37566127ead51d1f1f74f.step
def q232 := PerfectPower.CheckedSOE.Pfe3c37fe4df80184652d4965e7dd11781050eb346fe37566127ead51d1f1f74f.q
def out232 := PerfectPower.CheckedSOE.Pfe3c37fe4df80184652d4965e7dd11781050eb346fe37566127ead51d1f1f74f.out
def target232 := PerfectPower.CheckedSOE.Pfe3c37fe4df80184652d4965e7dd11781050eb346fe37566127ead51d1f1f74f.target
theorem complete232 (s t : Fin 2) : SOESemantics.Equivalent step232 obs232 s t ↔ q232 s = q232 t := PerfectPower.CheckedSOE.Pfe3c37fe4df80184652d4965e7dd11781050eb346fe37566127ead51d1f1f74f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb444c1fcefd4750ed061c387d69572527457b26cc665ec8a5687fb61a7008837
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b444c1fcefd4750ed061c387d69572527457b26cc665ec8a5687fb61a7008837; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb444c1fcefd4750ed061c387d69572527457b26cc665ec8a5687fb61a7008837

namespace PerfectPower.SOEModelPackets
def obs233 := PerfectPower.CheckedSOE.Pb444c1fcefd4750ed061c387d69572527457b26cc665ec8a5687fb61a7008837.obs
def step233 := PerfectPower.CheckedSOE.Pb444c1fcefd4750ed061c387d69572527457b26cc665ec8a5687fb61a7008837.step
def q233 := PerfectPower.CheckedSOE.Pb444c1fcefd4750ed061c387d69572527457b26cc665ec8a5687fb61a7008837.q
def out233 := PerfectPower.CheckedSOE.Pb444c1fcefd4750ed061c387d69572527457b26cc665ec8a5687fb61a7008837.out
def target233 := PerfectPower.CheckedSOE.Pb444c1fcefd4750ed061c387d69572527457b26cc665ec8a5687fb61a7008837.target
theorem complete233 (s t : Fin 2) : SOESemantics.Equivalent step233 obs233 s t ↔ q233 s = q233 t := PerfectPower.CheckedSOE.Pb444c1fcefd4750ed061c387d69572527457b26cc665ec8a5687fb61a7008837.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pcaa4addfc779e8b9773d6ffcb2f95dd3613c145319dea4efb177dbf9e522d0bb
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: caa4addfc779e8b9773d6ffcb2f95dd3613c145319dea4efb177dbf9e522d0bb; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pcaa4addfc779e8b9773d6ffcb2f95dd3613c145319dea4efb177dbf9e522d0bb

namespace PerfectPower.SOEModelPackets
def obs234 := PerfectPower.CheckedSOE.Pcaa4addfc779e8b9773d6ffcb2f95dd3613c145319dea4efb177dbf9e522d0bb.obs
def step234 := PerfectPower.CheckedSOE.Pcaa4addfc779e8b9773d6ffcb2f95dd3613c145319dea4efb177dbf9e522d0bb.step
def q234 := PerfectPower.CheckedSOE.Pcaa4addfc779e8b9773d6ffcb2f95dd3613c145319dea4efb177dbf9e522d0bb.q
def out234 := PerfectPower.CheckedSOE.Pcaa4addfc779e8b9773d6ffcb2f95dd3613c145319dea4efb177dbf9e522d0bb.out
def target234 := PerfectPower.CheckedSOE.Pcaa4addfc779e8b9773d6ffcb2f95dd3613c145319dea4efb177dbf9e522d0bb.target
theorem complete234 (s t : Fin 2) : SOESemantics.Equivalent step234 obs234 s t ↔ q234 s = q234 t := PerfectPower.CheckedSOE.Pcaa4addfc779e8b9773d6ffcb2f95dd3613c145319dea4efb177dbf9e522d0bb.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pbca317accbdf4447d89765b8b361404ef61a3cdbe40aafc1ee49e9fb1d41eb60
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: bca317accbdf4447d89765b8b361404ef61a3cdbe40aafc1ee49e9fb1d41eb60; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pbca317accbdf4447d89765b8b361404ef61a3cdbe40aafc1ee49e9fb1d41eb60

namespace PerfectPower.SOEModelPackets
def obs235 := PerfectPower.CheckedSOE.Pbca317accbdf4447d89765b8b361404ef61a3cdbe40aafc1ee49e9fb1d41eb60.obs
def step235 := PerfectPower.CheckedSOE.Pbca317accbdf4447d89765b8b361404ef61a3cdbe40aafc1ee49e9fb1d41eb60.step
def q235 := PerfectPower.CheckedSOE.Pbca317accbdf4447d89765b8b361404ef61a3cdbe40aafc1ee49e9fb1d41eb60.q
def out235 := PerfectPower.CheckedSOE.Pbca317accbdf4447d89765b8b361404ef61a3cdbe40aafc1ee49e9fb1d41eb60.out
def target235 := PerfectPower.CheckedSOE.Pbca317accbdf4447d89765b8b361404ef61a3cdbe40aafc1ee49e9fb1d41eb60.target
theorem complete235 (s t : Fin 2) : SOESemantics.Equivalent step235 obs235 s t ↔ q235 s = q235 t := PerfectPower.CheckedSOE.Pbca317accbdf4447d89765b8b361404ef61a3cdbe40aafc1ee49e9fb1d41eb60.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P5e8df229e93d99dc2150928924dbd499c7a22add59ae8e05f0d73e1c203beb6d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 5e8df229e93d99dc2150928924dbd499c7a22add59ae8e05f0d73e1c203beb6d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P5e8df229e93d99dc2150928924dbd499c7a22add59ae8e05f0d73e1c203beb6d

namespace PerfectPower.SOEModelPackets
def obs236 := PerfectPower.CheckedSOE.P5e8df229e93d99dc2150928924dbd499c7a22add59ae8e05f0d73e1c203beb6d.obs
def step236 := PerfectPower.CheckedSOE.P5e8df229e93d99dc2150928924dbd499c7a22add59ae8e05f0d73e1c203beb6d.step
def q236 := PerfectPower.CheckedSOE.P5e8df229e93d99dc2150928924dbd499c7a22add59ae8e05f0d73e1c203beb6d.q
def out236 := PerfectPower.CheckedSOE.P5e8df229e93d99dc2150928924dbd499c7a22add59ae8e05f0d73e1c203beb6d.out
def target236 := PerfectPower.CheckedSOE.P5e8df229e93d99dc2150928924dbd499c7a22add59ae8e05f0d73e1c203beb6d.target
theorem complete236 (s t : Fin 2) : SOESemantics.Equivalent step236 obs236 s t ↔ q236 s = q236 t := PerfectPower.CheckedSOE.P5e8df229e93d99dc2150928924dbd499c7a22add59ae8e05f0d73e1c203beb6d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd19f67c3c7766cc8a627634a71f9514c719f37f0619841a6a9c05e7e2fbe88bd
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d19f67c3c7766cc8a627634a71f9514c719f37f0619841a6a9c05e7e2fbe88bd; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd19f67c3c7766cc8a627634a71f9514c719f37f0619841a6a9c05e7e2fbe88bd

namespace PerfectPower.SOEModelPackets
def obs237 := PerfectPower.CheckedSOE.Pd19f67c3c7766cc8a627634a71f9514c719f37f0619841a6a9c05e7e2fbe88bd.obs
def step237 := PerfectPower.CheckedSOE.Pd19f67c3c7766cc8a627634a71f9514c719f37f0619841a6a9c05e7e2fbe88bd.step
def q237 := PerfectPower.CheckedSOE.Pd19f67c3c7766cc8a627634a71f9514c719f37f0619841a6a9c05e7e2fbe88bd.q
def out237 := PerfectPower.CheckedSOE.Pd19f67c3c7766cc8a627634a71f9514c719f37f0619841a6a9c05e7e2fbe88bd.out
def target237 := PerfectPower.CheckedSOE.Pd19f67c3c7766cc8a627634a71f9514c719f37f0619841a6a9c05e7e2fbe88bd.target
theorem complete237 (s t : Fin 2) : SOESemantics.Equivalent step237 obs237 s t ↔ q237 s = q237 t := PerfectPower.CheckedSOE.Pd19f67c3c7766cc8a627634a71f9514c719f37f0619841a6a9c05e7e2fbe88bd.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb9660cf92f87111bec72dc723ceeea4095a928f17119a5a27f8d90d91259de57
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b9660cf92f87111bec72dc723ceeea4095a928f17119a5a27f8d90d91259de57; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb9660cf92f87111bec72dc723ceeea4095a928f17119a5a27f8d90d91259de57

namespace PerfectPower.SOEModelPackets
def obs238 := PerfectPower.CheckedSOE.Pb9660cf92f87111bec72dc723ceeea4095a928f17119a5a27f8d90d91259de57.obs
def step238 := PerfectPower.CheckedSOE.Pb9660cf92f87111bec72dc723ceeea4095a928f17119a5a27f8d90d91259de57.step
def q238 := PerfectPower.CheckedSOE.Pb9660cf92f87111bec72dc723ceeea4095a928f17119a5a27f8d90d91259de57.q
def out238 := PerfectPower.CheckedSOE.Pb9660cf92f87111bec72dc723ceeea4095a928f17119a5a27f8d90d91259de57.out
def target238 := PerfectPower.CheckedSOE.Pb9660cf92f87111bec72dc723ceeea4095a928f17119a5a27f8d90d91259de57.target
theorem complete238 (s t : Fin 2) : SOESemantics.Equivalent step238 obs238 s t ↔ q238 s = q238 t := PerfectPower.CheckedSOE.Pb9660cf92f87111bec72dc723ceeea4095a928f17119a5a27f8d90d91259de57.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe5558ea540b9f5a956c2ed1cf878ff32af7a2b5522e7930d1329bf57aa0940ae
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e5558ea540b9f5a956c2ed1cf878ff32af7a2b5522e7930d1329bf57aa0940ae; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe5558ea540b9f5a956c2ed1cf878ff32af7a2b5522e7930d1329bf57aa0940ae

namespace PerfectPower.SOEModelPackets
def obs239 := PerfectPower.CheckedSOE.Pe5558ea540b9f5a956c2ed1cf878ff32af7a2b5522e7930d1329bf57aa0940ae.obs
def step239 := PerfectPower.CheckedSOE.Pe5558ea540b9f5a956c2ed1cf878ff32af7a2b5522e7930d1329bf57aa0940ae.step
def q239 := PerfectPower.CheckedSOE.Pe5558ea540b9f5a956c2ed1cf878ff32af7a2b5522e7930d1329bf57aa0940ae.q
def out239 := PerfectPower.CheckedSOE.Pe5558ea540b9f5a956c2ed1cf878ff32af7a2b5522e7930d1329bf57aa0940ae.out
def target239 := PerfectPower.CheckedSOE.Pe5558ea540b9f5a956c2ed1cf878ff32af7a2b5522e7930d1329bf57aa0940ae.target
theorem complete239 (s t : Fin 2) : SOESemantics.Equivalent step239 obs239 s t ↔ q239 s = q239 t := PerfectPower.CheckedSOE.Pe5558ea540b9f5a956c2ed1cf878ff32af7a2b5522e7930d1329bf57aa0940ae.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P8d4fc5515384e3ddd595f029750111f2c56bebb611152d5f4c54474eaefcaed1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 8d4fc5515384e3ddd595f029750111f2c56bebb611152d5f4c54474eaefcaed1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P8d4fc5515384e3ddd595f029750111f2c56bebb611152d5f4c54474eaefcaed1

namespace PerfectPower.SOEModelPackets
def obs240 := PerfectPower.CheckedSOE.P8d4fc5515384e3ddd595f029750111f2c56bebb611152d5f4c54474eaefcaed1.obs
def step240 := PerfectPower.CheckedSOE.P8d4fc5515384e3ddd595f029750111f2c56bebb611152d5f4c54474eaefcaed1.step
def q240 := PerfectPower.CheckedSOE.P8d4fc5515384e3ddd595f029750111f2c56bebb611152d5f4c54474eaefcaed1.q
def out240 := PerfectPower.CheckedSOE.P8d4fc5515384e3ddd595f029750111f2c56bebb611152d5f4c54474eaefcaed1.out
def target240 := PerfectPower.CheckedSOE.P8d4fc5515384e3ddd595f029750111f2c56bebb611152d5f4c54474eaefcaed1.target
theorem complete240 (s t : Fin 2) : SOESemantics.Equivalent step240 obs240 s t ↔ q240 s = q240 t := PerfectPower.CheckedSOE.P8d4fc5515384e3ddd595f029750111f2c56bebb611152d5f4c54474eaefcaed1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6be5b24661c4610d1dbfc9b6865e7857c77e348c5eb3e13dcf9e52f9bfd16adc
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6be5b24661c4610d1dbfc9b6865e7857c77e348c5eb3e13dcf9e52f9bfd16adc; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6be5b24661c4610d1dbfc9b6865e7857c77e348c5eb3e13dcf9e52f9bfd16adc

namespace PerfectPower.SOEModelPackets
def obs241 := PerfectPower.CheckedSOE.P6be5b24661c4610d1dbfc9b6865e7857c77e348c5eb3e13dcf9e52f9bfd16adc.obs
def step241 := PerfectPower.CheckedSOE.P6be5b24661c4610d1dbfc9b6865e7857c77e348c5eb3e13dcf9e52f9bfd16adc.step
def q241 := PerfectPower.CheckedSOE.P6be5b24661c4610d1dbfc9b6865e7857c77e348c5eb3e13dcf9e52f9bfd16adc.q
def out241 := PerfectPower.CheckedSOE.P6be5b24661c4610d1dbfc9b6865e7857c77e348c5eb3e13dcf9e52f9bfd16adc.out
def target241 := PerfectPower.CheckedSOE.P6be5b24661c4610d1dbfc9b6865e7857c77e348c5eb3e13dcf9e52f9bfd16adc.target
theorem complete241 (s t : Fin 2) : SOESemantics.Equivalent step241 obs241 s t ↔ q241 s = q241 t := PerfectPower.CheckedSOE.P6be5b24661c4610d1dbfc9b6865e7857c77e348c5eb3e13dcf9e52f9bfd16adc.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P7b571d299e86683721c01085f5a218a9615ba2587c4ec8c9f0e734dba5b3b6e3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 7b571d299e86683721c01085f5a218a9615ba2587c4ec8c9f0e734dba5b3b6e3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 2 := if s = 0 then 1 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([]) else (if j = 0 then [] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P7b571d299e86683721c01085f5a218a9615ba2587c4ec8c9f0e734dba5b3b6e3

namespace PerfectPower.SOEModelPackets
def obs242 := PerfectPower.CheckedSOE.P7b571d299e86683721c01085f5a218a9615ba2587c4ec8c9f0e734dba5b3b6e3.obs
def step242 := PerfectPower.CheckedSOE.P7b571d299e86683721c01085f5a218a9615ba2587c4ec8c9f0e734dba5b3b6e3.step
def q242 := PerfectPower.CheckedSOE.P7b571d299e86683721c01085f5a218a9615ba2587c4ec8c9f0e734dba5b3b6e3.q
def out242 := PerfectPower.CheckedSOE.P7b571d299e86683721c01085f5a218a9615ba2587c4ec8c9f0e734dba5b3b6e3.out
def target242 := PerfectPower.CheckedSOE.P7b571d299e86683721c01085f5a218a9615ba2587c4ec8c9f0e734dba5b3b6e3.target
theorem complete242 (s t : Fin 2) : SOESemantics.Equivalent step242 obs242 s t ↔ q242 s = q242 t := PerfectPower.CheckedSOE.P7b571d299e86683721c01085f5a218a9615ba2587c4ec8c9f0e734dba5b3b6e3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P87d8e4fe08eda1864c978937256a72dcb8709abba3627c3bed83ffbcf451a39f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 87d8e4fe08eda1864c978937256a72dcb8709abba3627c3bed83ffbcf451a39f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P87d8e4fe08eda1864c978937256a72dcb8709abba3627c3bed83ffbcf451a39f

namespace PerfectPower.SOEModelPackets
def obs243 := PerfectPower.CheckedSOE.P87d8e4fe08eda1864c978937256a72dcb8709abba3627c3bed83ffbcf451a39f.obs
def step243 := PerfectPower.CheckedSOE.P87d8e4fe08eda1864c978937256a72dcb8709abba3627c3bed83ffbcf451a39f.step
def q243 := PerfectPower.CheckedSOE.P87d8e4fe08eda1864c978937256a72dcb8709abba3627c3bed83ffbcf451a39f.q
def out243 := PerfectPower.CheckedSOE.P87d8e4fe08eda1864c978937256a72dcb8709abba3627c3bed83ffbcf451a39f.out
def target243 := PerfectPower.CheckedSOE.P87d8e4fe08eda1864c978937256a72dcb8709abba3627c3bed83ffbcf451a39f.target
theorem complete243 (s t : Fin 2) : SOESemantics.Equivalent step243 obs243 s t ↔ q243 s = q243 t := PerfectPower.CheckedSOE.P87d8e4fe08eda1864c978937256a72dcb8709abba3627c3bed83ffbcf451a39f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P902f5aa36ea510f419f8c8db2f4d443f9c6f3c74673e2b85367345b4fb65ba28
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 902f5aa36ea510f419f8c8db2f4d443f9c6f3c74673e2b85367345b4fb65ba28; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P902f5aa36ea510f419f8c8db2f4d443f9c6f3c74673e2b85367345b4fb65ba28

namespace PerfectPower.SOEModelPackets
def obs244 := PerfectPower.CheckedSOE.P902f5aa36ea510f419f8c8db2f4d443f9c6f3c74673e2b85367345b4fb65ba28.obs
def step244 := PerfectPower.CheckedSOE.P902f5aa36ea510f419f8c8db2f4d443f9c6f3c74673e2b85367345b4fb65ba28.step
def q244 := PerfectPower.CheckedSOE.P902f5aa36ea510f419f8c8db2f4d443f9c6f3c74673e2b85367345b4fb65ba28.q
def out244 := PerfectPower.CheckedSOE.P902f5aa36ea510f419f8c8db2f4d443f9c6f3c74673e2b85367345b4fb65ba28.out
def target244 := PerfectPower.CheckedSOE.P902f5aa36ea510f419f8c8db2f4d443f9c6f3c74673e2b85367345b4fb65ba28.target
theorem complete244 (s t : Fin 2) : SOESemantics.Equivalent step244 obs244 s t ↔ q244 s = q244 t := PerfectPower.CheckedSOE.P902f5aa36ea510f419f8c8db2f4d443f9c6f3c74673e2b85367345b4fb65ba28.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P89442819d9c372c5796bb4ac2fdac7541cbf7751ddc8a94b6afb034159647e7f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 89442819d9c372c5796bb4ac2fdac7541cbf7751ddc8a94b6afb034159647e7f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P89442819d9c372c5796bb4ac2fdac7541cbf7751ddc8a94b6afb034159647e7f

namespace PerfectPower.SOEModelPackets
def obs245 := PerfectPower.CheckedSOE.P89442819d9c372c5796bb4ac2fdac7541cbf7751ddc8a94b6afb034159647e7f.obs
def step245 := PerfectPower.CheckedSOE.P89442819d9c372c5796bb4ac2fdac7541cbf7751ddc8a94b6afb034159647e7f.step
def q245 := PerfectPower.CheckedSOE.P89442819d9c372c5796bb4ac2fdac7541cbf7751ddc8a94b6afb034159647e7f.q
def out245 := PerfectPower.CheckedSOE.P89442819d9c372c5796bb4ac2fdac7541cbf7751ddc8a94b6afb034159647e7f.out
def target245 := PerfectPower.CheckedSOE.P89442819d9c372c5796bb4ac2fdac7541cbf7751ddc8a94b6afb034159647e7f.target
theorem complete245 (s t : Fin 2) : SOESemantics.Equivalent step245 obs245 s t ↔ q245 s = q245 t := PerfectPower.CheckedSOE.P89442819d9c372c5796bb4ac2fdac7541cbf7751ddc8a94b6afb034159647e7f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc1d64c7f2fd892d09ba88885ebf2919973e726fb6f428311881449e8d8ee2461
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c1d64c7f2fd892d09ba88885ebf2919973e726fb6f428311881449e8d8ee2461; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc1d64c7f2fd892d09ba88885ebf2919973e726fb6f428311881449e8d8ee2461

namespace PerfectPower.SOEModelPackets
def obs246 := PerfectPower.CheckedSOE.Pc1d64c7f2fd892d09ba88885ebf2919973e726fb6f428311881449e8d8ee2461.obs
def step246 := PerfectPower.CheckedSOE.Pc1d64c7f2fd892d09ba88885ebf2919973e726fb6f428311881449e8d8ee2461.step
def q246 := PerfectPower.CheckedSOE.Pc1d64c7f2fd892d09ba88885ebf2919973e726fb6f428311881449e8d8ee2461.q
def out246 := PerfectPower.CheckedSOE.Pc1d64c7f2fd892d09ba88885ebf2919973e726fb6f428311881449e8d8ee2461.out
def target246 := PerfectPower.CheckedSOE.Pc1d64c7f2fd892d09ba88885ebf2919973e726fb6f428311881449e8d8ee2461.target
theorem complete246 (s t : Fin 2) : SOESemantics.Equivalent step246 obs246 s t ↔ q246 s = q246 t := PerfectPower.CheckedSOE.Pc1d64c7f2fd892d09ba88885ebf2919973e726fb6f428311881449e8d8ee2461.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2c26e3404dc400c07eceb829028d40a47698756f12cc3d34dd52ee02b7912039
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2c26e3404dc400c07eceb829028d40a47698756f12cc3d34dd52ee02b7912039; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2c26e3404dc400c07eceb829028d40a47698756f12cc3d34dd52ee02b7912039

namespace PerfectPower.SOEModelPackets
def obs247 := PerfectPower.CheckedSOE.P2c26e3404dc400c07eceb829028d40a47698756f12cc3d34dd52ee02b7912039.obs
def step247 := PerfectPower.CheckedSOE.P2c26e3404dc400c07eceb829028d40a47698756f12cc3d34dd52ee02b7912039.step
def q247 := PerfectPower.CheckedSOE.P2c26e3404dc400c07eceb829028d40a47698756f12cc3d34dd52ee02b7912039.q
def out247 := PerfectPower.CheckedSOE.P2c26e3404dc400c07eceb829028d40a47698756f12cc3d34dd52ee02b7912039.out
def target247 := PerfectPower.CheckedSOE.P2c26e3404dc400c07eceb829028d40a47698756f12cc3d34dd52ee02b7912039.target
theorem complete247 (s t : Fin 2) : SOESemantics.Equivalent step247 obs247 s t ↔ q247 s = q247 t := PerfectPower.CheckedSOE.P2c26e3404dc400c07eceb829028d40a47698756f12cc3d34dd52ee02b7912039.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa19d363edca97a5b20319d343eda447bafe73be4705c8e9a0bc7ee7fb1108fcb
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a19d363edca97a5b20319d343eda447bafe73be4705c8e9a0bc7ee7fb1108fcb; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa19d363edca97a5b20319d343eda447bafe73be4705c8e9a0bc7ee7fb1108fcb

namespace PerfectPower.SOEModelPackets
def obs248 := PerfectPower.CheckedSOE.Pa19d363edca97a5b20319d343eda447bafe73be4705c8e9a0bc7ee7fb1108fcb.obs
def step248 := PerfectPower.CheckedSOE.Pa19d363edca97a5b20319d343eda447bafe73be4705c8e9a0bc7ee7fb1108fcb.step
def q248 := PerfectPower.CheckedSOE.Pa19d363edca97a5b20319d343eda447bafe73be4705c8e9a0bc7ee7fb1108fcb.q
def out248 := PerfectPower.CheckedSOE.Pa19d363edca97a5b20319d343eda447bafe73be4705c8e9a0bc7ee7fb1108fcb.out
def target248 := PerfectPower.CheckedSOE.Pa19d363edca97a5b20319d343eda447bafe73be4705c8e9a0bc7ee7fb1108fcb.target
theorem complete248 (s t : Fin 2) : SOESemantics.Equivalent step248 obs248 s t ↔ q248 s = q248 t := PerfectPower.CheckedSOE.Pa19d363edca97a5b20319d343eda447bafe73be4705c8e9a0bc7ee7fb1108fcb.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc5b86fd5d89f80cc0ad0c0c21d92d720a8d0f6f881e61fd6cc419e2a31ac7666
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c5b86fd5d89f80cc0ad0c0c21d92d720a8d0f6f881e61fd6cc419e2a31ac7666; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc5b86fd5d89f80cc0ad0c0c21d92d720a8d0f6f881e61fd6cc419e2a31ac7666

namespace PerfectPower.SOEModelPackets
def obs249 := PerfectPower.CheckedSOE.Pc5b86fd5d89f80cc0ad0c0c21d92d720a8d0f6f881e61fd6cc419e2a31ac7666.obs
def step249 := PerfectPower.CheckedSOE.Pc5b86fd5d89f80cc0ad0c0c21d92d720a8d0f6f881e61fd6cc419e2a31ac7666.step
def q249 := PerfectPower.CheckedSOE.Pc5b86fd5d89f80cc0ad0c0c21d92d720a8d0f6f881e61fd6cc419e2a31ac7666.q
def out249 := PerfectPower.CheckedSOE.Pc5b86fd5d89f80cc0ad0c0c21d92d720a8d0f6f881e61fd6cc419e2a31ac7666.out
def target249 := PerfectPower.CheckedSOE.Pc5b86fd5d89f80cc0ad0c0c21d92d720a8d0f6f881e61fd6cc419e2a31ac7666.target
theorem complete249 (s t : Fin 2) : SOESemantics.Equivalent step249 obs249 s t ↔ q249 s = q249 t := PerfectPower.CheckedSOE.Pc5b86fd5d89f80cc0ad0c0c21d92d720a8d0f6f881e61fd6cc419e2a31ac7666.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd8f5ebe1ff52a8c200e76e2d7042ffc6e0c825808b6675d1491a96356ce58b1a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d8f5ebe1ff52a8c200e76e2d7042ffc6e0c825808b6675d1491a96356ce58b1a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd8f5ebe1ff52a8c200e76e2d7042ffc6e0c825808b6675d1491a96356ce58b1a

namespace PerfectPower.SOEModelPackets
def obs250 := PerfectPower.CheckedSOE.Pd8f5ebe1ff52a8c200e76e2d7042ffc6e0c825808b6675d1491a96356ce58b1a.obs
def step250 := PerfectPower.CheckedSOE.Pd8f5ebe1ff52a8c200e76e2d7042ffc6e0c825808b6675d1491a96356ce58b1a.step
def q250 := PerfectPower.CheckedSOE.Pd8f5ebe1ff52a8c200e76e2d7042ffc6e0c825808b6675d1491a96356ce58b1a.q
def out250 := PerfectPower.CheckedSOE.Pd8f5ebe1ff52a8c200e76e2d7042ffc6e0c825808b6675d1491a96356ce58b1a.out
def target250 := PerfectPower.CheckedSOE.Pd8f5ebe1ff52a8c200e76e2d7042ffc6e0c825808b6675d1491a96356ce58b1a.target
theorem complete250 (s t : Fin 2) : SOESemantics.Equivalent step250 obs250 s t ↔ q250 s = q250 t := PerfectPower.CheckedSOE.Pd8f5ebe1ff52a8c200e76e2d7042ffc6e0c825808b6675d1491a96356ce58b1a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P95e1d37d21b068885296fc7ceb38b43aa8f19a1dc44e3cafac569370c7d3e5ec
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 95e1d37d21b068885296fc7ceb38b43aa8f19a1dc44e3cafac569370c7d3e5ec; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then none else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P95e1d37d21b068885296fc7ceb38b43aa8f19a1dc44e3cafac569370c7d3e5ec

namespace PerfectPower.SOEModelPackets
def obs251 := PerfectPower.CheckedSOE.P95e1d37d21b068885296fc7ceb38b43aa8f19a1dc44e3cafac569370c7d3e5ec.obs
def step251 := PerfectPower.CheckedSOE.P95e1d37d21b068885296fc7ceb38b43aa8f19a1dc44e3cafac569370c7d3e5ec.step
def q251 := PerfectPower.CheckedSOE.P95e1d37d21b068885296fc7ceb38b43aa8f19a1dc44e3cafac569370c7d3e5ec.q
def out251 := PerfectPower.CheckedSOE.P95e1d37d21b068885296fc7ceb38b43aa8f19a1dc44e3cafac569370c7d3e5ec.out
def target251 := PerfectPower.CheckedSOE.P95e1d37d21b068885296fc7ceb38b43aa8f19a1dc44e3cafac569370c7d3e5ec.target
theorem complete251 (s t : Fin 2) : SOESemantics.Equivalent step251 obs251 s t ↔ q251 s = q251 t := PerfectPower.CheckedSOE.P95e1d37d21b068885296fc7ceb38b43aa8f19a1dc44e3cafac569370c7d3e5ec.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0a4824d7db516a2de4e744bfcdc8076a20e26cfebadfbd7a928bcc0282b38a25
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0a4824d7db516a2de4e744bfcdc8076a20e26cfebadfbd7a928bcc0282b38a25; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0a4824d7db516a2de4e744bfcdc8076a20e26cfebadfbd7a928bcc0282b38a25

namespace PerfectPower.SOEModelPackets
def obs252 := PerfectPower.CheckedSOE.P0a4824d7db516a2de4e744bfcdc8076a20e26cfebadfbd7a928bcc0282b38a25.obs
def step252 := PerfectPower.CheckedSOE.P0a4824d7db516a2de4e744bfcdc8076a20e26cfebadfbd7a928bcc0282b38a25.step
def q252 := PerfectPower.CheckedSOE.P0a4824d7db516a2de4e744bfcdc8076a20e26cfebadfbd7a928bcc0282b38a25.q
def out252 := PerfectPower.CheckedSOE.P0a4824d7db516a2de4e744bfcdc8076a20e26cfebadfbd7a928bcc0282b38a25.out
def target252 := PerfectPower.CheckedSOE.P0a4824d7db516a2de4e744bfcdc8076a20e26cfebadfbd7a928bcc0282b38a25.target
theorem complete252 (s t : Fin 2) : SOESemantics.Equivalent step252 obs252 s t ↔ q252 s = q252 t := PerfectPower.CheckedSOE.P0a4824d7db516a2de4e744bfcdc8076a20e26cfebadfbd7a928bcc0282b38a25.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4f26eaaa6b3076455d32d7fdd189e1b3003ecf375a4a6d437d6416745327e0b9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4f26eaaa6b3076455d32d7fdd189e1b3003ecf375a4a6d437d6416745327e0b9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4f26eaaa6b3076455d32d7fdd189e1b3003ecf375a4a6d437d6416745327e0b9

namespace PerfectPower.SOEModelPackets
def obs253 := PerfectPower.CheckedSOE.P4f26eaaa6b3076455d32d7fdd189e1b3003ecf375a4a6d437d6416745327e0b9.obs
def step253 := PerfectPower.CheckedSOE.P4f26eaaa6b3076455d32d7fdd189e1b3003ecf375a4a6d437d6416745327e0b9.step
def q253 := PerfectPower.CheckedSOE.P4f26eaaa6b3076455d32d7fdd189e1b3003ecf375a4a6d437d6416745327e0b9.q
def out253 := PerfectPower.CheckedSOE.P4f26eaaa6b3076455d32d7fdd189e1b3003ecf375a4a6d437d6416745327e0b9.out
def target253 := PerfectPower.CheckedSOE.P4f26eaaa6b3076455d32d7fdd189e1b3003ecf375a4a6d437d6416745327e0b9.target
theorem complete253 (s t : Fin 2) : SOESemantics.Equivalent step253 obs253 s t ↔ q253 s = q253 t := PerfectPower.CheckedSOE.P4f26eaaa6b3076455d32d7fdd189e1b3003ecf375a4a6d437d6416745327e0b9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6feb596631768b8a8501c65c39af9b934a27b12e9368cc09ae37be0d0a6f60e5
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6feb596631768b8a8501c65c39af9b934a27b12e9368cc09ae37be0d0a6f60e5; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6feb596631768b8a8501c65c39af9b934a27b12e9368cc09ae37be0d0a6f60e5

namespace PerfectPower.SOEModelPackets
def obs254 := PerfectPower.CheckedSOE.P6feb596631768b8a8501c65c39af9b934a27b12e9368cc09ae37be0d0a6f60e5.obs
def step254 := PerfectPower.CheckedSOE.P6feb596631768b8a8501c65c39af9b934a27b12e9368cc09ae37be0d0a6f60e5.step
def q254 := PerfectPower.CheckedSOE.P6feb596631768b8a8501c65c39af9b934a27b12e9368cc09ae37be0d0a6f60e5.q
def out254 := PerfectPower.CheckedSOE.P6feb596631768b8a8501c65c39af9b934a27b12e9368cc09ae37be0d0a6f60e5.out
def target254 := PerfectPower.CheckedSOE.P6feb596631768b8a8501c65c39af9b934a27b12e9368cc09ae37be0d0a6f60e5.target
theorem complete254 (s t : Fin 2) : SOESemantics.Equivalent step254 obs254 s t ↔ q254 s = q254 t := PerfectPower.CheckedSOE.P6feb596631768b8a8501c65c39af9b934a27b12e9368cc09ae37be0d0a6f60e5.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P617a37ecd03587ebb0e4176db57878ddf289ec7a5c9b9c329c0adc8116022725
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 617a37ecd03587ebb0e4176db57878ddf289ec7a5c9b9c329c0adc8116022725; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P617a37ecd03587ebb0e4176db57878ddf289ec7a5c9b9c329c0adc8116022725

namespace PerfectPower.SOEModelPackets
def obs255 := PerfectPower.CheckedSOE.P617a37ecd03587ebb0e4176db57878ddf289ec7a5c9b9c329c0adc8116022725.obs
def step255 := PerfectPower.CheckedSOE.P617a37ecd03587ebb0e4176db57878ddf289ec7a5c9b9c329c0adc8116022725.step
def q255 := PerfectPower.CheckedSOE.P617a37ecd03587ebb0e4176db57878ddf289ec7a5c9b9c329c0adc8116022725.q
def out255 := PerfectPower.CheckedSOE.P617a37ecd03587ebb0e4176db57878ddf289ec7a5c9b9c329c0adc8116022725.out
def target255 := PerfectPower.CheckedSOE.P617a37ecd03587ebb0e4176db57878ddf289ec7a5c9b9c329c0adc8116022725.target
theorem complete255 (s t : Fin 2) : SOESemantics.Equivalent step255 obs255 s t ↔ q255 s = q255 t := PerfectPower.CheckedSOE.P617a37ecd03587ebb0e4176db57878ddf289ec7a5c9b9c329c0adc8116022725.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P7301dc2ff3db1d4592f3aefbb40fc90ba8931eaf418955f15d5f6bfd7f84ffbd
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 7301dc2ff3db1d4592f3aefbb40fc90ba8931eaf418955f15d5f6bfd7f84ffbd; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P7301dc2ff3db1d4592f3aefbb40fc90ba8931eaf418955f15d5f6bfd7f84ffbd

namespace PerfectPower.SOEModelPackets
def obs256 := PerfectPower.CheckedSOE.P7301dc2ff3db1d4592f3aefbb40fc90ba8931eaf418955f15d5f6bfd7f84ffbd.obs
def step256 := PerfectPower.CheckedSOE.P7301dc2ff3db1d4592f3aefbb40fc90ba8931eaf418955f15d5f6bfd7f84ffbd.step
def q256 := PerfectPower.CheckedSOE.P7301dc2ff3db1d4592f3aefbb40fc90ba8931eaf418955f15d5f6bfd7f84ffbd.q
def out256 := PerfectPower.CheckedSOE.P7301dc2ff3db1d4592f3aefbb40fc90ba8931eaf418955f15d5f6bfd7f84ffbd.out
def target256 := PerfectPower.CheckedSOE.P7301dc2ff3db1d4592f3aefbb40fc90ba8931eaf418955f15d5f6bfd7f84ffbd.target
theorem complete256 (s t : Fin 2) : SOESemantics.Equivalent step256 obs256 s t ↔ q256 s = q256 t := PerfectPower.CheckedSOE.P7301dc2ff3db1d4592f3aefbb40fc90ba8931eaf418955f15d5f6bfd7f84ffbd.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Peb44a43f5403d4bb7d7e191605433140b316bf1012dae068ef73c25ff20e8aee
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: eb44a43f5403d4bb7d7e191605433140b316bf1012dae068ef73c25ff20e8aee; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Peb44a43f5403d4bb7d7e191605433140b316bf1012dae068ef73c25ff20e8aee

namespace PerfectPower.SOEModelPackets
def obs257 := PerfectPower.CheckedSOE.Peb44a43f5403d4bb7d7e191605433140b316bf1012dae068ef73c25ff20e8aee.obs
def step257 := PerfectPower.CheckedSOE.Peb44a43f5403d4bb7d7e191605433140b316bf1012dae068ef73c25ff20e8aee.step
def q257 := PerfectPower.CheckedSOE.Peb44a43f5403d4bb7d7e191605433140b316bf1012dae068ef73c25ff20e8aee.q
def out257 := PerfectPower.CheckedSOE.Peb44a43f5403d4bb7d7e191605433140b316bf1012dae068ef73c25ff20e8aee.out
def target257 := PerfectPower.CheckedSOE.Peb44a43f5403d4bb7d7e191605433140b316bf1012dae068ef73c25ff20e8aee.target
theorem complete257 (s t : Fin 2) : SOESemantics.Equivalent step257 obs257 s t ↔ q257 s = q257 t := PerfectPower.CheckedSOE.Peb44a43f5403d4bb7d7e191605433140b316bf1012dae068ef73c25ff20e8aee.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc4e23607fc7fcff9eb569a1c815ba506fac5c49059a53ee2e74d650b2fc4f9c4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c4e23607fc7fcff9eb569a1c815ba506fac5c49059a53ee2e74d650b2fc4f9c4; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc4e23607fc7fcff9eb569a1c815ba506fac5c49059a53ee2e74d650b2fc4f9c4

namespace PerfectPower.SOEModelPackets
def obs258 := PerfectPower.CheckedSOE.Pc4e23607fc7fcff9eb569a1c815ba506fac5c49059a53ee2e74d650b2fc4f9c4.obs
def step258 := PerfectPower.CheckedSOE.Pc4e23607fc7fcff9eb569a1c815ba506fac5c49059a53ee2e74d650b2fc4f9c4.step
def q258 := PerfectPower.CheckedSOE.Pc4e23607fc7fcff9eb569a1c815ba506fac5c49059a53ee2e74d650b2fc4f9c4.q
def out258 := PerfectPower.CheckedSOE.Pc4e23607fc7fcff9eb569a1c815ba506fac5c49059a53ee2e74d650b2fc4f9c4.out
def target258 := PerfectPower.CheckedSOE.Pc4e23607fc7fcff9eb569a1c815ba506fac5c49059a53ee2e74d650b2fc4f9c4.target
theorem complete258 (s t : Fin 2) : SOESemantics.Equivalent step258 obs258 s t ↔ q258 s = q258 t := PerfectPower.CheckedSOE.Pc4e23607fc7fcff9eb569a1c815ba506fac5c49059a53ee2e74d650b2fc4f9c4.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P327217bf92f97d9c70396b17d36f3e3dcf52e47cca462b2435f6f54304cb12b4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 327217bf92f97d9c70396b17d36f3e3dcf52e47cca462b2435f6f54304cb12b4; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P327217bf92f97d9c70396b17d36f3e3dcf52e47cca462b2435f6f54304cb12b4

namespace PerfectPower.SOEModelPackets
def obs259 := PerfectPower.CheckedSOE.P327217bf92f97d9c70396b17d36f3e3dcf52e47cca462b2435f6f54304cb12b4.obs
def step259 := PerfectPower.CheckedSOE.P327217bf92f97d9c70396b17d36f3e3dcf52e47cca462b2435f6f54304cb12b4.step
def q259 := PerfectPower.CheckedSOE.P327217bf92f97d9c70396b17d36f3e3dcf52e47cca462b2435f6f54304cb12b4.q
def out259 := PerfectPower.CheckedSOE.P327217bf92f97d9c70396b17d36f3e3dcf52e47cca462b2435f6f54304cb12b4.out
def target259 := PerfectPower.CheckedSOE.P327217bf92f97d9c70396b17d36f3e3dcf52e47cca462b2435f6f54304cb12b4.target
theorem complete259 (s t : Fin 2) : SOESemantics.Equivalent step259 obs259 s t ↔ q259 s = q259 t := PerfectPower.CheckedSOE.P327217bf92f97d9c70396b17d36f3e3dcf52e47cca462b2435f6f54304cb12b4.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Peed670614de7f0e8c902795593e59b4430ca41b59563e1d7c4d3342042951cf9
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: eed670614de7f0e8c902795593e59b4430ca41b59563e1d7c4d3342042951cf9; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 0) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Peed670614de7f0e8c902795593e59b4430ca41b59563e1d7c4d3342042951cf9

namespace PerfectPower.SOEModelPackets
def obs260 := PerfectPower.CheckedSOE.Peed670614de7f0e8c902795593e59b4430ca41b59563e1d7c4d3342042951cf9.obs
def step260 := PerfectPower.CheckedSOE.Peed670614de7f0e8c902795593e59b4430ca41b59563e1d7c4d3342042951cf9.step
def q260 := PerfectPower.CheckedSOE.Peed670614de7f0e8c902795593e59b4430ca41b59563e1d7c4d3342042951cf9.q
def out260 := PerfectPower.CheckedSOE.Peed670614de7f0e8c902795593e59b4430ca41b59563e1d7c4d3342042951cf9.out
def target260 := PerfectPower.CheckedSOE.Peed670614de7f0e8c902795593e59b4430ca41b59563e1d7c4d3342042951cf9.target
theorem complete260 (s t : Fin 2) : SOESemantics.Equivalent step260 obs260 s t ↔ q260 s = q260 t := PerfectPower.CheckedSOE.Peed670614de7f0e8c902795593e59b4430ca41b59563e1d7c4d3342042951cf9.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc21a23a771dd169ac74b25ff983148a955637df4ba3b8dcbae79cbc72b60aeaa
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c21a23a771dd169ac74b25ff983148a955637df4ba3b8dcbae79cbc72b60aeaa; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc21a23a771dd169ac74b25ff983148a955637df4ba3b8dcbae79cbc72b60aeaa

namespace PerfectPower.SOEModelPackets
def obs261 := PerfectPower.CheckedSOE.Pc21a23a771dd169ac74b25ff983148a955637df4ba3b8dcbae79cbc72b60aeaa.obs
def step261 := PerfectPower.CheckedSOE.Pc21a23a771dd169ac74b25ff983148a955637df4ba3b8dcbae79cbc72b60aeaa.step
def q261 := PerfectPower.CheckedSOE.Pc21a23a771dd169ac74b25ff983148a955637df4ba3b8dcbae79cbc72b60aeaa.q
def out261 := PerfectPower.CheckedSOE.Pc21a23a771dd169ac74b25ff983148a955637df4ba3b8dcbae79cbc72b60aeaa.out
def target261 := PerfectPower.CheckedSOE.Pc21a23a771dd169ac74b25ff983148a955637df4ba3b8dcbae79cbc72b60aeaa.target
theorem complete261 (s t : Fin 2) : SOESemantics.Equivalent step261 obs261 s t ↔ q261 s = q261 t := PerfectPower.CheckedSOE.Pc21a23a771dd169ac74b25ff983148a955637df4ba3b8dcbae79cbc72b60aeaa.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P1e9157507aae8c161a6335509ce8e1a17f002de2f1a7184dd25742aedc6f2f2a
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 1e9157507aae8c161a6335509ce8e1a17f002de2f1a7184dd25742aedc6f2f2a; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P1e9157507aae8c161a6335509ce8e1a17f002de2f1a7184dd25742aedc6f2f2a

namespace PerfectPower.SOEModelPackets
def obs262 := PerfectPower.CheckedSOE.P1e9157507aae8c161a6335509ce8e1a17f002de2f1a7184dd25742aedc6f2f2a.obs
def step262 := PerfectPower.CheckedSOE.P1e9157507aae8c161a6335509ce8e1a17f002de2f1a7184dd25742aedc6f2f2a.step
def q262 := PerfectPower.CheckedSOE.P1e9157507aae8c161a6335509ce8e1a17f002de2f1a7184dd25742aedc6f2f2a.q
def out262 := PerfectPower.CheckedSOE.P1e9157507aae8c161a6335509ce8e1a17f002de2f1a7184dd25742aedc6f2f2a.out
def target262 := PerfectPower.CheckedSOE.P1e9157507aae8c161a6335509ce8e1a17f002de2f1a7184dd25742aedc6f2f2a.target
theorem complete262 (s t : Fin 2) : SOESemantics.Equivalent step262 obs262 s t ↔ q262 s = q262 t := PerfectPower.CheckedSOE.P1e9157507aae8c161a6335509ce8e1a17f002de2f1a7184dd25742aedc6f2f2a.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P324116c0233036906f2d7ab36f7890c5f8468ed3b9cf6d7089da856c4e7e1d28
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 324116c0233036906f2d7ab36f7890c5f8468ed3b9cf6d7089da856c4e7e1d28; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P324116c0233036906f2d7ab36f7890c5f8468ed3b9cf6d7089da856c4e7e1d28

namespace PerfectPower.SOEModelPackets
def obs263 := PerfectPower.CheckedSOE.P324116c0233036906f2d7ab36f7890c5f8468ed3b9cf6d7089da856c4e7e1d28.obs
def step263 := PerfectPower.CheckedSOE.P324116c0233036906f2d7ab36f7890c5f8468ed3b9cf6d7089da856c4e7e1d28.step
def q263 := PerfectPower.CheckedSOE.P324116c0233036906f2d7ab36f7890c5f8468ed3b9cf6d7089da856c4e7e1d28.q
def out263 := PerfectPower.CheckedSOE.P324116c0233036906f2d7ab36f7890c5f8468ed3b9cf6d7089da856c4e7e1d28.out
def target263 := PerfectPower.CheckedSOE.P324116c0233036906f2d7ab36f7890c5f8468ed3b9cf6d7089da856c4e7e1d28.target
theorem complete263 (s t : Fin 2) : SOESemantics.Equivalent step263 obs263 s t ↔ q263 s = q263 t := PerfectPower.CheckedSOE.P324116c0233036906f2d7ab36f7890c5f8468ed3b9cf6d7089da856c4e7e1d28.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb9d08593c66bdfe99ab382a12dec8c0d97377c91617bc445f6f6970851e31a2e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b9d08593c66bdfe99ab382a12dec8c0d97377c91617bc445f6f6970851e31a2e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb9d08593c66bdfe99ab382a12dec8c0d97377c91617bc445f6f6970851e31a2e

namespace PerfectPower.SOEModelPackets
def obs264 := PerfectPower.CheckedSOE.Pb9d08593c66bdfe99ab382a12dec8c0d97377c91617bc445f6f6970851e31a2e.obs
def step264 := PerfectPower.CheckedSOE.Pb9d08593c66bdfe99ab382a12dec8c0d97377c91617bc445f6f6970851e31a2e.step
def q264 := PerfectPower.CheckedSOE.Pb9d08593c66bdfe99ab382a12dec8c0d97377c91617bc445f6f6970851e31a2e.q
def out264 := PerfectPower.CheckedSOE.Pb9d08593c66bdfe99ab382a12dec8c0d97377c91617bc445f6f6970851e31a2e.out
def target264 := PerfectPower.CheckedSOE.Pb9d08593c66bdfe99ab382a12dec8c0d97377c91617bc445f6f6970851e31a2e.target
theorem complete264 (s t : Fin 2) : SOESemantics.Equivalent step264 obs264 s t ↔ q264 s = q264 t := PerfectPower.CheckedSOE.Pb9d08593c66bdfe99ab382a12dec8c0d97377c91617bc445f6f6970851e31a2e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pfab050c0e216912d4c3a7d7ba3b6340ecacb7d6bc89830cbbf698fc40ccef5ae
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: fab050c0e216912d4c3a7d7ba3b6340ecacb7d6bc89830cbbf698fc40ccef5ae; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pfab050c0e216912d4c3a7d7ba3b6340ecacb7d6bc89830cbbf698fc40ccef5ae

namespace PerfectPower.SOEModelPackets
def obs265 := PerfectPower.CheckedSOE.Pfab050c0e216912d4c3a7d7ba3b6340ecacb7d6bc89830cbbf698fc40ccef5ae.obs
def step265 := PerfectPower.CheckedSOE.Pfab050c0e216912d4c3a7d7ba3b6340ecacb7d6bc89830cbbf698fc40ccef5ae.step
def q265 := PerfectPower.CheckedSOE.Pfab050c0e216912d4c3a7d7ba3b6340ecacb7d6bc89830cbbf698fc40ccef5ae.q
def out265 := PerfectPower.CheckedSOE.Pfab050c0e216912d4c3a7d7ba3b6340ecacb7d6bc89830cbbf698fc40ccef5ae.out
def target265 := PerfectPower.CheckedSOE.Pfab050c0e216912d4c3a7d7ba3b6340ecacb7d6bc89830cbbf698fc40ccef5ae.target
theorem complete265 (s t : Fin 2) : SOESemantics.Equivalent step265 obs265 s t ↔ q265 s = q265 t := PerfectPower.CheckedSOE.Pfab050c0e216912d4c3a7d7ba3b6340ecacb7d6bc89830cbbf698fc40ccef5ae.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Ped9c4c5fd4adf17379327a1a8a330422728cd4d144061430833b86b15bfef825
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ed9c4c5fd4adf17379327a1a8a330422728cd4d144061430833b86b15bfef825; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Ped9c4c5fd4adf17379327a1a8a330422728cd4d144061430833b86b15bfef825

namespace PerfectPower.SOEModelPackets
def obs266 := PerfectPower.CheckedSOE.Ped9c4c5fd4adf17379327a1a8a330422728cd4d144061430833b86b15bfef825.obs
def step266 := PerfectPower.CheckedSOE.Ped9c4c5fd4adf17379327a1a8a330422728cd4d144061430833b86b15bfef825.step
def q266 := PerfectPower.CheckedSOE.Ped9c4c5fd4adf17379327a1a8a330422728cd4d144061430833b86b15bfef825.q
def out266 := PerfectPower.CheckedSOE.Ped9c4c5fd4adf17379327a1a8a330422728cd4d144061430833b86b15bfef825.out
def target266 := PerfectPower.CheckedSOE.Ped9c4c5fd4adf17379327a1a8a330422728cd4d144061430833b86b15bfef825.target
theorem complete266 (s t : Fin 2) : SOESemantics.Equivalent step266 obs266 s t ↔ q266 s = q266 t := PerfectPower.CheckedSOE.Ped9c4c5fd4adf17379327a1a8a330422728cd4d144061430833b86b15bfef825.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Peff55742e47625909c8f8f1fe746cebd02b7596625c3706079bf00a9dbcb355d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: eff55742e47625909c8f8f1fe746cebd02b7596625c3706079bf00a9dbcb355d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Peff55742e47625909c8f8f1fe746cebd02b7596625c3706079bf00a9dbcb355d

namespace PerfectPower.SOEModelPackets
def obs267 := PerfectPower.CheckedSOE.Peff55742e47625909c8f8f1fe746cebd02b7596625c3706079bf00a9dbcb355d.obs
def step267 := PerfectPower.CheckedSOE.Peff55742e47625909c8f8f1fe746cebd02b7596625c3706079bf00a9dbcb355d.step
def q267 := PerfectPower.CheckedSOE.Peff55742e47625909c8f8f1fe746cebd02b7596625c3706079bf00a9dbcb355d.q
def out267 := PerfectPower.CheckedSOE.Peff55742e47625909c8f8f1fe746cebd02b7596625c3706079bf00a9dbcb355d.out
def target267 := PerfectPower.CheckedSOE.Peff55742e47625909c8f8f1fe746cebd02b7596625c3706079bf00a9dbcb355d.target
theorem complete267 (s t : Fin 2) : SOESemantics.Equivalent step267 obs267 s t ↔ q267 s = q267 t := PerfectPower.CheckedSOE.Peff55742e47625909c8f8f1fe746cebd02b7596625c3706079bf00a9dbcb355d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P29ba7333b22602bd08e6a74b7b6c0a361d28ebf6233b2ca2c50ad69353e18d52
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 29ba7333b22602bd08e6a74b7b6c0a361d28ebf6233b2ca2c50ad69353e18d52; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P29ba7333b22602bd08e6a74b7b6c0a361d28ebf6233b2ca2c50ad69353e18d52

namespace PerfectPower.SOEModelPackets
def obs268 := PerfectPower.CheckedSOE.P29ba7333b22602bd08e6a74b7b6c0a361d28ebf6233b2ca2c50ad69353e18d52.obs
def step268 := PerfectPower.CheckedSOE.P29ba7333b22602bd08e6a74b7b6c0a361d28ebf6233b2ca2c50ad69353e18d52.step
def q268 := PerfectPower.CheckedSOE.P29ba7333b22602bd08e6a74b7b6c0a361d28ebf6233b2ca2c50ad69353e18d52.q
def out268 := PerfectPower.CheckedSOE.P29ba7333b22602bd08e6a74b7b6c0a361d28ebf6233b2ca2c50ad69353e18d52.out
def target268 := PerfectPower.CheckedSOE.P29ba7333b22602bd08e6a74b7b6c0a361d28ebf6233b2ca2c50ad69353e18d52.target
theorem complete268 (s t : Fin 2) : SOESemantics.Equivalent step268 obs268 s t ↔ q268 s = q268 t := PerfectPower.CheckedSOE.P29ba7333b22602bd08e6a74b7b6c0a361d28ebf6233b2ca2c50ad69353e18d52.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P42cc82622ac87d94462d4df81e609c7ed2313b906cdb958237931ff3b864f724
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 42cc82622ac87d94462d4df81e609c7ed2313b906cdb958237931ff3b864f724; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then none else (some 1) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P42cc82622ac87d94462d4df81e609c7ed2313b906cdb958237931ff3b864f724

namespace PerfectPower.SOEModelPackets
def obs269 := PerfectPower.CheckedSOE.P42cc82622ac87d94462d4df81e609c7ed2313b906cdb958237931ff3b864f724.obs
def step269 := PerfectPower.CheckedSOE.P42cc82622ac87d94462d4df81e609c7ed2313b906cdb958237931ff3b864f724.step
def q269 := PerfectPower.CheckedSOE.P42cc82622ac87d94462d4df81e609c7ed2313b906cdb958237931ff3b864f724.q
def out269 := PerfectPower.CheckedSOE.P42cc82622ac87d94462d4df81e609c7ed2313b906cdb958237931ff3b864f724.out
def target269 := PerfectPower.CheckedSOE.P42cc82622ac87d94462d4df81e609c7ed2313b906cdb958237931ff3b864f724.target
theorem complete269 (s t : Fin 2) : SOESemantics.Equivalent step269 obs269 s t ↔ q269 s = q269 t := PerfectPower.CheckedSOE.P42cc82622ac87d94462d4df81e609c7ed2313b906cdb958237931ff3b864f724.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P5434ae1eec51505a19a9dd650bab373979e468f9a2f8ca1dcba3246532c1f3e7
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 5434ae1eec51505a19a9dd650bab373979e468f9a2f8ca1dcba3246532c1f3e7; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P5434ae1eec51505a19a9dd650bab373979e468f9a2f8ca1dcba3246532c1f3e7

namespace PerfectPower.SOEModelPackets
def obs270 := PerfectPower.CheckedSOE.P5434ae1eec51505a19a9dd650bab373979e468f9a2f8ca1dcba3246532c1f3e7.obs
def step270 := PerfectPower.CheckedSOE.P5434ae1eec51505a19a9dd650bab373979e468f9a2f8ca1dcba3246532c1f3e7.step
def q270 := PerfectPower.CheckedSOE.P5434ae1eec51505a19a9dd650bab373979e468f9a2f8ca1dcba3246532c1f3e7.q
def out270 := PerfectPower.CheckedSOE.P5434ae1eec51505a19a9dd650bab373979e468f9a2f8ca1dcba3246532c1f3e7.out
def target270 := PerfectPower.CheckedSOE.P5434ae1eec51505a19a9dd650bab373979e468f9a2f8ca1dcba3246532c1f3e7.target
theorem complete270 (s t : Fin 2) : SOESemantics.Equivalent step270 obs270 s t ↔ q270 s = q270 t := PerfectPower.CheckedSOE.P5434ae1eec51505a19a9dd650bab373979e468f9a2f8ca1dcba3246532c1f3e7.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P10931067a7abf21950d7935ec114c6e686829f90eb97a59a67897bc4bf2ab698
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 10931067a7abf21950d7935ec114c6e686829f90eb97a59a67897bc4bf2ab698; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P10931067a7abf21950d7935ec114c6e686829f90eb97a59a67897bc4bf2ab698

namespace PerfectPower.SOEModelPackets
def obs271 := PerfectPower.CheckedSOE.P10931067a7abf21950d7935ec114c6e686829f90eb97a59a67897bc4bf2ab698.obs
def step271 := PerfectPower.CheckedSOE.P10931067a7abf21950d7935ec114c6e686829f90eb97a59a67897bc4bf2ab698.step
def q271 := PerfectPower.CheckedSOE.P10931067a7abf21950d7935ec114c6e686829f90eb97a59a67897bc4bf2ab698.q
def out271 := PerfectPower.CheckedSOE.P10931067a7abf21950d7935ec114c6e686829f90eb97a59a67897bc4bf2ab698.out
def target271 := PerfectPower.CheckedSOE.P10931067a7abf21950d7935ec114c6e686829f90eb97a59a67897bc4bf2ab698.target
theorem complete271 (s t : Fin 2) : SOESemantics.Equivalent step271 obs271 s t ↔ q271 s = q271 t := PerfectPower.CheckedSOE.P10931067a7abf21950d7935ec114c6e686829f90eb97a59a67897bc4bf2ab698.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2f6cd7f4ede8ac92b6e442169046e49097855c461861260859ced973100c905e
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2f6cd7f4ede8ac92b6e442169046e49097855c461861260859ced973100c905e; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2f6cd7f4ede8ac92b6e442169046e49097855c461861260859ced973100c905e

namespace PerfectPower.SOEModelPackets
def obs272 := PerfectPower.CheckedSOE.P2f6cd7f4ede8ac92b6e442169046e49097855c461861260859ced973100c905e.obs
def step272 := PerfectPower.CheckedSOE.P2f6cd7f4ede8ac92b6e442169046e49097855c461861260859ced973100c905e.step
def q272 := PerfectPower.CheckedSOE.P2f6cd7f4ede8ac92b6e442169046e49097855c461861260859ced973100c905e.q
def out272 := PerfectPower.CheckedSOE.P2f6cd7f4ede8ac92b6e442169046e49097855c461861260859ced973100c905e.out
def target272 := PerfectPower.CheckedSOE.P2f6cd7f4ede8ac92b6e442169046e49097855c461861260859ced973100c905e.target
theorem complete272 (s t : Fin 2) : SOESemantics.Equivalent step272 obs272 s t ↔ q272 s = q272 t := PerfectPower.CheckedSOE.P2f6cd7f4ede8ac92b6e442169046e49097855c461861260859ced973100c905e.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb88e40f236289d4dccb5f12f0e56e8071dfdd98237dba9969480952030dc8648
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b88e40f236289d4dccb5f12f0e56e8071dfdd98237dba9969480952030dc8648; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb88e40f236289d4dccb5f12f0e56e8071dfdd98237dba9969480952030dc8648

namespace PerfectPower.SOEModelPackets
def obs273 := PerfectPower.CheckedSOE.Pb88e40f236289d4dccb5f12f0e56e8071dfdd98237dba9969480952030dc8648.obs
def step273 := PerfectPower.CheckedSOE.Pb88e40f236289d4dccb5f12f0e56e8071dfdd98237dba9969480952030dc8648.step
def q273 := PerfectPower.CheckedSOE.Pb88e40f236289d4dccb5f12f0e56e8071dfdd98237dba9969480952030dc8648.q
def out273 := PerfectPower.CheckedSOE.Pb88e40f236289d4dccb5f12f0e56e8071dfdd98237dba9969480952030dc8648.out
def target273 := PerfectPower.CheckedSOE.Pb88e40f236289d4dccb5f12f0e56e8071dfdd98237dba9969480952030dc8648.target
theorem complete273 (s t : Fin 2) : SOESemantics.Equivalent step273 obs273 s t ↔ q273 s = q273 t := PerfectPower.CheckedSOE.Pb88e40f236289d4dccb5f12f0e56e8071dfdd98237dba9969480952030dc8648.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P28b1ed57a6fa715d6ad0aa2f42c826eced51d71bb5125bea7665fe3a6d872107
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 28b1ed57a6fa715d6ad0aa2f42c826eced51d71bb5125bea7665fe3a6d872107; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P28b1ed57a6fa715d6ad0aa2f42c826eced51d71bb5125bea7665fe3a6d872107

namespace PerfectPower.SOEModelPackets
def obs274 := PerfectPower.CheckedSOE.P28b1ed57a6fa715d6ad0aa2f42c826eced51d71bb5125bea7665fe3a6d872107.obs
def step274 := PerfectPower.CheckedSOE.P28b1ed57a6fa715d6ad0aa2f42c826eced51d71bb5125bea7665fe3a6d872107.step
def q274 := PerfectPower.CheckedSOE.P28b1ed57a6fa715d6ad0aa2f42c826eced51d71bb5125bea7665fe3a6d872107.q
def out274 := PerfectPower.CheckedSOE.P28b1ed57a6fa715d6ad0aa2f42c826eced51d71bb5125bea7665fe3a6d872107.out
def target274 := PerfectPower.CheckedSOE.P28b1ed57a6fa715d6ad0aa2f42c826eced51d71bb5125bea7665fe3a6d872107.target
theorem complete274 (s t : Fin 2) : SOESemantics.Equivalent step274 obs274 s t ↔ q274 s = q274 t := PerfectPower.CheckedSOE.P28b1ed57a6fa715d6ad0aa2f42c826eced51d71bb5125bea7665fe3a6d872107.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P8d7f0706464e4390d5f702d0b3783d1ae35fb3ff59aa340e6127df09f6b6bf99
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 8d7f0706464e4390d5f702d0b3783d1ae35fb3ff59aa340e6127df09f6b6bf99; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P8d7f0706464e4390d5f702d0b3783d1ae35fb3ff59aa340e6127df09f6b6bf99

namespace PerfectPower.SOEModelPackets
def obs275 := PerfectPower.CheckedSOE.P8d7f0706464e4390d5f702d0b3783d1ae35fb3ff59aa340e6127df09f6b6bf99.obs
def step275 := PerfectPower.CheckedSOE.P8d7f0706464e4390d5f702d0b3783d1ae35fb3ff59aa340e6127df09f6b6bf99.step
def q275 := PerfectPower.CheckedSOE.P8d7f0706464e4390d5f702d0b3783d1ae35fb3ff59aa340e6127df09f6b6bf99.q
def out275 := PerfectPower.CheckedSOE.P8d7f0706464e4390d5f702d0b3783d1ae35fb3ff59aa340e6127df09f6b6bf99.out
def target275 := PerfectPower.CheckedSOE.P8d7f0706464e4390d5f702d0b3783d1ae35fb3ff59aa340e6127df09f6b6bf99.target
theorem complete275 (s t : Fin 2) : SOESemantics.Equivalent step275 obs275 s t ↔ q275 s = q275 t := PerfectPower.CheckedSOE.P8d7f0706464e4390d5f702d0b3783d1ae35fb3ff59aa340e6127df09f6b6bf99.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P25a483209b5b25860334bdc40eb13fc28ff2ae637d5814d65eefe52f8ca5b713
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 25a483209b5b25860334bdc40eb13fc28ff2ae637d5814d65eefe52f8ca5b713; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P25a483209b5b25860334bdc40eb13fc28ff2ae637d5814d65eefe52f8ca5b713

namespace PerfectPower.SOEModelPackets
def obs276 := PerfectPower.CheckedSOE.P25a483209b5b25860334bdc40eb13fc28ff2ae637d5814d65eefe52f8ca5b713.obs
def step276 := PerfectPower.CheckedSOE.P25a483209b5b25860334bdc40eb13fc28ff2ae637d5814d65eefe52f8ca5b713.step
def q276 := PerfectPower.CheckedSOE.P25a483209b5b25860334bdc40eb13fc28ff2ae637d5814d65eefe52f8ca5b713.q
def out276 := PerfectPower.CheckedSOE.P25a483209b5b25860334bdc40eb13fc28ff2ae637d5814d65eefe52f8ca5b713.out
def target276 := PerfectPower.CheckedSOE.P25a483209b5b25860334bdc40eb13fc28ff2ae637d5814d65eefe52f8ca5b713.target
theorem complete276 (s t : Fin 2) : SOESemantics.Equivalent step276 obs276 s t ↔ q276 s = q276 t := PerfectPower.CheckedSOE.P25a483209b5b25860334bdc40eb13fc28ff2ae637d5814d65eefe52f8ca5b713.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P520d0eca315d3154dfa88d1145ea597bccbad56807855af9a4729b0ff2f0c3c4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 520d0eca315d3154dfa88d1145ea597bccbad56807855af9a4729b0ff2f0c3c4; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P520d0eca315d3154dfa88d1145ea597bccbad56807855af9a4729b0ff2f0c3c4

namespace PerfectPower.SOEModelPackets
def obs277 := PerfectPower.CheckedSOE.P520d0eca315d3154dfa88d1145ea597bccbad56807855af9a4729b0ff2f0c3c4.obs
def step277 := PerfectPower.CheckedSOE.P520d0eca315d3154dfa88d1145ea597bccbad56807855af9a4729b0ff2f0c3c4.step
def q277 := PerfectPower.CheckedSOE.P520d0eca315d3154dfa88d1145ea597bccbad56807855af9a4729b0ff2f0c3c4.q
def out277 := PerfectPower.CheckedSOE.P520d0eca315d3154dfa88d1145ea597bccbad56807855af9a4729b0ff2f0c3c4.out
def target277 := PerfectPower.CheckedSOE.P520d0eca315d3154dfa88d1145ea597bccbad56807855af9a4729b0ff2f0c3c4.target
theorem complete277 (s t : Fin 2) : SOESemantics.Equivalent step277 obs277 s t ↔ q277 s = q277 t := PerfectPower.CheckedSOE.P520d0eca315d3154dfa88d1145ea597bccbad56807855af9a4729b0ff2f0c3c4.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pa82e389b4796c8872a57ed7854fb04665c731bd9f27dc9bb45940fbd003442c2
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: a82e389b4796c8872a57ed7854fb04665c731bd9f27dc9bb45940fbd003442c2; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pa82e389b4796c8872a57ed7854fb04665c731bd9f27dc9bb45940fbd003442c2

namespace PerfectPower.SOEModelPackets
def obs278 := PerfectPower.CheckedSOE.Pa82e389b4796c8872a57ed7854fb04665c731bd9f27dc9bb45940fbd003442c2.obs
def step278 := PerfectPower.CheckedSOE.Pa82e389b4796c8872a57ed7854fb04665c731bd9f27dc9bb45940fbd003442c2.step
def q278 := PerfectPower.CheckedSOE.Pa82e389b4796c8872a57ed7854fb04665c731bd9f27dc9bb45940fbd003442c2.q
def out278 := PerfectPower.CheckedSOE.Pa82e389b4796c8872a57ed7854fb04665c731bd9f27dc9bb45940fbd003442c2.out
def target278 := PerfectPower.CheckedSOE.Pa82e389b4796c8872a57ed7854fb04665c731bd9f27dc9bb45940fbd003442c2.target
theorem complete278 (s t : Fin 2) : SOESemantics.Equivalent step278 obs278 s t ↔ q278 s = q278 t := PerfectPower.CheckedSOE.Pa82e389b4796c8872a57ed7854fb04665c731bd9f27dc9bb45940fbd003442c2.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P7cd9bf37b51baf8613819682911f8349fa55d844ad49fdb9b384e5624f50bc54
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 7cd9bf37b51baf8613819682911f8349fa55d844ad49fdb9b384e5624f50bc54; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P7cd9bf37b51baf8613819682911f8349fa55d844ad49fdb9b384e5624f50bc54

namespace PerfectPower.SOEModelPackets
def obs279 := PerfectPower.CheckedSOE.P7cd9bf37b51baf8613819682911f8349fa55d844ad49fdb9b384e5624f50bc54.obs
def step279 := PerfectPower.CheckedSOE.P7cd9bf37b51baf8613819682911f8349fa55d844ad49fdb9b384e5624f50bc54.step
def q279 := PerfectPower.CheckedSOE.P7cd9bf37b51baf8613819682911f8349fa55d844ad49fdb9b384e5624f50bc54.q
def out279 := PerfectPower.CheckedSOE.P7cd9bf37b51baf8613819682911f8349fa55d844ad49fdb9b384e5624f50bc54.out
def target279 := PerfectPower.CheckedSOE.P7cd9bf37b51baf8613819682911f8349fa55d844ad49fdb9b384e5624f50bc54.target
theorem complete279 (s t : Fin 2) : SOESemantics.Equivalent step279 obs279 s t ↔ q279 s = q279 t := PerfectPower.CheckedSOE.P7cd9bf37b51baf8613819682911f8349fa55d844ad49fdb9b384e5624f50bc54.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P5c8929ae3279bdfd62961f1aabe57d78c7ea44069ea04cc7ba91318ed5b8a072
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 5c8929ae3279bdfd62961f1aabe57d78c7ea44069ea04cc7ba91318ed5b8a072; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P5c8929ae3279bdfd62961f1aabe57d78c7ea44069ea04cc7ba91318ed5b8a072

namespace PerfectPower.SOEModelPackets
def obs280 := PerfectPower.CheckedSOE.P5c8929ae3279bdfd62961f1aabe57d78c7ea44069ea04cc7ba91318ed5b8a072.obs
def step280 := PerfectPower.CheckedSOE.P5c8929ae3279bdfd62961f1aabe57d78c7ea44069ea04cc7ba91318ed5b8a072.step
def q280 := PerfectPower.CheckedSOE.P5c8929ae3279bdfd62961f1aabe57d78c7ea44069ea04cc7ba91318ed5b8a072.q
def out280 := PerfectPower.CheckedSOE.P5c8929ae3279bdfd62961f1aabe57d78c7ea44069ea04cc7ba91318ed5b8a072.out
def target280 := PerfectPower.CheckedSOE.P5c8929ae3279bdfd62961f1aabe57d78c7ea44069ea04cc7ba91318ed5b8a072.target
theorem complete280 (s t : Fin 2) : SOESemantics.Equivalent step280 obs280 s t ↔ q280 s = q280 t := PerfectPower.CheckedSOE.P5c8929ae3279bdfd62961f1aabe57d78c7ea44069ea04cc7ba91318ed5b8a072.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P95c97e4bc6b6c16f1d36e15d429962619b687a3b6310ec67ddbf2d399b4cafef
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 95c97e4bc6b6c16f1d36e15d429962619b687a3b6310ec67ddbf2d399b4cafef; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P95c97e4bc6b6c16f1d36e15d429962619b687a3b6310ec67ddbf2d399b4cafef

namespace PerfectPower.SOEModelPackets
def obs281 := PerfectPower.CheckedSOE.P95c97e4bc6b6c16f1d36e15d429962619b687a3b6310ec67ddbf2d399b4cafef.obs
def step281 := PerfectPower.CheckedSOE.P95c97e4bc6b6c16f1d36e15d429962619b687a3b6310ec67ddbf2d399b4cafef.step
def q281 := PerfectPower.CheckedSOE.P95c97e4bc6b6c16f1d36e15d429962619b687a3b6310ec67ddbf2d399b4cafef.q
def out281 := PerfectPower.CheckedSOE.P95c97e4bc6b6c16f1d36e15d429962619b687a3b6310ec67ddbf2d399b4cafef.out
def target281 := PerfectPower.CheckedSOE.P95c97e4bc6b6c16f1d36e15d429962619b687a3b6310ec67ddbf2d399b4cafef.target
theorem complete281 (s t : Fin 2) : SOESemantics.Equivalent step281 obs281 s t ↔ q281 s = q281 t := PerfectPower.CheckedSOE.P95c97e4bc6b6c16f1d36e15d429962619b687a3b6310ec67ddbf2d399b4cafef.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P58a656c2ab227e3261a9eca2d06be9bd3411c411a25723afba25f9bd9e1a16a3
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 58a656c2ab227e3261a9eca2d06be9bd3411c411a25723afba25f9bd9e1a16a3; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P58a656c2ab227e3261a9eca2d06be9bd3411c411a25723afba25f9bd9e1a16a3

namespace PerfectPower.SOEModelPackets
def obs282 := PerfectPower.CheckedSOE.P58a656c2ab227e3261a9eca2d06be9bd3411c411a25723afba25f9bd9e1a16a3.obs
def step282 := PerfectPower.CheckedSOE.P58a656c2ab227e3261a9eca2d06be9bd3411c411a25723afba25f9bd9e1a16a3.step
def q282 := PerfectPower.CheckedSOE.P58a656c2ab227e3261a9eca2d06be9bd3411c411a25723afba25f9bd9e1a16a3.q
def out282 := PerfectPower.CheckedSOE.P58a656c2ab227e3261a9eca2d06be9bd3411c411a25723afba25f9bd9e1a16a3.out
def target282 := PerfectPower.CheckedSOE.P58a656c2ab227e3261a9eca2d06be9bd3411c411a25723afba25f9bd9e1a16a3.target
theorem complete282 (s t : Fin 2) : SOESemantics.Equivalent step282 obs282 s t ↔ q282 s = q282 t := PerfectPower.CheckedSOE.P58a656c2ab227e3261a9eca2d06be9bd3411c411a25723afba25f9bd9e1a16a3.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P1a9fca5235ad9e5865f7c134cd75c6efccebfb5a96ab82144ef99257a6404487
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 1a9fca5235ad9e5865f7c134cd75c6efccebfb5a96ab82144ef99257a6404487; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P1a9fca5235ad9e5865f7c134cd75c6efccebfb5a96ab82144ef99257a6404487

namespace PerfectPower.SOEModelPackets
def obs283 := PerfectPower.CheckedSOE.P1a9fca5235ad9e5865f7c134cd75c6efccebfb5a96ab82144ef99257a6404487.obs
def step283 := PerfectPower.CheckedSOE.P1a9fca5235ad9e5865f7c134cd75c6efccebfb5a96ab82144ef99257a6404487.step
def q283 := PerfectPower.CheckedSOE.P1a9fca5235ad9e5865f7c134cd75c6efccebfb5a96ab82144ef99257a6404487.q
def out283 := PerfectPower.CheckedSOE.P1a9fca5235ad9e5865f7c134cd75c6efccebfb5a96ab82144ef99257a6404487.out
def target283 := PerfectPower.CheckedSOE.P1a9fca5235ad9e5865f7c134cd75c6efccebfb5a96ab82144ef99257a6404487.target
theorem complete283 (s t : Fin 2) : SOESemantics.Equivalent step283 obs283 s t ↔ q283 s = q283 t := PerfectPower.CheckedSOE.P1a9fca5235ad9e5865f7c134cd75c6efccebfb5a96ab82144ef99257a6404487.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P2b2f32a02d0c91c34e36bdf2dd91c983fee3768b322e59cc093abca0dd6fedf1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 2b2f32a02d0c91c34e36bdf2dd91c983fee3768b322e59cc093abca0dd6fedf1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P2b2f32a02d0c91c34e36bdf2dd91c983fee3768b322e59cc093abca0dd6fedf1

namespace PerfectPower.SOEModelPackets
def obs284 := PerfectPower.CheckedSOE.P2b2f32a02d0c91c34e36bdf2dd91c983fee3768b322e59cc093abca0dd6fedf1.obs
def step284 := PerfectPower.CheckedSOE.P2b2f32a02d0c91c34e36bdf2dd91c983fee3768b322e59cc093abca0dd6fedf1.step
def q284 := PerfectPower.CheckedSOE.P2b2f32a02d0c91c34e36bdf2dd91c983fee3768b322e59cc093abca0dd6fedf1.q
def out284 := PerfectPower.CheckedSOE.P2b2f32a02d0c91c34e36bdf2dd91c983fee3768b322e59cc093abca0dd6fedf1.out
def target284 := PerfectPower.CheckedSOE.P2b2f32a02d0c91c34e36bdf2dd91c983fee3768b322e59cc093abca0dd6fedf1.target
theorem complete284 (s t : Fin 2) : SOESemantics.Equivalent step284 obs284 s t ↔ q284 s = q284 t := PerfectPower.CheckedSOE.P2b2f32a02d0c91c34e36bdf2dd91c983fee3768b322e59cc093abca0dd6fedf1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc4437c6ffe2df035a1ed1c238d1566029e7d10057dee5e0ff11ce70c452f9400
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c4437c6ffe2df035a1ed1c238d1566029e7d10057dee5e0ff11ce70c452f9400; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc4437c6ffe2df035a1ed1c238d1566029e7d10057dee5e0ff11ce70c452f9400

namespace PerfectPower.SOEModelPackets
def obs285 := PerfectPower.CheckedSOE.Pc4437c6ffe2df035a1ed1c238d1566029e7d10057dee5e0ff11ce70c452f9400.obs
def step285 := PerfectPower.CheckedSOE.Pc4437c6ffe2df035a1ed1c238d1566029e7d10057dee5e0ff11ce70c452f9400.step
def q285 := PerfectPower.CheckedSOE.Pc4437c6ffe2df035a1ed1c238d1566029e7d10057dee5e0ff11ce70c452f9400.q
def out285 := PerfectPower.CheckedSOE.Pc4437c6ffe2df035a1ed1c238d1566029e7d10057dee5e0ff11ce70c452f9400.out
def target285 := PerfectPower.CheckedSOE.Pc4437c6ffe2df035a1ed1c238d1566029e7d10057dee5e0ff11ce70c452f9400.target
theorem complete285 (s t : Fin 2) : SOESemantics.Equivalent step285 obs285 s t ↔ q285 s = q285 t := PerfectPower.CheckedSOE.Pc4437c6ffe2df035a1ed1c238d1566029e7d10057dee5e0ff11ce70c452f9400.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P7ace2b49cd9b6df442e416df3a2ab52900f34e8f04c6be5e2f264a58e86b46d4
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 7ace2b49cd9b6df442e416df3a2ab52900f34e8f04c6be5e2f264a58e86b46d4; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P7ace2b49cd9b6df442e416df3a2ab52900f34e8f04c6be5e2f264a58e86b46d4

namespace PerfectPower.SOEModelPackets
def obs286 := PerfectPower.CheckedSOE.P7ace2b49cd9b6df442e416df3a2ab52900f34e8f04c6be5e2f264a58e86b46d4.obs
def step286 := PerfectPower.CheckedSOE.P7ace2b49cd9b6df442e416df3a2ab52900f34e8f04c6be5e2f264a58e86b46d4.step
def q286 := PerfectPower.CheckedSOE.P7ace2b49cd9b6df442e416df3a2ab52900f34e8f04c6be5e2f264a58e86b46d4.q
def out286 := PerfectPower.CheckedSOE.P7ace2b49cd9b6df442e416df3a2ab52900f34e8f04c6be5e2f264a58e86b46d4.out
def target286 := PerfectPower.CheckedSOE.P7ace2b49cd9b6df442e416df3a2ab52900f34e8f04c6be5e2f264a58e86b46d4.target
theorem complete286 (s t : Fin 2) : SOESemantics.Equivalent step286 obs286 s t ↔ q286 s = q286 t := PerfectPower.CheckedSOE.P7ace2b49cd9b6df442e416df3a2ab52900f34e8f04c6be5e2f264a58e86b46d4.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P65143aa697ee9b792c2daecdc7d467c7c9ca8f089f0e13a0b87196760a59f249
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 65143aa697ee9b792c2daecdc7d467c7c9ca8f089f0e13a0b87196760a59f249; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P65143aa697ee9b792c2daecdc7d467c7c9ca8f089f0e13a0b87196760a59f249

namespace PerfectPower.SOEModelPackets
def obs287 := PerfectPower.CheckedSOE.P65143aa697ee9b792c2daecdc7d467c7c9ca8f089f0e13a0b87196760a59f249.obs
def step287 := PerfectPower.CheckedSOE.P65143aa697ee9b792c2daecdc7d467c7c9ca8f089f0e13a0b87196760a59f249.step
def q287 := PerfectPower.CheckedSOE.P65143aa697ee9b792c2daecdc7d467c7c9ca8f089f0e13a0b87196760a59f249.q
def out287 := PerfectPower.CheckedSOE.P65143aa697ee9b792c2daecdc7d467c7c9ca8f089f0e13a0b87196760a59f249.out
def target287 := PerfectPower.CheckedSOE.P65143aa697ee9b792c2daecdc7d467c7c9ca8f089f0e13a0b87196760a59f249.target
theorem complete287 (s t : Fin 2) : SOESemantics.Equivalent step287 obs287 s t ↔ q287 s = q287 t := PerfectPower.CheckedSOE.P65143aa697ee9b792c2daecdc7d467c7c9ca8f089f0e13a0b87196760a59f249.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P266096f1ccb3f8a7c8752d5098fa0a114e426e9bdd4e36e3b313b34cfd63ea00
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 266096f1ccb3f8a7c8752d5098fa0a114e426e9bdd4e36e3b313b34cfd63ea00; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P266096f1ccb3f8a7c8752d5098fa0a114e426e9bdd4e36e3b313b34cfd63ea00

namespace PerfectPower.SOEModelPackets
def obs288 := PerfectPower.CheckedSOE.P266096f1ccb3f8a7c8752d5098fa0a114e426e9bdd4e36e3b313b34cfd63ea00.obs
def step288 := PerfectPower.CheckedSOE.P266096f1ccb3f8a7c8752d5098fa0a114e426e9bdd4e36e3b313b34cfd63ea00.step
def q288 := PerfectPower.CheckedSOE.P266096f1ccb3f8a7c8752d5098fa0a114e426e9bdd4e36e3b313b34cfd63ea00.q
def out288 := PerfectPower.CheckedSOE.P266096f1ccb3f8a7c8752d5098fa0a114e426e9bdd4e36e3b313b34cfd63ea00.out
def target288 := PerfectPower.CheckedSOE.P266096f1ccb3f8a7c8752d5098fa0a114e426e9bdd4e36e3b313b34cfd63ea00.target
theorem complete288 (s t : Fin 2) : SOESemantics.Equivalent step288 obs288 s t ↔ q288 s = q288 t := PerfectPower.CheckedSOE.P266096f1ccb3f8a7c8752d5098fa0a114e426e9bdd4e36e3b313b34cfd63ea00.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pac154cb9be906de8ff2bde1be8cf4a54a8f1c8f6def21025322668590fd3b465
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ac154cb9be906de8ff2bde1be8cf4a54a8f1c8f6def21025322668590fd3b465; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pac154cb9be906de8ff2bde1be8cf4a54a8f1c8f6def21025322668590fd3b465

namespace PerfectPower.SOEModelPackets
def obs289 := PerfectPower.CheckedSOE.Pac154cb9be906de8ff2bde1be8cf4a54a8f1c8f6def21025322668590fd3b465.obs
def step289 := PerfectPower.CheckedSOE.Pac154cb9be906de8ff2bde1be8cf4a54a8f1c8f6def21025322668590fd3b465.step
def q289 := PerfectPower.CheckedSOE.Pac154cb9be906de8ff2bde1be8cf4a54a8f1c8f6def21025322668590fd3b465.q
def out289 := PerfectPower.CheckedSOE.Pac154cb9be906de8ff2bde1be8cf4a54a8f1c8f6def21025322668590fd3b465.out
def target289 := PerfectPower.CheckedSOE.Pac154cb9be906de8ff2bde1be8cf4a54a8f1c8f6def21025322668590fd3b465.target
theorem complete289 (s t : Fin 2) : SOESemantics.Equivalent step289 obs289 s t ↔ q289 s = q289 t := PerfectPower.CheckedSOE.Pac154cb9be906de8ff2bde1be8cf4a54a8f1c8f6def21025322668590fd3b465.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P542019411c0a73dadb8fa010a904db5a26a4144ec5c165fe6345ce58d354a9ae
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 542019411c0a73dadb8fa010a904db5a26a4144ec5c165fe6345ce58d354a9ae; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P542019411c0a73dadb8fa010a904db5a26a4144ec5c165fe6345ce58d354a9ae

namespace PerfectPower.SOEModelPackets
def obs290 := PerfectPower.CheckedSOE.P542019411c0a73dadb8fa010a904db5a26a4144ec5c165fe6345ce58d354a9ae.obs
def step290 := PerfectPower.CheckedSOE.P542019411c0a73dadb8fa010a904db5a26a4144ec5c165fe6345ce58d354a9ae.step
def q290 := PerfectPower.CheckedSOE.P542019411c0a73dadb8fa010a904db5a26a4144ec5c165fe6345ce58d354a9ae.q
def out290 := PerfectPower.CheckedSOE.P542019411c0a73dadb8fa010a904db5a26a4144ec5c165fe6345ce58d354a9ae.out
def target290 := PerfectPower.CheckedSOE.P542019411c0a73dadb8fa010a904db5a26a4144ec5c165fe6345ce58d354a9ae.target
theorem complete290 (s t : Fin 2) : SOESemantics.Equivalent step290 obs290 s t ↔ q290 s = q290 t := PerfectPower.CheckedSOE.P542019411c0a73dadb8fa010a904db5a26a4144ec5c165fe6345ce58d354a9ae.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P73d9d2a1832f8f3638bd41cd42d1024511b5849314982bc9ed68d9e260e11158
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 73d9d2a1832f8f3638bd41cd42d1024511b5849314982bc9ed68d9e260e11158; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P73d9d2a1832f8f3638bd41cd42d1024511b5849314982bc9ed68d9e260e11158

namespace PerfectPower.SOEModelPackets
def obs291 := PerfectPower.CheckedSOE.P73d9d2a1832f8f3638bd41cd42d1024511b5849314982bc9ed68d9e260e11158.obs
def step291 := PerfectPower.CheckedSOE.P73d9d2a1832f8f3638bd41cd42d1024511b5849314982bc9ed68d9e260e11158.step
def q291 := PerfectPower.CheckedSOE.P73d9d2a1832f8f3638bd41cd42d1024511b5849314982bc9ed68d9e260e11158.q
def out291 := PerfectPower.CheckedSOE.P73d9d2a1832f8f3638bd41cd42d1024511b5849314982bc9ed68d9e260e11158.out
def target291 := PerfectPower.CheckedSOE.P73d9d2a1832f8f3638bd41cd42d1024511b5849314982bc9ed68d9e260e11158.target
theorem complete291 (s t : Fin 2) : SOESemantics.Equivalent step291 obs291 s t ↔ q291 s = q291 t := PerfectPower.CheckedSOE.P73d9d2a1832f8f3638bd41cd42d1024511b5849314982bc9ed68d9e260e11158.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pdf1c95073e116a6f70e2b865ad92b844d99210a29ee7a9710f6294010c621de2
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: df1c95073e116a6f70e2b865ad92b844d99210a29ee7a9710f6294010c621de2; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pdf1c95073e116a6f70e2b865ad92b844d99210a29ee7a9710f6294010c621de2

namespace PerfectPower.SOEModelPackets
def obs292 := PerfectPower.CheckedSOE.Pdf1c95073e116a6f70e2b865ad92b844d99210a29ee7a9710f6294010c621de2.obs
def step292 := PerfectPower.CheckedSOE.Pdf1c95073e116a6f70e2b865ad92b844d99210a29ee7a9710f6294010c621de2.step
def q292 := PerfectPower.CheckedSOE.Pdf1c95073e116a6f70e2b865ad92b844d99210a29ee7a9710f6294010c621de2.q
def out292 := PerfectPower.CheckedSOE.Pdf1c95073e116a6f70e2b865ad92b844d99210a29ee7a9710f6294010c621de2.out
def target292 := PerfectPower.CheckedSOE.Pdf1c95073e116a6f70e2b865ad92b844d99210a29ee7a9710f6294010c621de2.target
theorem complete292 (s t : Fin 2) : SOESemantics.Equivalent step292 obs292 s t ↔ q292 s = q292 t := PerfectPower.CheckedSOE.Pdf1c95073e116a6f70e2b865ad92b844d99210a29ee7a9710f6294010c621de2.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P915eb4fe20a86aa9d98fcf9dba7c54a82ff3c680b29df2262e03ae95cc51773b
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 915eb4fe20a86aa9d98fcf9dba7c54a82ff3c680b29df2262e03ae95cc51773b; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P915eb4fe20a86aa9d98fcf9dba7c54a82ff3c680b29df2262e03ae95cc51773b

namespace PerfectPower.SOEModelPackets
def obs293 := PerfectPower.CheckedSOE.P915eb4fe20a86aa9d98fcf9dba7c54a82ff3c680b29df2262e03ae95cc51773b.obs
def step293 := PerfectPower.CheckedSOE.P915eb4fe20a86aa9d98fcf9dba7c54a82ff3c680b29df2262e03ae95cc51773b.step
def q293 := PerfectPower.CheckedSOE.P915eb4fe20a86aa9d98fcf9dba7c54a82ff3c680b29df2262e03ae95cc51773b.q
def out293 := PerfectPower.CheckedSOE.P915eb4fe20a86aa9d98fcf9dba7c54a82ff3c680b29df2262e03ae95cc51773b.out
def target293 := PerfectPower.CheckedSOE.P915eb4fe20a86aa9d98fcf9dba7c54a82ff3c680b29df2262e03ae95cc51773b.target
theorem complete293 (s t : Fin 2) : SOESemantics.Equivalent step293 obs293 s t ↔ q293 s = q293 t := PerfectPower.CheckedSOE.P915eb4fe20a86aa9d98fcf9dba7c54a82ff3c680b29df2262e03ae95cc51773b.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P665a1da85b08d145446b0cba8254414a1acb65b8f52bf4043bc9dc3bfeb11891
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 665a1da85b08d145446b0cba8254414a1acb65b8f52bf4043bc9dc3bfeb11891; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P665a1da85b08d145446b0cba8254414a1acb65b8f52bf4043bc9dc3bfeb11891

namespace PerfectPower.SOEModelPackets
def obs294 := PerfectPower.CheckedSOE.P665a1da85b08d145446b0cba8254414a1acb65b8f52bf4043bc9dc3bfeb11891.obs
def step294 := PerfectPower.CheckedSOE.P665a1da85b08d145446b0cba8254414a1acb65b8f52bf4043bc9dc3bfeb11891.step
def q294 := PerfectPower.CheckedSOE.P665a1da85b08d145446b0cba8254414a1acb65b8f52bf4043bc9dc3bfeb11891.q
def out294 := PerfectPower.CheckedSOE.P665a1da85b08d145446b0cba8254414a1acb65b8f52bf4043bc9dc3bfeb11891.out
def target294 := PerfectPower.CheckedSOE.P665a1da85b08d145446b0cba8254414a1acb65b8f52bf4043bc9dc3bfeb11891.target
theorem complete294 (s t : Fin 2) : SOESemantics.Equivalent step294 obs294 s t ↔ q294 s = q294 t := PerfectPower.CheckedSOE.P665a1da85b08d145446b0cba8254414a1acb65b8f52bf4043bc9dc3bfeb11891.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P72be66064b7f335865bf3fbfd324719df7f53154d99ff69c5a891f390b08cda7
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 72be66064b7f335865bf3fbfd324719df7f53154d99ff69c5a891f390b08cda7; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P72be66064b7f335865bf3fbfd324719df7f53154d99ff69c5a891f390b08cda7

namespace PerfectPower.SOEModelPackets
def obs295 := PerfectPower.CheckedSOE.P72be66064b7f335865bf3fbfd324719df7f53154d99ff69c5a891f390b08cda7.obs
def step295 := PerfectPower.CheckedSOE.P72be66064b7f335865bf3fbfd324719df7f53154d99ff69c5a891f390b08cda7.step
def q295 := PerfectPower.CheckedSOE.P72be66064b7f335865bf3fbfd324719df7f53154d99ff69c5a891f390b08cda7.q
def out295 := PerfectPower.CheckedSOE.P72be66064b7f335865bf3fbfd324719df7f53154d99ff69c5a891f390b08cda7.out
def target295 := PerfectPower.CheckedSOE.P72be66064b7f335865bf3fbfd324719df7f53154d99ff69c5a891f390b08cda7.target
theorem complete295 (s t : Fin 2) : SOESemantics.Equivalent step295 obs295 s t ↔ q295 s = q295 t := PerfectPower.CheckedSOE.P72be66064b7f335865bf3fbfd324719df7f53154d99ff69c5a891f390b08cda7.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P9c454585a5716385e14e686c849dbc39e915cae729dec2dbb690d5c0fe4827e8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 9c454585a5716385e14e686c849dbc39e915cae729dec2dbb690d5c0fe4827e8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 0 else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P9c454585a5716385e14e686c849dbc39e915cae729dec2dbb690d5c0fe4827e8

namespace PerfectPower.SOEModelPackets
def obs296 := PerfectPower.CheckedSOE.P9c454585a5716385e14e686c849dbc39e915cae729dec2dbb690d5c0fe4827e8.obs
def step296 := PerfectPower.CheckedSOE.P9c454585a5716385e14e686c849dbc39e915cae729dec2dbb690d5c0fe4827e8.step
def q296 := PerfectPower.CheckedSOE.P9c454585a5716385e14e686c849dbc39e915cae729dec2dbb690d5c0fe4827e8.q
def out296 := PerfectPower.CheckedSOE.P9c454585a5716385e14e686c849dbc39e915cae729dec2dbb690d5c0fe4827e8.out
def target296 := PerfectPower.CheckedSOE.P9c454585a5716385e14e686c849dbc39e915cae729dec2dbb690d5c0fe4827e8.target
theorem complete296 (s t : Fin 2) : SOESemantics.Equivalent step296 obs296 s t ↔ q296 s = q296 t := PerfectPower.CheckedSOE.P9c454585a5716385e14e686c849dbc39e915cae729dec2dbb690d5c0fe4827e8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pedfe48026a9c52fc2a0cb2db9c48b2255e057b2b57c9269dffa1a9093828b9a6
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: edfe48026a9c52fc2a0cb2db9c48b2255e057b2b57c9269dffa1a9093828b9a6; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pedfe48026a9c52fc2a0cb2db9c48b2255e057b2b57c9269dffa1a9093828b9a6

namespace PerfectPower.SOEModelPackets
def obs297 := PerfectPower.CheckedSOE.Pedfe48026a9c52fc2a0cb2db9c48b2255e057b2b57c9269dffa1a9093828b9a6.obs
def step297 := PerfectPower.CheckedSOE.Pedfe48026a9c52fc2a0cb2db9c48b2255e057b2b57c9269dffa1a9093828b9a6.step
def q297 := PerfectPower.CheckedSOE.Pedfe48026a9c52fc2a0cb2db9c48b2255e057b2b57c9269dffa1a9093828b9a6.q
def out297 := PerfectPower.CheckedSOE.Pedfe48026a9c52fc2a0cb2db9c48b2255e057b2b57c9269dffa1a9093828b9a6.out
def target297 := PerfectPower.CheckedSOE.Pedfe48026a9c52fc2a0cb2db9c48b2255e057b2b57c9269dffa1a9093828b9a6.target
theorem complete297 (s t : Fin 2) : SOESemantics.Equivalent step297 obs297 s t ↔ q297 s = q297 t := PerfectPower.CheckedSOE.Pedfe48026a9c52fc2a0cb2db9c48b2255e057b2b57c9269dffa1a9093828b9a6.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb8999b1bb2bc9aa8792796d1f9570d7e9f8b61b8caf05868c3701493ba3abd0d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b8999b1bb2bc9aa8792796d1f9570d7e9f8b61b8caf05868c3701493ba3abd0d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb8999b1bb2bc9aa8792796d1f9570d7e9f8b61b8caf05868c3701493ba3abd0d

namespace PerfectPower.SOEModelPackets
def obs298 := PerfectPower.CheckedSOE.Pb8999b1bb2bc9aa8792796d1f9570d7e9f8b61b8caf05868c3701493ba3abd0d.obs
def step298 := PerfectPower.CheckedSOE.Pb8999b1bb2bc9aa8792796d1f9570d7e9f8b61b8caf05868c3701493ba3abd0d.step
def q298 := PerfectPower.CheckedSOE.Pb8999b1bb2bc9aa8792796d1f9570d7e9f8b61b8caf05868c3701493ba3abd0d.q
def out298 := PerfectPower.CheckedSOE.Pb8999b1bb2bc9aa8792796d1f9570d7e9f8b61b8caf05868c3701493ba3abd0d.out
def target298 := PerfectPower.CheckedSOE.Pb8999b1bb2bc9aa8792796d1f9570d7e9f8b61b8caf05868c3701493ba3abd0d.target
theorem complete298 (s t : Fin 2) : SOESemantics.Equivalent step298 obs298 s t ↔ q298 s = q298 t := PerfectPower.CheckedSOE.Pb8999b1bb2bc9aa8792796d1f9570d7e9f8b61b8caf05868c3701493ba3abd0d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pddee9d0afc6a81a0a3be3ced9dd3340e0ec6e93ccf016ef3251b1dc1307c088f
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ddee9d0afc6a81a0a3be3ced9dd3340e0ec6e93ccf016ef3251b1dc1307c088f; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pddee9d0afc6a81a0a3be3ced9dd3340e0ec6e93ccf016ef3251b1dc1307c088f

namespace PerfectPower.SOEModelPackets
def obs299 := PerfectPower.CheckedSOE.Pddee9d0afc6a81a0a3be3ced9dd3340e0ec6e93ccf016ef3251b1dc1307c088f.obs
def step299 := PerfectPower.CheckedSOE.Pddee9d0afc6a81a0a3be3ced9dd3340e0ec6e93ccf016ef3251b1dc1307c088f.step
def q299 := PerfectPower.CheckedSOE.Pddee9d0afc6a81a0a3be3ced9dd3340e0ec6e93ccf016ef3251b1dc1307c088f.q
def out299 := PerfectPower.CheckedSOE.Pddee9d0afc6a81a0a3be3ced9dd3340e0ec6e93ccf016ef3251b1dc1307c088f.out
def target299 := PerfectPower.CheckedSOE.Pddee9d0afc6a81a0a3be3ced9dd3340e0ec6e93ccf016ef3251b1dc1307c088f.target
theorem complete299 (s t : Fin 2) : SOESemantics.Equivalent step299 obs299 s t ↔ q299 s = q299 t := PerfectPower.CheckedSOE.Pddee9d0afc6a81a0a3be3ced9dd3340e0ec6e93ccf016ef3251b1dc1307c088f.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P9109414f72b51ea3e231818879128980249fc2ae8185c614f498f3d778d515ec
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 9109414f72b51ea3e231818879128980249fc2ae8185c614f498f3d778d515ec; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P9109414f72b51ea3e231818879128980249fc2ae8185c614f498f3d778d515ec

namespace PerfectPower.SOEModelPackets
def obs300 := PerfectPower.CheckedSOE.P9109414f72b51ea3e231818879128980249fc2ae8185c614f498f3d778d515ec.obs
def step300 := PerfectPower.CheckedSOE.P9109414f72b51ea3e231818879128980249fc2ae8185c614f498f3d778d515ec.step
def q300 := PerfectPower.CheckedSOE.P9109414f72b51ea3e231818879128980249fc2ae8185c614f498f3d778d515ec.q
def out300 := PerfectPower.CheckedSOE.P9109414f72b51ea3e231818879128980249fc2ae8185c614f498f3d778d515ec.out
def target300 := PerfectPower.CheckedSOE.P9109414f72b51ea3e231818879128980249fc2ae8185c614f498f3d778d515ec.target
theorem complete300 (s t : Fin 2) : SOESemantics.Equivalent step300 obs300 s t ↔ q300 s = q300 t := PerfectPower.CheckedSOE.P9109414f72b51ea3e231818879128980249fc2ae8185c614f498f3d778d515ec.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P6bad56ba299af2c53aa0fecddf667da9d105da3c1bfe44989a02ca74c64cba6c
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 6bad56ba299af2c53aa0fecddf667da9d105da3c1bfe44989a02ca74c64cba6c; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P6bad56ba299af2c53aa0fecddf667da9d105da3c1bfe44989a02ca74c64cba6c

namespace PerfectPower.SOEModelPackets
def obs301 := PerfectPower.CheckedSOE.P6bad56ba299af2c53aa0fecddf667da9d105da3c1bfe44989a02ca74c64cba6c.obs
def step301 := PerfectPower.CheckedSOE.P6bad56ba299af2c53aa0fecddf667da9d105da3c1bfe44989a02ca74c64cba6c.step
def q301 := PerfectPower.CheckedSOE.P6bad56ba299af2c53aa0fecddf667da9d105da3c1bfe44989a02ca74c64cba6c.q
def out301 := PerfectPower.CheckedSOE.P6bad56ba299af2c53aa0fecddf667da9d105da3c1bfe44989a02ca74c64cba6c.out
def target301 := PerfectPower.CheckedSOE.P6bad56ba299af2c53aa0fecddf667da9d105da3c1bfe44989a02ca74c64cba6c.target
theorem complete301 (s t : Fin 2) : SOESemantics.Equivalent step301 obs301 s t ↔ q301 s = q301 t := PerfectPower.CheckedSOE.P6bad56ba299af2c53aa0fecddf667da9d105da3c1bfe44989a02ca74c64cba6c.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pc6d0d833ba89557dc9543a9303d6906ad32d364d3f9c5eebce24b55698a26259
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: c6d0d833ba89557dc9543a9303d6906ad32d364d3f9c5eebce24b55698a26259; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 0 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pc6d0d833ba89557dc9543a9303d6906ad32d364d3f9c5eebce24b55698a26259

namespace PerfectPower.SOEModelPackets
def obs302 := PerfectPower.CheckedSOE.Pc6d0d833ba89557dc9543a9303d6906ad32d364d3f9c5eebce24b55698a26259.obs
def step302 := PerfectPower.CheckedSOE.Pc6d0d833ba89557dc9543a9303d6906ad32d364d3f9c5eebce24b55698a26259.step
def q302 := PerfectPower.CheckedSOE.Pc6d0d833ba89557dc9543a9303d6906ad32d364d3f9c5eebce24b55698a26259.q
def out302 := PerfectPower.CheckedSOE.Pc6d0d833ba89557dc9543a9303d6906ad32d364d3f9c5eebce24b55698a26259.out
def target302 := PerfectPower.CheckedSOE.Pc6d0d833ba89557dc9543a9303d6906ad32d364d3f9c5eebce24b55698a26259.target
theorem complete302 (s t : Fin 2) : SOESemantics.Equivalent step302 obs302 s t ↔ q302 s = q302 t := PerfectPower.CheckedSOE.Pc6d0d833ba89557dc9543a9303d6906ad32d364d3f9c5eebce24b55698a26259.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd52729a7cb347bde6bc745b49c977fb759b3ccd061a0814adf32095c329d99c2
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d52729a7cb347bde6bc745b49c977fb759b3ccd061a0814adf32095c329d99c2; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd52729a7cb347bde6bc745b49c977fb759b3ccd061a0814adf32095c329d99c2

namespace PerfectPower.SOEModelPackets
def obs303 := PerfectPower.CheckedSOE.Pd52729a7cb347bde6bc745b49c977fb759b3ccd061a0814adf32095c329d99c2.obs
def step303 := PerfectPower.CheckedSOE.Pd52729a7cb347bde6bc745b49c977fb759b3ccd061a0814adf32095c329d99c2.step
def q303 := PerfectPower.CheckedSOE.Pd52729a7cb347bde6bc745b49c977fb759b3ccd061a0814adf32095c329d99c2.q
def out303 := PerfectPower.CheckedSOE.Pd52729a7cb347bde6bc745b49c977fb759b3ccd061a0814adf32095c329d99c2.out
def target303 := PerfectPower.CheckedSOE.Pd52729a7cb347bde6bc745b49c977fb759b3ccd061a0814adf32095c329d99c2.target
theorem complete303 (s t : Fin 2) : SOESemantics.Equivalent step303 obs303 s t ↔ q303 s = q303 t := PerfectPower.CheckedSOE.Pd52729a7cb347bde6bc745b49c977fb759b3ccd061a0814adf32095c329d99c2.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pe76c426732a867e34fc2da21bce1d9530c0fba413d285fdb6d7a65dcbe145ce5
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: e76c426732a867e34fc2da21bce1d9530c0fba413d285fdb6d7a65dcbe145ce5; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pe76c426732a867e34fc2da21bce1d9530c0fba413d285fdb6d7a65dcbe145ce5

namespace PerfectPower.SOEModelPackets
def obs304 := PerfectPower.CheckedSOE.Pe76c426732a867e34fc2da21bce1d9530c0fba413d285fdb6d7a65dcbe145ce5.obs
def step304 := PerfectPower.CheckedSOE.Pe76c426732a867e34fc2da21bce1d9530c0fba413d285fdb6d7a65dcbe145ce5.step
def q304 := PerfectPower.CheckedSOE.Pe76c426732a867e34fc2da21bce1d9530c0fba413d285fdb6d7a65dcbe145ce5.q
def out304 := PerfectPower.CheckedSOE.Pe76c426732a867e34fc2da21bce1d9530c0fba413d285fdb6d7a65dcbe145ce5.out
def target304 := PerfectPower.CheckedSOE.Pe76c426732a867e34fc2da21bce1d9530c0fba413d285fdb6d7a65dcbe145ce5.target
theorem complete304 (s t : Fin 2) : SOESemantics.Equivalent step304 obs304 s t ↔ q304 s = q304 t := PerfectPower.CheckedSOE.Pe76c426732a867e34fc2da21bce1d9530c0fba413d285fdb6d7a65dcbe145ce5.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P8f50bc8d84d3f05a94fc3afe0ddb2657b124f63eb8acaf194214c9ca4383a841
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 8f50bc8d84d3f05a94fc3afe0ddb2657b124f63eb8acaf194214c9ca4383a841; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (none) else (if s = 0 then some 1 else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([0]) else (if j = 0 then [0] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P8f50bc8d84d3f05a94fc3afe0ddb2657b124f63eb8acaf194214c9ca4383a841

namespace PerfectPower.SOEModelPackets
def obs305 := PerfectPower.CheckedSOE.P8f50bc8d84d3f05a94fc3afe0ddb2657b124f63eb8acaf194214c9ca4383a841.obs
def step305 := PerfectPower.CheckedSOE.P8f50bc8d84d3f05a94fc3afe0ddb2657b124f63eb8acaf194214c9ca4383a841.step
def q305 := PerfectPower.CheckedSOE.P8f50bc8d84d3f05a94fc3afe0ddb2657b124f63eb8acaf194214c9ca4383a841.q
def out305 := PerfectPower.CheckedSOE.P8f50bc8d84d3f05a94fc3afe0ddb2657b124f63eb8acaf194214c9ca4383a841.out
def target305 := PerfectPower.CheckedSOE.P8f50bc8d84d3f05a94fc3afe0ddb2657b124f63eb8acaf194214c9ca4383a841.target
theorem complete305 (s t : Fin 2) : SOESemantics.Equivalent step305 obs305 s t ↔ q305 s = q305 t := PerfectPower.CheckedSOE.P8f50bc8d84d3f05a94fc3afe0ddb2657b124f63eb8acaf194214c9ca4383a841.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P5fee095d44a9cec8cdad4b35ea02ef3464d6b4c23108f904400f71a1a72d10af
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 5fee095d44a9cec8cdad4b35ea02ef3464d6b4c23108f904400f71a1a72d10af; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P5fee095d44a9cec8cdad4b35ea02ef3464d6b4c23108f904400f71a1a72d10af

namespace PerfectPower.SOEModelPackets
def obs306 := PerfectPower.CheckedSOE.P5fee095d44a9cec8cdad4b35ea02ef3464d6b4c23108f904400f71a1a72d10af.obs
def step306 := PerfectPower.CheckedSOE.P5fee095d44a9cec8cdad4b35ea02ef3464d6b4c23108f904400f71a1a72d10af.step
def q306 := PerfectPower.CheckedSOE.P5fee095d44a9cec8cdad4b35ea02ef3464d6b4c23108f904400f71a1a72d10af.q
def out306 := PerfectPower.CheckedSOE.P5fee095d44a9cec8cdad4b35ea02ef3464d6b4c23108f904400f71a1a72d10af.out
def target306 := PerfectPower.CheckedSOE.P5fee095d44a9cec8cdad4b35ea02ef3464d6b4c23108f904400f71a1a72d10af.target
theorem complete306 (s t : Fin 2) : SOESemantics.Equivalent step306 obs306 s t ↔ q306 s = q306 t := PerfectPower.CheckedSOE.P5fee095d44a9cec8cdad4b35ea02ef3464d6b4c23108f904400f71a1a72d10af.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4f357ef3b9e0e3963099fed3cefe83063d49469ee1175d655e72f1117f804aff
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4f357ef3b9e0e3963099fed3cefe83063d49469ee1175d655e72f1117f804aff; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4f357ef3b9e0e3963099fed3cefe83063d49469ee1175d655e72f1117f804aff

namespace PerfectPower.SOEModelPackets
def obs307 := PerfectPower.CheckedSOE.P4f357ef3b9e0e3963099fed3cefe83063d49469ee1175d655e72f1117f804aff.obs
def step307 := PerfectPower.CheckedSOE.P4f357ef3b9e0e3963099fed3cefe83063d49469ee1175d655e72f1117f804aff.step
def q307 := PerfectPower.CheckedSOE.P4f357ef3b9e0e3963099fed3cefe83063d49469ee1175d655e72f1117f804aff.q
def out307 := PerfectPower.CheckedSOE.P4f357ef3b9e0e3963099fed3cefe83063d49469ee1175d655e72f1117f804aff.out
def target307 := PerfectPower.CheckedSOE.P4f357ef3b9e0e3963099fed3cefe83063d49469ee1175d655e72f1117f804aff.target
theorem complete307 (s t : Fin 2) : SOESemantics.Equivalent step307 obs307 s t ↔ q307 s = q307 t := PerfectPower.CheckedSOE.P4f357ef3b9e0e3963099fed3cefe83063d49469ee1175d655e72f1117f804aff.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P25075dc43d6df7e15d0d9dc4c3847097e9e911fbb64f8e1f32ba3aaaf6465788
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 25075dc43d6df7e15d0d9dc4c3847097e9e911fbb64f8e1f32ba3aaaf6465788; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P25075dc43d6df7e15d0d9dc4c3847097e9e911fbb64f8e1f32ba3aaaf6465788

namespace PerfectPower.SOEModelPackets
def obs308 := PerfectPower.CheckedSOE.P25075dc43d6df7e15d0d9dc4c3847097e9e911fbb64f8e1f32ba3aaaf6465788.obs
def step308 := PerfectPower.CheckedSOE.P25075dc43d6df7e15d0d9dc4c3847097e9e911fbb64f8e1f32ba3aaaf6465788.step
def q308 := PerfectPower.CheckedSOE.P25075dc43d6df7e15d0d9dc4c3847097e9e911fbb64f8e1f32ba3aaaf6465788.q
def out308 := PerfectPower.CheckedSOE.P25075dc43d6df7e15d0d9dc4c3847097e9e911fbb64f8e1f32ba3aaaf6465788.out
def target308 := PerfectPower.CheckedSOE.P25075dc43d6df7e15d0d9dc4c3847097e9e911fbb64f8e1f32ba3aaaf6465788.target
theorem complete308 (s t : Fin 2) : SOESemantics.Equivalent step308 obs308 s t ↔ q308 s = q308 t := PerfectPower.CheckedSOE.P25075dc43d6df7e15d0d9dc4c3847097e9e911fbb64f8e1f32ba3aaaf6465788.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P03344a809f3cc6c28869775570024bdcb8f02c58447814c78920195cdd501152
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 03344a809f3cc6c28869775570024bdcb8f02c58447814c78920195cdd501152; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P03344a809f3cc6c28869775570024bdcb8f02c58447814c78920195cdd501152

namespace PerfectPower.SOEModelPackets
def obs309 := PerfectPower.CheckedSOE.P03344a809f3cc6c28869775570024bdcb8f02c58447814c78920195cdd501152.obs
def step309 := PerfectPower.CheckedSOE.P03344a809f3cc6c28869775570024bdcb8f02c58447814c78920195cdd501152.step
def q309 := PerfectPower.CheckedSOE.P03344a809f3cc6c28869775570024bdcb8f02c58447814c78920195cdd501152.q
def out309 := PerfectPower.CheckedSOE.P03344a809f3cc6c28869775570024bdcb8f02c58447814c78920195cdd501152.out
def target309 := PerfectPower.CheckedSOE.P03344a809f3cc6c28869775570024bdcb8f02c58447814c78920195cdd501152.target
theorem complete309 (s t : Fin 2) : SOESemantics.Equivalent step309 obs309 s t ↔ q309 s = q309 t := PerfectPower.CheckedSOE.P03344a809f3cc6c28869775570024bdcb8f02c58447814c78920195cdd501152.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P8bee8f028cffd4c6e1ea5c3d6f9cbe625f15783c00b893aa4b3798814dee9826
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 8bee8f028cffd4c6e1ea5c3d6f9cbe625f15783c00b893aa4b3798814dee9826; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P8bee8f028cffd4c6e1ea5c3d6f9cbe625f15783c00b893aa4b3798814dee9826

namespace PerfectPower.SOEModelPackets
def obs310 := PerfectPower.CheckedSOE.P8bee8f028cffd4c6e1ea5c3d6f9cbe625f15783c00b893aa4b3798814dee9826.obs
def step310 := PerfectPower.CheckedSOE.P8bee8f028cffd4c6e1ea5c3d6f9cbe625f15783c00b893aa4b3798814dee9826.step
def q310 := PerfectPower.CheckedSOE.P8bee8f028cffd4c6e1ea5c3d6f9cbe625f15783c00b893aa4b3798814dee9826.q
def out310 := PerfectPower.CheckedSOE.P8bee8f028cffd4c6e1ea5c3d6f9cbe625f15783c00b893aa4b3798814dee9826.out
def target310 := PerfectPower.CheckedSOE.P8bee8f028cffd4c6e1ea5c3d6f9cbe625f15783c00b893aa4b3798814dee9826.target
theorem complete310 (s t : Fin 2) : SOESemantics.Equivalent step310 obs310 s t ↔ q310 s = q310 t := PerfectPower.CheckedSOE.P8bee8f028cffd4c6e1ea5c3d6f9cbe625f15783c00b893aa4b3798814dee9826.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P0a82f7b2d41e5b992ed697954aa7e307965a73db2e7ff0347fcf4def8f03806d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 0a82f7b2d41e5b992ed697954aa7e307965a73db2e7ff0347fcf4def8f03806d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P0a82f7b2d41e5b992ed697954aa7e307965a73db2e7ff0347fcf4def8f03806d

namespace PerfectPower.SOEModelPackets
def obs311 := PerfectPower.CheckedSOE.P0a82f7b2d41e5b992ed697954aa7e307965a73db2e7ff0347fcf4def8f03806d.obs
def step311 := PerfectPower.CheckedSOE.P0a82f7b2d41e5b992ed697954aa7e307965a73db2e7ff0347fcf4def8f03806d.step
def q311 := PerfectPower.CheckedSOE.P0a82f7b2d41e5b992ed697954aa7e307965a73db2e7ff0347fcf4def8f03806d.q
def out311 := PerfectPower.CheckedSOE.P0a82f7b2d41e5b992ed697954aa7e307965a73db2e7ff0347fcf4def8f03806d.out
def target311 := PerfectPower.CheckedSOE.P0a82f7b2d41e5b992ed697954aa7e307965a73db2e7ff0347fcf4def8f03806d.target
theorem complete311 (s t : Fin 2) : SOESemantics.Equivalent step311 obs311 s t ↔ q311 s = q311 t := PerfectPower.CheckedSOE.P0a82f7b2d41e5b992ed697954aa7e307965a73db2e7ff0347fcf4def8f03806d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P7f37512035096fa00b02f7841add13bd5a302e0d6231db37a766dcc90da4114d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 7f37512035096fa00b02f7841add13bd5a302e0d6231db37a766dcc90da4114d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P7f37512035096fa00b02f7841add13bd5a302e0d6231db37a766dcc90da4114d

namespace PerfectPower.SOEModelPackets
def obs312 := PerfectPower.CheckedSOE.P7f37512035096fa00b02f7841add13bd5a302e0d6231db37a766dcc90da4114d.obs
def step312 := PerfectPower.CheckedSOE.P7f37512035096fa00b02f7841add13bd5a302e0d6231db37a766dcc90da4114d.step
def q312 := PerfectPower.CheckedSOE.P7f37512035096fa00b02f7841add13bd5a302e0d6231db37a766dcc90da4114d.q
def out312 := PerfectPower.CheckedSOE.P7f37512035096fa00b02f7841add13bd5a302e0d6231db37a766dcc90da4114d.out
def target312 := PerfectPower.CheckedSOE.P7f37512035096fa00b02f7841add13bd5a302e0d6231db37a766dcc90da4114d.target
theorem complete312 (s t : Fin 2) : SOESemantics.Equivalent step312 obs312 s t ↔ q312 s = q312 t := PerfectPower.CheckedSOE.P7f37512035096fa00b02f7841add13bd5a302e0d6231db37a766dcc90da4114d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pb3b02cff98ae398679e8447415d165c436245b6b6869b1d8d0ef39268dafc09c
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: b3b02cff98ae398679e8447415d165c436245b6b6869b1d8d0ef39268dafc09c; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pb3b02cff98ae398679e8447415d165c436245b6b6869b1d8d0ef39268dafc09c

namespace PerfectPower.SOEModelPackets
def obs313 := PerfectPower.CheckedSOE.Pb3b02cff98ae398679e8447415d165c436245b6b6869b1d8d0ef39268dafc09c.obs
def step313 := PerfectPower.CheckedSOE.Pb3b02cff98ae398679e8447415d165c436245b6b6869b1d8d0ef39268dafc09c.step
def q313 := PerfectPower.CheckedSOE.Pb3b02cff98ae398679e8447415d165c436245b6b6869b1d8d0ef39268dafc09c.q
def out313 := PerfectPower.CheckedSOE.Pb3b02cff98ae398679e8447415d165c436245b6b6869b1d8d0ef39268dafc09c.out
def target313 := PerfectPower.CheckedSOE.Pb3b02cff98ae398679e8447415d165c436245b6b6869b1d8d0ef39268dafc09c.target
theorem complete313 (s t : Fin 2) : SOESemantics.Equivalent step313 obs313 s t ↔ q313 s = q313 t := PerfectPower.CheckedSOE.Pb3b02cff98ae398679e8447415d165c436245b6b6869b1d8d0ef39268dafc09c.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P41d6088be9dfbc16ae3599fcf8379a0f0f162f1fba48c65203ddba04f7896dd7
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 41d6088be9dfbc16ae3599fcf8379a0f0f162f1fba48c65203ddba04f7896dd7; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 0) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P41d6088be9dfbc16ae3599fcf8379a0f0f162f1fba48c65203ddba04f7896dd7

namespace PerfectPower.SOEModelPackets
def obs314 := PerfectPower.CheckedSOE.P41d6088be9dfbc16ae3599fcf8379a0f0f162f1fba48c65203ddba04f7896dd7.obs
def step314 := PerfectPower.CheckedSOE.P41d6088be9dfbc16ae3599fcf8379a0f0f162f1fba48c65203ddba04f7896dd7.step
def q314 := PerfectPower.CheckedSOE.P41d6088be9dfbc16ae3599fcf8379a0f0f162f1fba48c65203ddba04f7896dd7.q
def out314 := PerfectPower.CheckedSOE.P41d6088be9dfbc16ae3599fcf8379a0f0f162f1fba48c65203ddba04f7896dd7.out
def target314 := PerfectPower.CheckedSOE.P41d6088be9dfbc16ae3599fcf8379a0f0f162f1fba48c65203ddba04f7896dd7.target
theorem complete314 (s t : Fin 2) : SOESemantics.Equivalent step314 obs314 s t ↔ q314 s = q314 t := PerfectPower.CheckedSOE.P41d6088be9dfbc16ae3599fcf8379a0f0f162f1fba48c65203ddba04f7896dd7.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P4478ba9c7bc98e3f5490aa8cffbadfe59d64f2cd25b48e9bc585a14ae291dcf8
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 4478ba9c7bc98e3f5490aa8cffbadfe59d64f2cd25b48e9bc585a14ae291dcf8; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (none))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (none)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P4478ba9c7bc98e3f5490aa8cffbadfe59d64f2cd25b48e9bc585a14ae291dcf8

namespace PerfectPower.SOEModelPackets
def obs315 := PerfectPower.CheckedSOE.P4478ba9c7bc98e3f5490aa8cffbadfe59d64f2cd25b48e9bc585a14ae291dcf8.obs
def step315 := PerfectPower.CheckedSOE.P4478ba9c7bc98e3f5490aa8cffbadfe59d64f2cd25b48e9bc585a14ae291dcf8.step
def q315 := PerfectPower.CheckedSOE.P4478ba9c7bc98e3f5490aa8cffbadfe59d64f2cd25b48e9bc585a14ae291dcf8.q
def out315 := PerfectPower.CheckedSOE.P4478ba9c7bc98e3f5490aa8cffbadfe59d64f2cd25b48e9bc585a14ae291dcf8.out
def target315 := PerfectPower.CheckedSOE.P4478ba9c7bc98e3f5490aa8cffbadfe59d64f2cd25b48e9bc585a14ae291dcf8.target
theorem complete315 (s t : Fin 2) : SOESemantics.Equivalent step315 obs315 s t ↔ q315 s = q315 t := PerfectPower.CheckedSOE.P4478ba9c7bc98e3f5490aa8cffbadfe59d64f2cd25b48e9bc585a14ae291dcf8.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P590f3fc603f0edee84fbec4bd7a2b7672ecec07514f577d2b04994286daa9bc1
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 590f3fc603f0edee84fbec4bd7a2b7672ecec07514f577d2b04994286daa9bc1; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 0))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 0))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P590f3fc603f0edee84fbec4bd7a2b7672ecec07514f577d2b04994286daa9bc1

namespace PerfectPower.SOEModelPackets
def obs316 := PerfectPower.CheckedSOE.P590f3fc603f0edee84fbec4bd7a2b7672ecec07514f577d2b04994286daa9bc1.obs
def step316 := PerfectPower.CheckedSOE.P590f3fc603f0edee84fbec4bd7a2b7672ecec07514f577d2b04994286daa9bc1.step
def q316 := PerfectPower.CheckedSOE.P590f3fc603f0edee84fbec4bd7a2b7672ecec07514f577d2b04994286daa9bc1.q
def out316 := PerfectPower.CheckedSOE.P590f3fc603f0edee84fbec4bd7a2b7672ecec07514f577d2b04994286daa9bc1.out
def target316 := PerfectPower.CheckedSOE.P590f3fc603f0edee84fbec4bd7a2b7672ecec07514f577d2b04994286daa9bc1.target
theorem complete316 (s t : Fin 2) : SOESemantics.Equivalent step316 obs316 s t ↔ q316 s = q316 t := PerfectPower.CheckedSOE.P590f3fc603f0edee84fbec4bd7a2b7672ecec07514f577d2b04994286daa9bc1.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P8e9c1bf0600433e4814bac0b593d17cb6e30e112b01c26b7f02e16fc883fa927
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 8e9c1bf0600433e4814bac0b593d17cb6e30e112b01c26b7f02e16fc883fa927; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 1))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then none else (some 1))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P8e9c1bf0600433e4814bac0b593d17cb6e30e112b01c26b7f02e16fc883fa927

namespace PerfectPower.SOEModelPackets
def obs317 := PerfectPower.CheckedSOE.P8e9c1bf0600433e4814bac0b593d17cb6e30e112b01c26b7f02e16fc883fa927.obs
def step317 := PerfectPower.CheckedSOE.P8e9c1bf0600433e4814bac0b593d17cb6e30e112b01c26b7f02e16fc883fa927.step
def q317 := PerfectPower.CheckedSOE.P8e9c1bf0600433e4814bac0b593d17cb6e30e112b01c26b7f02e16fc883fa927.q
def out317 := PerfectPower.CheckedSOE.P8e9c1bf0600433e4814bac0b593d17cb6e30e112b01c26b7f02e16fc883fa927.out
def target317 := PerfectPower.CheckedSOE.P8e9c1bf0600433e4814bac0b593d17cb6e30e112b01c26b7f02e16fc883fa927.target
theorem complete317 (s t : Fin 2) : SOESemantics.Equivalent step317 obs317 s t ↔ q317 s = q317 t := PerfectPower.CheckedSOE.P8e9c1bf0600433e4814bac0b593d17cb6e30e112b01c26b7f02e16fc883fa927.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P48d5377a9ec243b7d7fbd1cd78af77d960c06be3b7e905824ddf9710bbfffbc6
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 48d5377a9ec243b7d7fbd1cd78af77d960c06be3b7e905824ddf9710bbfffbc6; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P48d5377a9ec243b7d7fbd1cd78af77d960c06be3b7e905824ddf9710bbfffbc6

namespace PerfectPower.SOEModelPackets
def obs318 := PerfectPower.CheckedSOE.P48d5377a9ec243b7d7fbd1cd78af77d960c06be3b7e905824ddf9710bbfffbc6.obs
def step318 := PerfectPower.CheckedSOE.P48d5377a9ec243b7d7fbd1cd78af77d960c06be3b7e905824ddf9710bbfffbc6.step
def q318 := PerfectPower.CheckedSOE.P48d5377a9ec243b7d7fbd1cd78af77d960c06be3b7e905824ddf9710bbfffbc6.q
def out318 := PerfectPower.CheckedSOE.P48d5377a9ec243b7d7fbd1cd78af77d960c06be3b7e905824ddf9710bbfffbc6.out
def target318 := PerfectPower.CheckedSOE.P48d5377a9ec243b7d7fbd1cd78af77d960c06be3b7e905824ddf9710bbfffbc6.target
theorem complete318 (s t : Fin 2) : SOESemantics.Equivalent step318 obs318 s t ↔ q318 s = q318 t := PerfectPower.CheckedSOE.P48d5377a9ec243b7d7fbd1cd78af77d960c06be3b7e905824ddf9710bbfffbc6.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pff5c242e5a2b6680ab6211f7ff7eba28f204d37db9c4b6441364fa7805f36b8d
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: ff5c242e5a2b6680ab6211f7ff7eba28f204d37db9c4b6441364fa7805f36b8d; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pff5c242e5a2b6680ab6211f7ff7eba28f204d37db9c4b6441364fa7805f36b8d

namespace PerfectPower.SOEModelPackets
def obs319 := PerfectPower.CheckedSOE.Pff5c242e5a2b6680ab6211f7ff7eba28f204d37db9c4b6441364fa7805f36b8d.obs
def step319 := PerfectPower.CheckedSOE.Pff5c242e5a2b6680ab6211f7ff7eba28f204d37db9c4b6441364fa7805f36b8d.step
def q319 := PerfectPower.CheckedSOE.Pff5c242e5a2b6680ab6211f7ff7eba28f204d37db9c4b6441364fa7805f36b8d.q
def out319 := PerfectPower.CheckedSOE.Pff5c242e5a2b6680ab6211f7ff7eba28f204d37db9c4b6441364fa7805f36b8d.out
def target319 := PerfectPower.CheckedSOE.Pff5c242e5a2b6680ab6211f7ff7eba28f204d37db9c4b6441364fa7805f36b8d.target
theorem complete319 (s t : Fin 2) : SOESemantics.Equivalent step319 obs319 s t ↔ q319 s = q319 t := PerfectPower.CheckedSOE.Pff5c242e5a2b6680ab6211f7ff7eba28f204d37db9c4b6441364fa7805f36b8d.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P5505807440d6e8215f9f7c7e74f72facba74305e211c63b0c3162b102fd4f569
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 5505807440d6e8215f9f7c7e74f72facba74305e211c63b0c3162b102fd4f569; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 0 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P5505807440d6e8215f9f7c7e74f72facba74305e211c63b0c3162b102fd4f569

namespace PerfectPower.SOEModelPackets
def obs320 := PerfectPower.CheckedSOE.P5505807440d6e8215f9f7c7e74f72facba74305e211c63b0c3162b102fd4f569.obs
def step320 := PerfectPower.CheckedSOE.P5505807440d6e8215f9f7c7e74f72facba74305e211c63b0c3162b102fd4f569.step
def q320 := PerfectPower.CheckedSOE.P5505807440d6e8215f9f7c7e74f72facba74305e211c63b0c3162b102fd4f569.q
def out320 := PerfectPower.CheckedSOE.P5505807440d6e8215f9f7c7e74f72facba74305e211c63b0c3162b102fd4f569.out
def target320 := PerfectPower.CheckedSOE.P5505807440d6e8215f9f7c7e74f72facba74305e211c63b0c3162b102fd4f569.target
theorem complete320 (s t : Fin 2) : SOESemantics.Equivalent step320 obs320 s t ↔ q320 s = q320 t := PerfectPower.CheckedSOE.P5505807440d6e8215f9f7c7e74f72facba74305e211c63b0c3162b102fd4f569.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.Pd403a98898a4e92320c6507c4c229e6cbcd9aa395136b527d838f2fa60e4a364
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: d403a98898a4e92320c6507c4c229e6cbcd9aa395136b527d838f2fa60e4a364; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (none))
def q (s : Fin 2) : Fin 2 := if s = 0 then 0 else (1)
def out (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def target (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (none))
def experiment (i j : Fin 2) : List (Fin 2) := if i = 0 then if j = 0 then [] else ([1]) else (if j = 0 then [1] else ([]))
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 2, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.Pd403a98898a4e92320c6507c4c229e6cbcd9aa395136b527d838f2fa60e4a364

namespace PerfectPower.SOEModelPackets
def obs321 := PerfectPower.CheckedSOE.Pd403a98898a4e92320c6507c4c229e6cbcd9aa395136b527d838f2fa60e4a364.obs
def step321 := PerfectPower.CheckedSOE.Pd403a98898a4e92320c6507c4c229e6cbcd9aa395136b527d838f2fa60e4a364.step
def q321 := PerfectPower.CheckedSOE.Pd403a98898a4e92320c6507c4c229e6cbcd9aa395136b527d838f2fa60e4a364.q
def out321 := PerfectPower.CheckedSOE.Pd403a98898a4e92320c6507c4c229e6cbcd9aa395136b527d838f2fa60e4a364.out
def target321 := PerfectPower.CheckedSOE.Pd403a98898a4e92320c6507c4c229e6cbcd9aa395136b527d838f2fa60e4a364.target
theorem complete321 (s t : Fin 2) : SOESemantics.Equivalent step321 obs321 s t ↔ q321 s = q321 t := PerfectPower.CheckedSOE.Pd403a98898a4e92320c6507c4c229e6cbcd9aa395136b527d838f2fa60e4a364.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P501490385505ba9a703e99293e4bbf71a3a5ae7efdb0a3f521fb00da4538c219
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 501490385505ba9a703e99293e4bbf71a3a5ae7efdb0a3f521fb00da4538c219; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 0))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P501490385505ba9a703e99293e4bbf71a3a5ae7efdb0a3f521fb00da4538c219

namespace PerfectPower.SOEModelPackets
def obs322 := PerfectPower.CheckedSOE.P501490385505ba9a703e99293e4bbf71a3a5ae7efdb0a3f521fb00da4538c219.obs
def step322 := PerfectPower.CheckedSOE.P501490385505ba9a703e99293e4bbf71a3a5ae7efdb0a3f521fb00da4538c219.step
def q322 := PerfectPower.CheckedSOE.P501490385505ba9a703e99293e4bbf71a3a5ae7efdb0a3f521fb00da4538c219.q
def out322 := PerfectPower.CheckedSOE.P501490385505ba9a703e99293e4bbf71a3a5ae7efdb0a3f521fb00da4538c219.out
def target322 := PerfectPower.CheckedSOE.P501490385505ba9a703e99293e4bbf71a3a5ae7efdb0a3f521fb00da4538c219.target
theorem complete322 (s t : Fin 2) : SOESemantics.Equivalent step322 obs322 s t ↔ q322 s = q322 t := PerfectPower.CheckedSOE.P501490385505ba9a703e99293e4bbf71a3a5ae7efdb0a3f521fb00da4538c219.complete s t
end PerfectPower.SOEModelPackets

namespace PerfectPower.CheckedSOE.P779c92c10ae85ecff62bec4cb3720cf4259a04ca8c27f8a0744b563ee7e34537
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
-- Source/packet SHA256: 779c92c10ae85ecff62bec4cb3720cf4259a04ca8c27f8a0744b563ee7e34537; encodings are recorded in the compiler receipt.
def obs (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def step (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a = 0 then if s = 0 then some 1 else (some 1) else (if s = 0 then some 1 else (some 1))
def q (s : Fin 2) : Fin 1 := if s = 0 then 0 else (0)
def out (s : Fin 1) : Fin 1 := 0
def target (s : Fin 1) (a : Fin 2) : Option (Fin 1) := if a = 0 then some 0 else (some 0)
def experiment (i j : Fin 1) : List (Fin 2) := []
theorem observation_preserved : ∀ s, obs s = out (q s) := by decide
theorem transition_preserved : ∀ s a, (step s a).map q = target (q s) a := by decide
theorem separated : ∀ i j : Fin 1, i ≠ j →
    SOESemantics.behavior target out i (experiment i j) ≠
    SOESemantics.behavior target out j (experiment i j) := by decide
theorem complete (s t : Fin 2) :
    SOESemantics.Equivalent step obs s t ↔ q s = q t := by
  apply SOESemantics.quotient_complete step target obs out q observation_preserved transition_preserved
  intro u v h
  refine ⟨experiment (q u) (q v), ?_⟩
  rw [SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved,
      SOESemantics.behavior_transport step target obs out q observation_preserved transition_preserved]
  exact separated (q u) (q v) h
end PerfectPower.CheckedSOE.P779c92c10ae85ecff62bec4cb3720cf4259a04ca8c27f8a0744b563ee7e34537

namespace PerfectPower.SOEModelPackets
def obs323 := PerfectPower.CheckedSOE.P779c92c10ae85ecff62bec4cb3720cf4259a04ca8c27f8a0744b563ee7e34537.obs
def step323 := PerfectPower.CheckedSOE.P779c92c10ae85ecff62bec4cb3720cf4259a04ca8c27f8a0744b563ee7e34537.step
def q323 := PerfectPower.CheckedSOE.P779c92c10ae85ecff62bec4cb3720cf4259a04ca8c27f8a0744b563ee7e34537.q
def out323 := PerfectPower.CheckedSOE.P779c92c10ae85ecff62bec4cb3720cf4259a04ca8c27f8a0744b563ee7e34537.out
def target323 := PerfectPower.CheckedSOE.P779c92c10ae85ecff62bec4cb3720cf4259a04ca8c27f8a0744b563ee7e34537.target
theorem complete323 (s t : Fin 2) : SOESemantics.Equivalent step323 obs323 s t ↔ q323 s = q323 t := PerfectPower.CheckedSOE.P779c92c10ae85ecff62bec4cb3720cf4259a04ca8c27f8a0744b563ee7e34537.complete s t
end PerfectPower.SOEModelPackets
