import PerfectPower.Generated.BlastAlignmentSOE
import PerfectPower.BlastAlignment
namespace PerfectPower.Generated.BlastPathCounts
open PerfectPower.CheckedSOE.P4e1a7f8a8c39d16135844ab08dbd8f7051b1b58b9fdfb47df2645fc3a1470556
def remaining (s : Fin 13) : Nat := if s = 0 then 4 else (if s = 1 then 2 else (if s = 2 then 3 else (if s = 3 then 3 else (if s = 4 then 0 else (if s = 5 then 1 else (if s = 6 then 1 else (if s = 7 then 1 else (if s = 8 then 2 else (if s = 9 then 1 else (if s = 10 then 2 else (if s = 11 then 0 else (0))))))))))))
theorem decreases : ∀ s a t, step s a = some t → remaining t < remaining s := by decide
theorem terminal_disabled : ∀ s a, obs s = 1 → step s a = none := by decide
def countFuel : Nat → Fin 13 → Nat
  | 0, s => if obs s = 1 then 1 else 0
  | n+1, s => if obs s = 1 then 1 else
      ((List.finRange 6).map (fun a => match step s a with
        | none => 0
        | some t => countFuel n t)).sum
theorem count_at_root : countFuel 4 0 = 3 := by decide
theorem every_word_bounded (s t : Fin 13) (word : List (Fin 6))
    (h : PerfectPower.SOESemantics.run step s word = some t) : word.length ≤ remaining s := by
  exact PerfectPower.BlastAlignment.path_length_bound step remaining decreases s t word h
#print axioms decreases
#print axioms terminal_disabled
#print axioms count_at_root
#print axioms every_word_bounded
end PerfectPower.Generated.BlastPathCounts
