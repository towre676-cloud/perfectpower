import Std
namespace PerfectPower.CheckedGraph.Pc627e892f2076f664ad60be0c41bc93556a188fb4931ae918b5d0d23251233e3
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
def satisfies (x : Nat) : Bool := ((x / 1 % 2 == 1) || (x / 2 % 2 == 1)) && ((x / 2 % 2 == 0) || (x / 4 % 2 == 1)) && ((x / 4 % 2 == 1) || (x / 8 % 2 == 1))
theorem exact_count : ((List.range 16).filter satisfies).length = 7 := by decide
#print axioms exact_count
end PerfectPower.CheckedGraph.Pc627e892f2076f664ad60be0c41bc93556a188fb4931ae918b5d0d23251233e3
