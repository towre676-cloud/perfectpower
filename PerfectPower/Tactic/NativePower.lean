import PerfectPower.NativeNearSquare

/-! Native finite enumeration for the explicitly supported near-square family.
The expected point set is computed and checked by kernel reduction, not native_decide. -/
syntax "decide_perfect_power " term "," term "," term " => " term : tactic

macro_rules
  | `(tactic| decide_perfect_power $a, $b, $k => $expected) =>
    `(tactic| (
      have hpoints : PerfectPower.NativeNearSquare.points $a $b $k = $expected := by
        decide +kernel
      rw [← hpoints]
      exact PerfectPower.NativeNearSquare.complete $a $b $k (by norm_num) _ _))

open Lean Elab Command Term Meta

/-- Compute an explicit finite list in Lean and emit its kernel-checked completeness theorem.
For example: `native_near_square quartic for 0, 0, 1`. -/
syntax (name := nativeNearSquare) "native_near_square " ident " for " term "," term "," term : command

@[command_elab nativeNearSquare]
unsafe def elabNativeNearSquare : CommandElab
  | `(native_near_square $name for $a, $b, $k) => do
    let evalInt (stx : Syntax) : CommandElabM Int := liftTermElabM do
      let expr ← Term.elabTermEnsuringType stx (mkConst ``Int)
      Term.synthesizeSyntheticMVarsNoPostponing
      let expr ← instantiateMVars expr
      Meta.evalExpr Int (mkConst ``Int) expr
    let av ← evalInt a
    let bv ← evalInt b
    let kv ← evalInt k
    if kv == 0 then throwError "k = 0 is an infinite square family; no finite list is emitted"
    let bound := PerfectPower.NativeNearSquare.xBound av bv kv
    let xs := (List.range (2*bound+1).toNat).map fun i => (i : Int)-bound
    let ys := (List.range (2*kv.natAbs+1)).map fun i => (i : Int)-|kv|
    let values : List (Int × Int) := xs.flatMap fun x => ys.filterMap fun y =>
      if PerfectPower.NativeNearSquare.equation av bv kv x y then some (x,y) else none
    let data := quote values
    let theoremName := mkIdent (name.getId.appendAfter "_complete")
    elabCommand (← `(def $name : Finset (ℤ × ℤ) := ($data : List (ℤ × ℤ)).toFinset))
    elabCommand (← `(theorem $theoremName (x y : ℤ) :
        y^2=(x^2+$a*x+$b)^2+$k ↔ (x,y) ∈ $name := by
      decide_perfect_power $a, $b, $k => $name))
  | _ => throwUnsupportedSyntax
