import PerfectPower.LinearPerturbation
import Mathlib.Data.Finset.Sort
open Lean Elab Command Term Meta

syntax (name := nativeLinearPerturbation) "native_linear_perturbation " ident " for "
  term "," term "," term "," term "," term : command

@[command_elab nativeLinearPerturbation]
unsafe def elabNativeLinearPerturbation : CommandElab
  | `(native_linear_perturbation $name for $L, $a, $b, $c, $d) => do
    let args ← liftTermElabM do
      let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``Int)
      let e ← Term.elabTermEnsuringType (← `([$L,$a,$b,$c,$d])) ty
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.evalExpr (List Int) ty (← instantiateMVars e)
    let [Lv,av,bv,cv,dv] := args | throwError "five integer parameters required"
    if Lv == 0 then throwError "quadratic leading coefficient must be nonzero"
    if cv == 0 && dv == 0 then throwError "zero perturbation is an infinite family"
    let bound := PerfectPower.LinearPerturbation.bound av bv cv dv
    if 2*bound+1 > 100000 then throwError "complete interval exceeds native work limit"
    let values : List (Int × Int) := (List.range (2*bound+1).toNat).flatMap fun i =>
      let x := (i:Int)-bound
      ((PerfectPower.LinearPerturbation.squareRoots
        (PerfectPower.LinearPerturbation.value Lv av bv cv dv x)).sort (· ≤ ·)).map fun y => (x,y)
    let data := quote values
    let theoremName := mkIdent (name.getId.appendAfter "_complete")
    elabCommand (← `(def $name : Finset (ℤ × ℤ) := ($data : List (ℤ × ℤ)).toFinset))
    elabCommand (← `(set_option maxRecDepth 100000 in theorem $theoremName (x y : ℤ) :
      y^2 = PerfectPower.LinearPerturbation.value $L $a $b $c $d x ↔ (x,y) ∈ $name := by
      have hp : PerfectPower.LinearPerturbation.points $L $a $b $c $d = $name := by decide +kernel
      rw [← hp]
      exact PerfectPower.LinearPerturbation.complete $L $a $b $c $d
        (by norm_num) (by norm_num) x y))
  | _ => throwUnsupportedSyntax
