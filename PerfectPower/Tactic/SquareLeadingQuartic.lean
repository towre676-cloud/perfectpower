import PerfectPower.SquareLeadingQuartic
import Mathlib.Data.Finset.Sort
open Lean Elab Command Term Meta
syntax (name := nativeSquareLeadingQuartic) "native_square_leading_quartic " ident " for "
  term "," term "," term "," term "," term : command
@[command_elab nativeSquareLeadingQuartic]
unsafe def elabNativeSquareLeadingQuartic : CommandElab
  | `(native_square_leading_quartic $name for $L, $u, $v, $w, $z) => do
    let args ← liftTermElabM do
      let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``Int)
      let e ← Term.elabTermEnsuringType (← `([$L,$u,$v,$w,$z])) ty
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.evalExpr (List Int) ty (← instantiateMVars e)
    let [Lv,uv,vv,wv,zv] := args | throwError "five integer parameters required"
    if Lv == 0 then throwError "leading square root must be nonzero"
    if PerfectPower.SquareLeadingQuartic.rc Lv uv vv wv == 0 &&
       PerfectPower.SquareLeadingQuartic.rd Lv uv vv zv == 0 then
      throwError "zero normalized perturbation is excluded"
    let bound := PerfectPower.SquareLeadingQuartic.bound Lv uv vv wv zv
    if 2*bound+1 > 100000 then throwError "complete normalized interval exceeds native work limit"
    let values : List (Int × Int) := (List.range (2*bound+1).toNat).flatMap fun i =>
      let x := (i:Int)-bound
      ((PerfectPower.LinearPerturbation.squareRoots
        (PerfectPower.SquareLeadingQuartic.value Lv uv vv wv zv x)).sort (· ≤ ·)).map fun y => (x,y)
    let data := quote values
    let theoremName := mkIdent (name.getId.appendAfter "_complete")
    elabCommand (← `(def $name : Finset (ℤ × ℤ) := ($data : List (ℤ × ℤ)).toFinset))
    elabCommand (← `(set_option maxRecDepth 100000 in theorem $theoremName (x y : ℤ) :
      y^2=PerfectPower.SquareLeadingQuartic.value $L $u $v $w $z x ↔ (x,y) ∈ $name := by
      have hp : PerfectPower.SquareLeadingQuartic.points $L $u $v $w $z = $name := by decide +kernel
      rw [← hp]
      exact PerfectPower.SquareLeadingQuartic.complete $L $u $v $w $z
        (by norm_num) (by norm_num [PerfectPower.SquareLeadingQuartic.rc,
          PerfectPower.SquareLeadingQuartic.rd,PerfectPower.SquareLeadingQuartic.scale,
          PerfectPower.SquareLeadingQuartic.qa,PerfectPower.SquareLeadingQuartic.qb]) x y))
  | _ => throwUnsupportedSyntax
