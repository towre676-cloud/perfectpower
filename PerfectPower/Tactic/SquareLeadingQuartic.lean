import PerfectPower.QuarticCutoff
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
    let ql := |PerfectPower.SquareLeadingQuartic.qL Lv|
    let qa := |PerfectPower.SquareLeadingQuartic.qa Lv uv|
    let qb := |PerfectPower.SquareLeadingQuartic.qb Lv uv vv|
    let rc := PerfectPower.SquareLeadingQuartic.rc Lv uv vv wv
    let rd := PerfectPower.SquareLeadingQuartic.rd Lv uv vv zv
    let mut bound : Int := 0
    while !(qa+|rc| ≤ ql*bound && (qa+|rc|)*bound+qb+|rd| < ql*bound^2) do
      bound := bound+1
      if 2*bound+1 > 100000 then throwError "complete cutoff interval exceeds native work limit"
    let cutoff := quote bound
    let interval := (List.range (2*bound+1).toNat).map fun i => (i:Int)-bound
    let exceptional := if rc != 0 && rc*((-rd)/rc)+rd == 0 then [(-rd)/rc] else []
    let xs := (interval++exceptional).eraseDups
    let values : List (Int × Int) := xs.flatMap fun x =>
      ((PerfectPower.LinearPerturbation.squareRoots
        (PerfectPower.SquareLeadingQuartic.value Lv uv vv wv zv x)).sort (· ≤ ·)).map fun y => (x,y)
    let data := quote values
    let theoremName := mkIdent (name.getId.appendAfter "_complete")
    elabCommand (← `(def $name : Finset (ℤ × ℤ) := ($data : List (ℤ × ℤ)).toFinset))
    elabCommand (← `(set_option maxRecDepth 100000 in theorem $theoremName (x y : ℤ) :
      y^2=PerfectPower.SquareLeadingQuartic.value $L $u $v $w $z x ↔ (x,y) ∈ $name := by
      have hp : PerfectPower.QuarticCutoff.points $L $u $v $w $z $cutoff = $name := by decide +kernel
      rw [← hp]
      exact PerfectPower.QuarticCutoff.complete $L $u $v $w $z $cutoff
        (by norm_num)
        (by norm_num [PerfectPower.SquareLeadingQuartic.qa,PerfectPower.SquareLeadingQuartic.rc,
          PerfectPower.SquareLeadingQuartic.qL,PerfectPower.SquareLeadingQuartic.qb,
          PerfectPower.SquareLeadingQuartic.scale])
        (by norm_num [PerfectPower.SquareLeadingQuartic.qa,PerfectPower.SquareLeadingQuartic.rc,
          PerfectPower.SquareLeadingQuartic.qL,PerfectPower.SquareLeadingQuartic.qb,
          PerfectPower.SquareLeadingQuartic.rd,PerfectPower.SquareLeadingQuartic.scale])
        (by norm_num [PerfectPower.SquareLeadingQuartic.rc,
          PerfectPower.SquareLeadingQuartic.rd,PerfectPower.SquareLeadingQuartic.scale,
          PerfectPower.SquareLeadingQuartic.qa,PerfectPower.SquareLeadingQuartic.qb]) x y))
  | _ => throwUnsupportedSyntax
