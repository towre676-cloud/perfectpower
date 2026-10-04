import PerfectPower.NativePolynomialSquare

/-! Native arbitrary-degree automation for `y² = P(x)² + k`, with ascending coefficients.
The elaborator proposes a list; `decide +kernel` checks it independently. -/
syntax "decide_polynomial_square " term "," term " => " term : tactic
macro_rules
  | `(tactic| decide_polynomial_square $as, $k => $expected) =>
    `(tactic| (
      have hpoints : PerfectPower.NativePolynomialSquare.points $as $k = $expected := by
        decide +kernel
      rw [← hpoints]
      exact PerfectPower.NativePolynomialSquare.complete $as $k
        (by decide +kernel) (by decide +kernel) (by norm_num) _ _))

open Lean Elab Command Term Meta

/-- Generate a point set and an unconditional completeness theorem.
Example: `native_polynomial_square cubic for [0, 0, 0, 2], 1`. -/
syntax (name := nativePolynomialSquare) "native_polynomial_square " ident " for " term "," term : command

@[command_elab nativePolynomialSquare]
unsafe def elabNativePolynomialSquare : CommandElab
  | `(native_polynomial_square $name for $as, $k) => do
    let coefficients ← liftTermElabM do
      let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``Int)
      let e ← Term.elabTermEnsuringType as ty
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.evalExpr (List Int) ty (← instantiateMVars e)
    let kv ← liftTermElabM do
      let e ← Term.elabTermEnsuringType k (mkConst ``Int)
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.evalExpr Int (mkConst ``Int) (← instantiateMVars e)
    if coefficients.length < 2 then
      throwError "at least two coefficients are required for a nonconstant polynomial"
    if !(PerfectPower.NativePolynomialSquare.valid coefficients) then
      throwError "the final coefficient must be nonzero; remove trailing zeros"
    if kv == 0 then
      throwError "k = 0 is an infinite square family; no finite list is emitted"
    let bound := PerfectPower.NativePolynomialSquare.bound coefficients kv
    let xs := (List.range (2 * bound + 1).toNat).map fun i => (i : Int) - bound
    let ys := (List.range (2 * kv.natAbs + 1)).map fun i => (i : Int) - |kv|
    let values : List (Int × Int) := xs.flatMap fun x => ys.filterMap fun y =>
      if y^2 = (PerfectPower.NativePolynomialSquare.eval coefficients x)^2 + kv
        then some (x,y) else none
    let data := quote values
    let theoremName := mkIdent (name.getId.appendAfter "_complete")
    elabCommand (← `(def $name : Finset (ℤ × ℤ) := ($data : List (ℤ × ℤ)).toFinset))
    elabCommand (← `(theorem $theoremName (x y : ℤ) :
      y^2 = (PerfectPower.NativePolynomialSquare.eval $as x)^2 + $k ↔ (x,y) ∈ $name := by
      decide_polynomial_square $as, $k => $name))
  | _ => throwUnsupportedSyntax
