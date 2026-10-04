import PerfectPower.RungePolynomial
import Mathlib.Data.Finset.Sort

/-! Native recognition of expanded even-degree polynomials with positive square
leading coefficient. Proposed decompositions and point lists are kernel checked. -/
open Lean Elab Command Term Meta

namespace PerfectPower.RungeAutomation

def trim (xs : List Int) : List Int := (xs.reverse.dropWhile (· == 0)).reverse

/-- Exact rational square-root truncation at infinity followed by denominator clearing.
This computation proposes data; the emitted polynomial identity proves it independently. -/
def decompose (xs : List Int) : Except String (Int × List Int × List Int) := Id.run do
  let F := trim xs
  if F.length < 3 then return .error "a nonconstant polynomial of positive even degree is required"
  let degree := F.length-1
  if degree % 2 != 0 then return .error "odd degree is outside this Runge recognizer"
  let lead := F.getLast!
  if lead ≤ 0 then return .error "a positive square leading coefficient is required"
  let root := FastDivisors.sqrt lead.toNat
  if (root : Int)^2 != lead then return .error "the leading coefficient is not an integer square"
  let n := degree/2
  let mut Q : Array Rat := Array.replicate (n+1) 0
  Q := Q.set! n (root : Rat)
  for i in List.range n do
    let k := n-1-i
    let target := n+k
    let mut known : Rat := 0
    for j in List.range (n+1) do
      let l := target-j
      if l ≤ n then known := known+Q[j]!*Q[l]!
    Q := Q.set! k ((((F[target]! : Int) : Rat)-known)/(2*(root:Rat)))
  let a := Q.toList.foldl (fun d q => Nat.lcm d q.den) 1
  let qi := Q.toList.map fun q => (a:Int)*q.num/(q.den:Int)
  let R := (List.range (degree+1)).map fun k =>
    let square := (List.range (n+1)).foldl (fun s j =>
      if j ≤ k && k-j ≤ n then s+qi[j]!*qi[k-j]! else s) (0:Int)
    (a:Int)^2*F[k]!-square
  return .ok ((a:Int),qi,trim R)

end PerfectPower.RungeAutomation

syntax (name := nativeRunge) "native_runge " ident " for " term : command
syntax (name := nativeRungeCertificate) "native_runge_certificate " ident " for " term : command

/-- Generate the decomposition and unconditional bound alone, or also enumerate points. -/
unsafe def elaborateRunge (name : Ident) (input : TSyntax `term) (enumerate : Bool) : CommandElabM Unit := do
  let F ← liftTermElabM do
    let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``Int)
    let e ← Term.elabTermEnsuringType input ty
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.evalExpr (List Int) ty (← instantiateMVars e)
  let (a,q,r) ← match PerfectPower.RungeAutomation.decompose F with
    | .ok data => pure data
    | .error message => throwError "{message}"
  let bound := PerfectPower.RungePolynomial.bound q r
  if enumerate && !r.isEmpty && 2*bound+1 > 10001 then
    throwError "the complete interval exceeds 10001 coordinates; use native_runge_certificate for the decomposition and bound"
  let sa := quote a
  let sq := quote q
  let sr := quote r
  let identityName := mkIdent (name.getId.appendAfter "_decomposition")
  let boundName := mkIdent (name.getId.appendAfter "_bound")
  let theoremName := mkIdent (name.getId.appendAfter "_complete")
  elabCommand (← `(theorem $identityName (x : ℤ) :
    ($sa : ℤ)^2*PerfectPower.NativePolynomialSquare.eval $input x =
      (PerfectPower.NativePolynomialSquare.eval $sq x)^2+
        PerfectPower.NativePolynomialSquare.eval $sr x := by
    norm_num [PerfectPower.NativePolynomialSquare.eval]
    ring))
  if r.isEmpty then
    elabCommand (← `(theorem $theoremName (x y : ℤ) :
      y^2=PerfectPower.NativePolynomialSquare.eval $input x ↔
        ($sa : ℤ)*y=PerfectPower.NativePolynomialSquare.eval $sq x ∨
        ($sa : ℤ)*y= -PerfectPower.NativePolynomialSquare.eval $sq x := by
      exact PerfectPower.RungePolynomial.square_family $input $sq $sa (by norm_num)
        (by intro x; simpa [PerfectPower.NativePolynomialSquare.eval] using $identityName x) x y))
    return
  let sb := quote bound
  elabCommand (← `(theorem $boundName (x y : ℤ)
    (h : y^2=PerfectPower.NativePolynomialSquare.eval $input x) :
    |x| ≤ ($sb : ℤ) := by
    have hs : (($sa : ℤ)*y)^2=(PerfectPower.NativePolynomialSquare.eval $sq x)^2+
      PerfectPower.NativePolynomialSquare.eval $sr x := by rw [← $identityName x,← h]; ring
    exact PerfectPower.RungePolynomial.coordinate_bound $sq $sr (($sa : ℤ)*y) x
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hs))
  if !enumerate then
    elabCommand (← `(theorem $theoremName (x y : ℤ) :
      y^2=PerfectPower.NativePolynomialSquare.eval $input x ↔
        (x,y) ∈ PerfectPower.RungePolynomial.points $input $sq $sr := by
      exact PerfectPower.RungePolynomial.complete $input $sq $sr $sa
        (by decide +kernel) (by decide +kernel) (by decide +kernel) $identityName x y))
    return
  let xs := (List.range (2*bound+1).toNat).map fun i => (i:Int)-bound
  let exceptional := (PerfectPower.NativePolynomialRoots.roots r).sort (· ≤ ·)
  let values : List (Int × Int) := (xs++exceptional).eraseDups.flatMap fun x =>
    (PerfectPower.LinearPerturbation.squareRoots
      (PerfectPower.NativePolynomialSquare.eval F x)).sort (· ≤ ·) |>.map fun y => (x,y)
  let data := quote values
  elabCommand (← `(def $name : Finset (ℤ × ℤ) := ($data : List (ℤ × ℤ)).toFinset))
  elabCommand (← `(set_option maxRecDepth 100000 in theorem $theoremName (x y : ℤ) :
    y^2=PerfectPower.NativePolynomialSquare.eval $input x ↔ (x,y) ∈ $name := by
    have hp : PerfectPower.RungePolynomial.points $input $sq $sr=$name := by decide +kernel
    rw [← hp]
    exact PerfectPower.RungePolynomial.complete $input $sq $sr $sa
      (by decide +kernel) (by decide +kernel) (by decide +kernel) $identityName x y))

@[command_elab nativeRunge]
unsafe def elabNativeRunge : CommandElab
  | `(native_runge $name for $input) => elaborateRunge name input true
  | _ => throwUnsupportedSyntax

@[command_elab nativeRungeCertificate]
unsafe def elabNativeRungeCertificate : CommandElab
  | `(native_runge_certificate $name for $input) => elaborateRunge name input false
  | _ => throwUnsupportedSyntax
