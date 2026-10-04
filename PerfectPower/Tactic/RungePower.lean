import PerfectPower.RungePower
import Mathlib.Data.Finset.Sort

/-! Native d-th-power completion for expanded integer polynomials. Every proposed
identity, bound and complete packet is independently checked by Lean's kernel. -/
open Lean Elab Command Term Meta

namespace PerfectPower.RungePowerAutomation

/-- Exact coefficient convolution; only proposed data, never an assumed identity. -/
def multiply {α : Type} [Semiring α] (a b : List α) : List α :=
  if a.isEmpty || b.isEmpty then [] else
    (List.range (a.length+b.length-1)).map fun k =>
      (List.range a.length).foldl (fun s j =>
        if j ≤ k then s+a.getD j 0*b.getD (k-j) 0 else s) 0

def power {α : Type} [Semiring α] (q : List α) : ℕ → List α
  | 0 => [1]
  | n+1 => multiply (power q n) q

def trim (xs : List Int) : List Int := (xs.reverse.dropWhile (· == 0)).reverse

/-- Reconstruct the rational polynomial root at infinity and clear denominators.
P is the coefficient list of Q^(d-1), used for effective domination. -/
def decompose (xs : List Int) (d : Nat) :
    Except String (Int × List Int × List Int × List Int) := Id.run do
  if d < 2 then return .error "the exponent must be at least two"
  let F := trim xs
  if F.length < 2 then return .error "a nonconstant polynomial is required"
  let degree := F.length-1
  if degree % d != 0 then return .error "the polynomial degree must be divisible by the exponent"
  let lead := F.getLast!
  let root := NativePowerRoots.root d lead.natAbs
  let c : Int := if lead < 0 then -(root:Int) else root
  if c^d != lead then return .error "the leading coefficient is not an integer d-th power"
  let n := degree/d
  let mut Q : Array Rat := Array.replicate (n+1) 0
  Q := Q.set! n (c : Rat)
  for i in List.range n do
    let k := n-1-i
    let target := (d-1)*n+k
    let known := (power Q.toList d).getD target 0
    Q := Q.set! k ((((F[target]! : Int) : Rat)-known)/((d:Rat)*(c:Rat)^(d-1)))
  let a := Q.toList.foldl (fun l q => Nat.lcm l q.den) 1
  let qi := Q.toList.map fun q => (a:Int)*q.num/(q.den:Int)
  let Qd := power qi d
  let R := (List.range (degree+1)).map fun k => (a:Int)^d*F[k]!-Qd.getD k 0
  return .ok ((a:Int),qi,power qi (d-1),trim R)

syntax (name := nativeRungePower) "native_runge_power " ident " for " term "," term : command
syntax (name := nativeRungePowerCertificate) "native_runge_power_certificate " ident " for " term "," term : command

unsafe def elaborate (name : Ident) (input exponent : TSyntax `term) (enumerate : Bool) : CommandElabM Unit := do
  let F ← liftTermElabM do
    let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``Int)
    let e ← Term.elabTermEnsuringType input ty
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.evalExpr (List Int) ty (← instantiateMVars e)
  let d ← liftTermElabM do
    let e ← Term.elabTermEnsuringType exponent (mkConst ``Nat)
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.evalExpr Nat (mkConst ``Nat) (← instantiateMVars e)
  let (a,q,P,r) ← match decompose F d with
    | .ok data => pure data
    | .error message => throwError "{message}"
  let bound := RungePolynomial.bound P r
  if enumerate && !r.isEmpty && 2*bound+1 > 10001 then
    throwError "the complete interval exceeds 10001 coordinates; use native_runge_power_certificate"
  let sa := quote a
  let sq := quote q
  let sP := quote P
  let sr := quote r
  let sd := quote d
  let sb := quote bound
  let identityName := mkIdent (name.getId.appendAfter "_decomposition")
  let powerName := mkIdent (name.getId.appendAfter "_dominating_power")
  let boundName := mkIdent (name.getId.appendAfter "_bound")
  let theoremName := mkIdent (name.getId.appendAfter "_complete")
  elabCommand (← `(theorem $identityName (x : ℤ) :
    ($sa : ℤ)^($exponent : ℕ)*PerfectPower.NativePolynomialSquare.eval $input x =
      (PerfectPower.NativePolynomialSquare.eval $sq x)^($exponent : ℕ)+
        PerfectPower.NativePolynomialSquare.eval $sr x := by
    norm_num [PerfectPower.NativePolynomialSquare.eval] <;> ring))
  if r.isEmpty then
    elabCommand (← `(theorem $theoremName (x y : ℤ) :
      y^($exponent : ℕ)=PerfectPower.NativePolynomialSquare.eval $input x ↔
        ($sa : ℤ)*y=PerfectPower.NativePolynomialSquare.eval $sq x ∨
        ($sa : ℤ)*y= -PerfectPower.NativePolynomialSquare.eval $sq x ∧ Even ($exponent : ℕ) := by
      exact PerfectPower.RungePower.power_family $input $sq $sa $exponent (by decide +kernel)
        (by norm_num) (by intro x; simpa [PerfectPower.NativePolynomialSquare.eval] using $identityName x) x y))
    return
  elabCommand (← `(theorem $powerName (x : ℤ) :
    PerfectPower.NativePolynomialSquare.eval $sP x=
      (PerfectPower.NativePolynomialSquare.eval $sq x)^(($exponent : ℕ)-1) := by
    norm_num [PerfectPower.NativePolynomialSquare.eval] <;> ring))
  elabCommand (← `(theorem $boundName (x y : ℤ)
    (h : y^($exponent : ℕ)=PerfectPower.NativePolynomialSquare.eval $input x) :
    |x| ≤ ($sb : ℤ) := by
    exact PerfectPower.RungePower.coordinate_bound $input $sq $sP $sr $sa $exponent
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      $powerName $identityName x y h))
  if !enumerate then
    elabCommand (← `(theorem $theoremName (x y : ℤ) :
      y^($exponent : ℕ)=PerfectPower.NativePolynomialSquare.eval $input x ↔
        (x,y) ∈ PerfectPower.RungePower.points $input $sP $sr $exponent := by
      exact PerfectPower.RungePower.complete $input $sq $sP $sr $sa $exponent
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        $powerName $identityName x y))
    return
  let xs := (List.range (2*bound+1).toNat).map fun i => (i:Int)-bound
  let exceptional := (NativePolynomialRoots.roots r).sort (· ≤ ·)
  let values : List (Int × Int) := (xs++exceptional).eraseDups.flatMap fun x =>
    (NativePowerRoots.roots d (NativePolynomialSquare.eval F x)).sort (· ≤ ·) |>.map fun y => (x,y)
  let data := quote values
  elabCommand (← `(def $name : Finset (ℤ × ℤ) := ($data : List (ℤ × ℤ)).toFinset))
  elabCommand (← `(set_option maxRecDepth 100000 in theorem $theoremName (x y : ℤ) :
    y^($exponent : ℕ)=PerfectPower.NativePolynomialSquare.eval $input x ↔ (x,y) ∈ $name := by
    have hp : PerfectPower.RungePower.points $input $sP $sr $sd=$name := by decide +kernel
    rw [← hp]
    exact PerfectPower.RungePower.complete $input $sq $sP $sr $sa $exponent
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      $powerName $identityName x y))

@[command_elab nativeRungePower]
unsafe def elabNativeRungePower : CommandElab
  | `(native_runge_power $name for $input, $exponent) => elaborate name input exponent true
  | _ => throwUnsupportedSyntax

@[command_elab nativeRungePowerCertificate]
unsafe def elabNativeRungePowerCertificate : CommandElab
  | `(native_runge_power_certificate $name for $input, $exponent) => elaborate name input exponent false
  | _ => throwUnsupportedSyntax

end PerfectPower.RungePowerAutomation
