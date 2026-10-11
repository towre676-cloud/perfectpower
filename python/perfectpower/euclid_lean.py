"""Source-bound polynomial Bezout and rational square-root bound proof emitters."""
from fractions import Fraction as Q
from hashlib import sha256
import json
from .euclid_descent import check_resultant
from .euclid_exact import check_exhaustion


def _identity(spec):return sha256(json.dumps(spec,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def _list(cs):return '['+','.join(str(x) for x in cs)+']'


def compile_resultant(certificate):
    check_resultant(certificate,certificate['left'],certificate['right']);c=certificate
    digest=_identity(c);length=len(c['left'])+len(c['right'])-2
    target=[c['resultant']]+[0]*(length-1)
    source=f'''import PerfectPower.EuclidMethods
namespace PerfectPower.CheckedEuclid.P{digest}
open PerfectPower.EuclidMethods
def A : List Int := {_list(c['left'])}
def B : List Int := {_list(c['right'])}
def U : List Int := {_list(c['u'])}
def V : List Int := {_list(c['v'])}
theorem coefficient_identity : addPoly (mulPoly U A) (mulPoly V B) = {_list(target)} := by decide
theorem identity_all_inputs (n : Int) : horner U n*horner A n+horner V n*horner B n=({c['resultant']}) := by
  have h := congrArg (fun p => horner p n) coefficient_identity
  dsimp only at h
  rw [horner_add, horner_mul, horner_mul] at h
  simpa [horner] using h
theorem common_divisor_bound (n d : Int) (hA : d ∣ horner A n) (hB : d ∣ horner B n) : d ∣ ({c['resultant']}) :=
  common_divisor_bezout (horner A n) (horner B n) (horner U n) (horner V n) ({c['resultant']}) d hA hB (identity_all_inputs n)
#print axioms identity_all_inputs
#print axioms common_divisor_bound
end PerfectPower.CheckedEuclid.P{digest}
'''
    return {'schema':'pp-source-bound-bezout/1','certificate':c,'source':source,
            'source_sha256':sha256(source.encode()).hexdigest(),'specification_sha256':digest,
            'scope':'every integer input and every common integer divisor of the two original polynomial values'}


def compile_sqrt_bounds(packet):
    check_exhaustion(packet);value=Q(packet['radicand']);lo=Q(packet['lower']);hi=Q(packet['upper']);eps=Q(packet['epsilon']);width=hi-lo
    digest=_identity(packet)
    source=f'''import Std
namespace PerfectPower.CheckedEuclid.Bounds{digest}
theorem lower_square : ({lo.numerator} : Int)^2*{value.denominator} ≤ ({value.numerator})*{lo.denominator}^2 := by decide
theorem upper_square : ({value.numerator} : Int)*{hi.denominator}^2 ≤ ({hi.numerator})^2*{value.denominator} := by decide
theorem nonnegative_endpoints : (0 : Int) ≤ {lo.numerator} ∧ (0 : Int) ≤ {hi.numerator} := by decide
theorem tolerance : ({width.numerator} : Int)*{eps.denominator} ≤ ({eps.numerator})*{width.denominator} := by decide
#print axioms lower_square
#print axioms upper_square
#print axioms tolerance
end PerfectPower.CheckedEuclid.Bounds{digest}
'''
    return {'schema':'pp-source-bound-sqrt-bounds/1','packet':packet,'source':source,
            'source_sha256':sha256(source.encode()).hexdigest(),'specification_sha256':digest,
            'scope':'exact endpoint square and width inequalities for supplied rational radicand and tolerance'}
