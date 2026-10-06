"""Bridge existing rational-root packets to emitted Lean completeness theorems."""
import hashlib
import json
from math import isqrt, lcm
from . import polyalg as P
from .elliptic_arithmetic import q, rational_literal, rational_root_certificate, root_budget
from .elliptic_certificate_verifier import CheckBudget, check_rational_roots
from .divisor_square import WorkLimit


def _literal(v):
    return f'({v.numerator}/{v.denominator})' if v.denominator != 1 else f'({v.numerator})'


def _poly(values, monic=False):
    terms=[]
    for i,c in enumerate(values):
        if not c:continue
        power='1' if i==0 else 'X' if i==1 else f'X^{i}'
        if i==0:terms.append(f'C {_literal(c)}')
        elif c==1:terms.append(power)
        else:terms.append(f'C {_literal(c)} * {power}')
    return ' + '.join(terms) or '0'


def rational_certificate(coefficients, *, receipt=None, divisor_work_limit=1024,
                         node_limit=100000):
    """Emit proofs for the original, possibly nonmonic rational polynomial.

    The supplied root packet is replayed. Lean then checks the scaling identity
    and independently reduces the native signed-divisor root generator. Sturm
    analytic variation semantics are not used as a trusted premise.
    """
    root_budget(node_limit)
    if type(divisor_work_limit) is not int or not 1<=divisor_work_limit<=4096:
        raise ValueError('divisor work limit 1 through 4096 required')
    if not isinstance(coefficients,(list,tuple)) or not 1<=len(coefficients)<=13:
        raise ValueError('one through thirteen rational coefficients required')
    f=P.poly(q(c,256) for c in coefficients)
    if P.is_zero(f):raise ValueError('zero polynomial has infinitely many rational roots')
    normalized=P.monic(f);n=P.degree(f);D=lcm(*(c.denominator for c in normalized))
    g=[int(c*D**(n-i)) for i,c in enumerate(normalized)]
    first=next(c for c in g if c)
    if isqrt(abs(first))>divisor_work_limit:
        raise WorkLimit('native signed-divisor reduction exceeds certificate budget')
    packet=rational_root_certificate(f,node_limit) if receipt is None else receipt
    budget=CheckBudget(2000000);budget.packet(packet)
    roots,_=check_rational_roots(packet,f,node_limit,budget)
    canonical=[rational_literal(c) for c in f]
    tag=hashlib.sha256(json.dumps(canonical,separators=(',',':')).encode()).hexdigest()[:16]
    namespace='PerfectPower.RationalPacket_'+tag
    expr=_poly(f);norm=_poly(normalized);ints='['+','.join(map(str,g))+']'
    rootset='({' + ','.join(_literal(r) for r in roots) + '} : Finset ℚ)' if roots else '(∅ : Finset ℚ)'
    source=f'''import PerfectPower.NativeRationalRoots
import PerfectPower.TypedDivisionPackets
namespace {namespace}
open Polynomial PerfectPower
noncomputable def source : Polynomial ℚ := {expr}
private def coefficients : List ℤ := {ints}
private noncomputable def scaled : Polynomial ℤ := NativePolynomialSquare.polynomial coefficients
private theorem source_degree : source.natDegree = {n} := by unfold source; compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_leading : source.leadingCoeff = {_literal(f[-1])} := by
  rw [Polynomial.leadingCoeff, source_degree]
  norm_num [source, Polynomial.coeff_one, Polynomial.coeff_X]
private theorem source_nonzero : source ≠ 0 := by
  intro hz
  have hc := source_leading
  rw [hz] at hc
  norm_num at hc
private theorem scaled_monic : scaled.Monic := by
  simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> monicity! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
private theorem scaling : scaled.map (Int.castRingHom ℚ) =
    (NativeRationalRoots.normalize source).scaleRoots ({D}) := by
  have hn : NativeRationalRoots.normalize source = ({norm} : Polynomial ℚ) := by
    unfold NativeRationalRoots.normalize
    rw [source_leading]
    unfold source
    simp only [mul_add, ← mul_assoc, ← Polynomial.C_mul]
    norm_num <;> ring
  rw [hn]
  have hd : ({norm} : Polynomial ℚ).natDegree = {n} := by compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  have hg : scaled.natDegree = {n} := by
    simp [scaled, coefficients, NativePolynomialSquare.polynomial] <;> compute_degree! <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_scaleRoots, hd]
  by_cases hi : i ≤ {n}
  · interval_cases i <;> norm_num [scaled, coefficients, NativePolynomialSquare.polynomial, Polynomial.coeff_one, Polynomial.coeff_X]
  · have hi' : {n} < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi')]
    simp

theorem native_roots_checked : NativeRationalRoots.roots coefficients ({D}) = {rootset} := by
  decide +kernel

noncomputable def typedPacket : TypedDivisionPackets.RationalPacket
    (NativeRationalRoots.normalize source) where
  coefficients := coefficients
  scale := ({D})
  scale_ne_zero := by norm_num
  valid := by decide +kernel
  monic := scaled_monic
  scaling := scaling

theorem typed_roots_complete (r : ℚ) :
    (NativeRationalRoots.normalize source).eval r=0 ↔ r ∈ typedPacket.interpret :=
  typedPacket.complete r

theorem source_complete (r : ℚ) : source.eval r = 0 ↔ r ∈ {rootset} := by
  rw [← native_roots_checked]
  exact NativeRationalRoots.complete_nonmonic source source_nonzero coefficients ({D})
    (by norm_num) (by decide +kernel) scaled_monic scaling r
end {namespace}
#print axioms {namespace}.native_roots_checked
#print axioms {namespace}.source_complete
#print axioms {namespace}.typed_roots_complete
'''
    return dict(schema='pp-native-rational-certificate/1',original_coefficients=canonical,
        receipt=packet,roots=[rational_literal(r) for r in roots],namespace=namespace,
        lean=source,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        execution_verified=False,scope='compile the emitted Lean to prove original-source root completeness; native divisor budget applies')


def two_torsion_certificate(specification, *, divisor_work_limit=1024, node_limit=100000):
    """Complete two-torsion of the checked completed-square Mathlib curve.

    The original Weierstrass specification is retained, but the original-model
    point transport implementation is not proved by this completed-model theorem.
    """
    from .elliptic_arithmetic import EllipticCurve
    E=EllipticCurve(specification)
    packet=rational_certificate(E.cubic,divisor_work_limit=divisor_work_limit,node_limit=node_limit)
    C,B,A,_=E.cubic;abc=f'({_literal(A)} : ℚ) {_literal(B)} {_literal(C)}';namespace=packet['namespace']
    roots=[q(r) for r in packet['roots']]
    rootset='({' + ','.join(_literal(r) for r in roots) + '} : Finset ℚ)' if roots else '(∅ : Finset ℚ)'
    extra=f'''
namespace {namespace}
open PerfectPower

theorem smooth_checked : (EllipticPointDivision.completed {abc}).Δ ≠ 0 := by
  norm_num [EllipticPointDivision.completed, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem actual_two_torsion_complete (P : (EllipticPointDivision.completed {abc}).Point) :
    (2 : ℤ) • P = 0 ↔ P ∈ EllipticPointDivision.torsionList {abc}
      smooth_checked {rootset}.toList := by
  apply EllipticPointDivision.torsion_list_complete
  intro x
  have h := source_complete x
  have he : source.eval x = EllipticDivision.cubic {abc} x := by
    norm_num [source, EllipticDivision.cubic] <;> ring
  rw [he] at h
  simpa only [Finset.mem_toList] using h
end {namespace}
#print axioms {namespace}.smooth_checked
#print axioms {namespace}.actual_two_torsion_complete
'''
    source=packet['lean'].replace('import PerfectPower.NativeRationalRoots',
        'import PerfectPower.NativeRationalRoots\nimport PerfectPower.EllipticPointDivision')+extra
    return dict(schema='pp-native-two-torsion-certificate/1',curve=E.specification,
        completed_coefficients=[rational_literal(v) for v in (A,B,C)],rational_root_packet=packet,
        two_torsion_cardinality=1+len(roots),lean=source,namespace=namespace,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),execution_verified=False,
        scope='compile Lean to prove smoothness and complete rational two-torsion on the completed-square model; original-model transport remains separate')
