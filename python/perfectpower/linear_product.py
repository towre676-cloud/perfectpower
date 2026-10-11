"""Complete all-integer charts for y²=(a*n+b)(c*n+d), ac a positive square.

Distinct linear roots are required. Work exhaustion raises and never produces a
partial list. Python execution is tested; compile_lean supplies a separate
kernel-checked equality to the proved finite chart.
"""
from math import isqrt
from .euclid_descent import resultant_certificate, _factor
from .divisor_square import Budget, WorkLimit


def _parameters(left, right):
    left, right = list(left), list(right)
    if any(len(p) != 2 or any(type(v) is not int for v in p) or p[1] == 0
           for p in (left, right)):
        raise ValueError('two nonconstant integral linear factors required')
    b, a = left; d, c = right
    q = a*c
    if q <= 0 or isqrt(q)**2 != q:
        raise ValueError('positive square leading product required; nonsquare Pell branches remain unsupported here')
    if a*d-b*c == 0:
        raise ValueError('distinct linear roots required; proportional factors can give infinite families')
    return left, right, q, a*d+b*c, isqrt(q)


def solve(left, right, *, work_limit=1000000):
    left, right, q, t, s = _parameters(left, right)
    cert = resultant_certificate(left, right)
    delta = cert['resultant']; k = delta*delta
    budget = Budget(work_limit)
    factors = _factor(abs(delta), budget)
    divisors = [1]
    for p, e in sorted(factors.items()):
        expanded = []
        for u in divisors:
            power = 1
            for _ in range(2*e+1):
                budget.spend(); expanded.append(u*power); power *= p
        divisors = expanded
    signed = sorted([-u for u in divisors]+divisors)
    points = set(); accepted = []
    for u in signed:
        budget.spend(); v = k//u
        nx, ny = u+v-2*t, v-u
        if nx % (4*q) or ny % (4*s):
            continue
        n, y = nx//(4*q), ny//(4*s)
        if y*y != (left[1]*n+left[0])*(right[1]*n+right[0]):
            raise AssertionError('integral chart reconstruction failed')
        points.add((n,y)); accepted.append({'pair':[u,v],'point':[n,y]})
    return {'schema':'pp-linear-product-chart/1', 'left':left,'right':right,
            'bezout':cert,'transform':{'q':q,'t':t,'s':s,'constant':k},
            'resultant_factorization':[[p,e] for p,e in sorted(factors.items())],
            'signed_divisors':signed,'accepted_pairs':accepted,
            'points':[list(p) for p in sorted(points)],'cardinality':len(points),
            'work_used':budget.used,'status':'COMPLETE','complete':True,
            'kernel_checked':False,
            'scope':'all integer n and signed integer y; square degree 2, positive square leading product, distinct roots'}


def check(packet, *, work_limit=1000000):
    expected = solve(packet['left'],packet['right'],work_limit=work_limit)
    if expected != packet:
        raise ValueError('source-bound linear-product chart does not replay')
    return True


def close_descent(descent, *, work_limit=1000000):
    """Close every branch of a supported existing resultant descent packet.

    The full original-equation chart has a Lean compiler. Assignment of its
    points to the older exceptional-prime branches remains replayed Python.
    """
    from .euclid_descent import check_descent, classify_input
    check_descent(descent,work_limit=work_limit)
    if descent['degree'] != 2: raise ValueError('this complete chart closes square degree 2 only')
    cert=descent['bezout']
    chart=solve(cert['left'],cert['right'],work_limit=work_limit)
    branches=[{'branch':i,'coefficients':[b['left_coefficient'],b['right_coefficient']],
               'points':[]} for i,b in enumerate(descent['branches'])]
    zeros=[]
    for point in chart['points']:
        classification=classify_input(descent,point[0])
        if classification['status']=='ZERO': zeros.append(point)
        elif classification['status']=='BRANCH':branches[classification['branch']]['points'].append(point)
        else:raise AssertionError('complete chart point missing from descent cover')
    return {'schema':'pp-closed-linear-descent/1','descent':descent,'chart':chart,
            'branches':branches,'zero_points':zeros,'status':'COMPLETE','branches_solved':True,
            'kernel_checked':False,'scope':'complete original-equation point set; branch assignment is tested Python'}


class LinearProductPopulation:
    """Lexicographic rank/select on a complete chart, with exact restrictions."""
    def __init__(self, packet, *, n_min=None,n_max=None,y_min=None,y_max=None,
                 n_modulus=None,n_residue=0,work_limit=1000000):
        check(packet,work_limit=work_limit)
        for v in (n_min,n_max,y_min,y_max):
            if v is not None and type(v) is not int: raise ValueError('integer bounds required')
        if type(n_residue) is not int: raise ValueError('integer residue required')
        if n_modulus is not None and (type(n_modulus) is not int or n_modulus <= 0):
            raise ValueError('positive integer modulus required')
        if (n_min is not None and n_max is not None and n_min>n_max) or (y_min is not None and y_max is not None and y_min>y_max):
            raise ValueError('ordered coordinate bounds required')
        self.points = [tuple(p) for p in packet['points']
                       if (n_min is None or p[0]>=n_min) and (n_max is None or p[0]<=n_max)
                       and (y_min is None or p[1]>=y_min) and (y_max is None or p[1]<=y_max)
                       and (n_modulus is None or p[0]%n_modulus==n_residue%n_modulus)]
    def count(self): return len(self.points)
    def select(self, rank):
        if type(rank) is not int or not 0<=rank<self.count(): raise IndexError('rank outside population')
        return self.points[rank]
    def rank(self, point):
        if len(point)!=2 or any(type(v) is not int for v in point): raise ValueError('integer coordinate pair required')
        p=tuple(point)
        return self.points.index(p) if p in self.points else None
    def optimize(self, objective='abs_y', maximize=False):
        if objective not in ('n','y','abs_y'): raise ValueError('objective must be n, y or abs_y')
        if type(maximize) is not bool: raise ValueError('boolean maximize required')
        if not self.points: return None
        value=lambda p: p[0] if objective=='n' else p[1] if objective=='y' else abs(p[1])
        optimum=(max if maximize else min)(map(value,self.points))
        return {'value':optimum,'points':[list(p) for p in self.points if value(p)==optimum]}


def query(packet, spec):
    restrictions=spec.get('restrictions',{})
    pop=LinearProductPopulation(packet,**restrictions)
    result={'count':pop.count(),'points':[list(p) for p in pop.points]}
    if 'select' in spec: result['selected']=list(pop.select(spec['select']))
    if 'rank' in spec: result['rank']=pop.rank(spec['rank'])
    if 'objective' in spec: result['optimum']=pop.optimize(spec['objective'],spec.get('maximize',False))
    return result


def compile_lean(packet, *, divisor_scan_limit=100000):
    """Check the faster list against the proved Std chart for every integer input.

    Kernel enumeration is intentionally capped separately from Python factoring;
    large complete Python charts may need a future faster Lean divisor algorithm.
    """
    from hashlib import sha256
    import json
    from . import polyalg as P
    check(packet)
    if type(divisor_scan_limit) is not int or divisor_scan_limit<1:
        raise ValueError('positive proof enumeration budget required')
    k=packet['transform']['constant']
    if 2*k+1>divisor_scan_limit:
        raise WorkLimit('Lean divisor enumeration budget exceeded; Python chart remains separately complete')
    left,right=packet['left'],packet['right']
    q,t,s=(packet['transform'][key] for key in ('q','t','s'))
    F=[int(c) for c in P.mul(P.poly(left),P.poly(right))]
    X=[t,2*q]
    # A coefficient identity binds the transform to the original polynomial.
    lhs=[int(c) for c in P.add(P.mul(P.poly(X),P.poly(X)),P.scale(P.poly(F),-(2*s)**2))]
    assert P.poly(lhs)==P.poly([k])
    digest=sha256(json.dumps(packet,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    ints=lambda cs:'['+','.join(str(c) for c in cs)+']'
    pts='['+','.join(f'({n},{y})' for n,y in packet['points'])+']'
    chart_pts='['+','.join(f"({p['point'][0]},{p['point'][1]})" for p in packet['accepted_pairs'])+']'
    source=f'''import PerfectPower.LinearProductChart
namespace PerfectPower.CheckedLinearProduct.P{digest}
open PerfectPower.EuclidMethods PerfectPower.LinearProductChart
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def F : List Int := {ints(F)}
def X : List Int := {ints(X)}
theorem coefficient_identity : addPoly (mulPoly X X) (scalePoly (-((2*({s} : Int))*(2*({s})))) F) = {ints([k,0,0])} := by decide
theorem transform (n : Int) :
    (2*({q})*n+({t}))*(2*({q})*n+({t}))-(2*({s}))*(2*({s}))*horner F n=({k}) := by
  have h := congrArg (fun p => horner p n) coefficient_identity
  dsimp only at h
  rw [horner_add,horner_mul,horner_scale] at h
  simpa [X,horner,Int.mul_comm,Int.add_comm,Int.mul_neg,Int.neg_mul,Int.sub_eq_add_neg] using h
def solutions : List (Int × Int) := {pts}
def chart_points : List (Int × Int) := {chart_pts}
theorem computed_chart : points (horner F) ({q}) ({t}) ({s}) ({k}) = chart_points := by decide
theorem lists_agree : chart_points ⊆ solutions ∧ solutions ⊆ chart_points := by decide
theorem all_integer_solutions (n y : Int) :
    y*y=({left[1]}*n+({left[0]}))*({right[1]}*n+({right[0]})) ↔ (n,y) ∈ solutions := by
  have h := complete (horner F) ({q}) ({t}) ({s}) ({k}) (by decide) (by decide) (by decide) transform n y
  rw [computed_chart] at h
  have he : horner F n=({left[1]}*n+({left[0]}))*({right[1]}*n+({right[0]})) := by
    have hh := horner_mul ({ints(left)} : List Int) {ints(right)} n
    simpa [mulPoly,addPoly,scalePoly,horner,F,Int.mul_comm,Int.add_comm] using hh
  rw [he] at h
  exact h.trans ⟨fun hp => lists_agree.1 hp, fun hp => lists_agree.2 hp⟩
#print axioms transform
#print axioms all_integer_solutions
end PerfectPower.CheckedLinearProduct.P{digest}
'''
    return {'schema':'pp-checked-linear-product/1','source':source,
            'source_sha256':sha256(source.encode()).hexdigest(),'specification_sha256':digest,
            'scope':'all signed integer input/output pairs for the two supplied linear factors',
            'kernel_checked':False}
