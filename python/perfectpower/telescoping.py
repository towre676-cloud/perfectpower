"""Boundary-complete creative telescoping for binomial power sums.

Original bounded polynomial search over Q(n); no symbolic dependencies.
No negative result from a bounded search implies nonexistence.
"""
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
from .rational_functions import RationalFunction as RF, AlgebraBudget, solve_many
from . import field_polynomials as F
from . import polyalg as P
from .core import mul, integer_power_root
from .divisor_square import WorkLimit
from .holonomic_series import ThetaSeries


def _integer(value, lo, hi, name):
    if type(value) is not int or not lo <= value <= hi:
        raise ValueError(name+' outside supported integer range')
    return value


def _setup(power, order):
    budget = AlgebraBudget(work_limit=20000000)
    one = RF([1], budget=budget); n = RF([0, 1], budget=budget)
    N = n+order
    ratios = []
    for j in range(order+1):
        a = [one]; d = one
        for h in range(order-j):
            a = F.product(a, [N-h, -one]); d *= N-h
        ratios.append(F.power(a, power))
        # RF deliberately has no general exponent operator.
        divisor = one
        for _ in range(power): divisor *= d
        ratios[-1] = F.scale(ratios[-1], one/divisor)
    return budget, one, N, ratios


def _columns(power, N, degree, one):
    left = F.power([N, -one], power)
    right = [one.coerce(0)]*power+[one]
    return [F.add(F.product(left, F.shift([one.coerce(0)]*i+[one], one)),
                  F.scale(F.product(right, [one.coerce(0)]*i+[one]), -1))
            for i in range(degree+1)]


def discover_binomial_sum(power, max_order=3, degree=None):
    """Compile S(n)=sum_{k=0}^n binomial(n,k)^power, power=1..4.

    Search normalizes the last recurrence coefficient to one over Q(n).
    G(n,k)=k^power*b(n,k)*binomial(n+order,k)^power.
    """
    _integer(power, 1, 4, 'power'); _integer(max_order, 1, 3, 'max_order')
    if degree is not None: _integer(degree, 0, 12, 'degree')
    attempts = []
    for order in range(1, max_order+1):
        d = degree if degree is not None else power*order
        budget, one, N, ratios = _setup(power, order)
        cols = [F.scale(v, -1) for v in ratios[:-1]]+_columns(power, N, d, one)
        length = max(map(len, cols+[ratios[-1]])); zero = one.coerce(0)
        padded = [v+[zero]*(length-len(v)) for v in cols]
        rhs = ratios[-1]+[zero]*(length-len(ratios[-1]))
        sol = solve_many([list(row) for row in zip(*padded)], [[v] for v in rhs])
        attempts.append({'order': order, 'degree': d, 'solved': sol is not None})
        if sol is None: continue
        coeff = [v[0] for v in sol[:order]]+[one]
        b = [v[0] for v in sol[order:]]
        packet = {'schema': 'pp-binomial-telescoping/1', 'power': power, 'order': order,
                  'coefficients': [v.packet() for v in coeff],
                  'certificate_polynomial': [v.packet() for v in F.trim(b)],
                  'initial': [str(sum(comb(n,k)**power for k in range(n+1))) for n in range(order)],
                  'attempts': attempts}
        replay_binomial_sum(packet)
        return packet
    return {'schema': 'pp-telescoping-search/1', 'status': 'ANSATZ_UNRESOLVED',
            'power': power, 'attempts': attempts, 'nonexistence_proved': False}


def _checked(packet):
    if not isinstance(packet, dict) or packet.get('schema') != 'pp-binomial-telescoping/1':
        raise ValueError('binomial telescoping packet required')
    p = _integer(packet['power'], 1, 4, 'power')
    r = _integer(packet['order'], 1, 3, 'order')
    if not isinstance(packet['coefficients'], list) or len(packet['coefficients']) != r+1:
        raise ValueError('recurrence length mismatch')
    if not isinstance(packet['certificate_polynomial'], list) or not 1 <= len(packet['certificate_polynomial']) <= 13:
        raise ValueError('bounded certificate polynomial required')
    budget, one, N, ratios = _setup(p, r)
    a = [RF.parse(v, budget) for v in packet['coefficients']]
    b = [RF.parse(v, budget) for v in packet['certificate_polynomial']]
    if a[-1] != 1: raise ValueError('normalized leading coefficient required')
    # Endpoint proof needs coefficients defined for every integer n>=0.
    # Our accepted domain is stricter: all denominator coefficients positive.
    for v in a+b:
        if v.d[0] <= 0 or any(c < 0 for c in v.d):
            raise ValueError('denominator not certified positive on n>=0')
    residual = [one.coerce(0)]
    for c, ratio in zip(a, ratios): residual = F.add(residual, F.scale(ratio, c))
    boundary_diff = F.add(F.product(F.power([N, -one], p), F.shift(b, one)),
                          F.scale([one.coerce(0)]*p+b, -1))
    if any(F.add(residual, F.scale(boundary_diff, -1))):
        raise ValueError('telescoping identity failed')
    initial = [str(sum(comb(n,k)**p for k in range(n+1))) for n in range(r)]
    if packet.get('initial') != initial: raise ValueError('initial sums failed')
    return p, r, a, b


def replay_binomial_sum(packet):
    _checked(packet)
    return {'valid': True, 'boundary_conditions_proved': True,
            'domain': 'every integer n>=0', 'sequence': 'sum(k=0..n, binomial(n,k)^power)',
            'boundary_reason': 'G(0)=0 from k^power; G(n+order+1)=0 from finite binomial support; polynomial certificate has no k poles',
            'proof_backend': 'exact Python rational-function replay', 'lean_verified': False}


def theta_from_telescoping(packet):
    """Forward recurrence to OGF theta operator, retaining finite forcing."""
    p, r, coeff, _ = _checked(packet)
    denominator = P.ONE
    for c in coeff: denominator = mul(denominator, P.exact_div(c.d, P.gcd_poly(denominator,c.d)))
    polynomials = [mul(c.n, P.exact_div(denominator,c.d)) for c in coeff]
    rows = [P.ZERO]*(r+1)
    for j, a in enumerate(polynomials):
        # q(theta) at z^(r-j) acts on coefficient a_m with q(m)=A_j(m-j).
        shifted = F.shift([RF([x]) for x in a], RF([-j]))
        rows[r-j] = tuple(v.evaluate(0) for v in shifted)
    initial = list(map(Q, packet['initial']))
    forcing = []
    for n in range(r):
        forcing.append(sum(P.evaluate(rows[h],n-h)*initial[n-h] for h in range(n+1)))
    spec = {'theta': [list(map(str,row)) for row in rows],
            'initial': packet['initial'], 'forcing': list(map(str,forcing))}
    return ThetaSeries(spec)


class BinomialSumSequence:
    def __init__(self, packet):
        self.packet = deepcopy(packet)
        self.series = theta_from_telescoping(self.packet)

    def coefficient(self, index): return self.series.coefficient(index)
    def terms(self, start=0, size=12): return self.series.terms(start,size)

    def power_hits(self, start=0, size=100, exponent=2):
        _integer(exponent, 2, 64, 'exponent')
        values = self.terms(start,size); hits = []
        for n, value in enumerate(values,start):
            if value.denominator != 1: raise AssertionError('integer sum became nonintegral')
            root = integer_power_root(value.numerator,exponent)
            if root is not None: hits.append({'index': n, 'value': str(value), 'root': str(root)})
        return {'schema': 'pp-binomial-power-window/1', 'start': start, 'size': size,
                'exponent': exponent, 'hits': hits, 'complete_in_window': True,
                'unbounded_classification_proved': False}


def _shift(v):
    return RF([c.evaluate(0) for c in F.shift([RF([x]) for x in v.n], RF([1]))],
              [c.evaluate(0) for c in F.shift([RF([x]) for x in v.d], RF([1]))], budget=v.budget)


def discover_antidifference(ratio, denominator=(1,), degree=4):
    """Bounded Gosper-style rational search r(k)R(k+1)-R(k)=1.

    Caller supplies a denominator ansatz; failure is not Gosper's complete
    nonsummability decision. Returned identities need domain checks to sum.
    """
    _integer(degree,0,16,'degree')
    budget = AlgebraBudget()
    r = RF.parse(ratio,budget); D = RF(denominator,budget=budget)
    if not D or P.degree(D.n)>32: raise ValueError('bounded nonzero polynomial denominator required')
    cols = []
    for j in range(degree+1):
        R = RF([0]*j+[1],D.n,budget=budget)
        cols.append(r*_shift(R)-R)
    common = P.ONE
    for v in cols: common=mul(common,P.exact_div(v.d,P.gcd_poly(common,v.d))); budget.check(common)
    polynomials = [mul(v.n,P.exact_div(common,v.d)) for v in cols]
    length=max(len(common),max(map(len,polynomials))); zero=RF([0],budget=budget)
    matrix=[[RF([v[i] if i<len(v) else 0],budget=budget) for v in polynomials] for i in range(length)]
    rhs=[[RF([common[i] if i<len(common) else 0],budget=budget)] for i in range(length)]
    sol=solve_many(matrix,rhs)
    if sol is None: return {'status':'ANSATZ_UNRESOLVED','nonexistence_proved':False}
    R=RF([v[0].evaluate(0) for v in sol],D.n,budget=budget)
    packet={'schema':'pp-antidifference/1','ratio':r.packet(),'certificate':R.packet()}
    replay_antidifference(packet)
    return packet


def replay_antidifference(packet):
    if not isinstance(packet,dict) or packet.get('schema')!='pp-antidifference/1':
        raise ValueError('antidifference packet required')
    budget=AlgebraBudget(); r=RF.parse(packet['ratio'],budget); R=RF.parse(packet['certificate'],budget)
    if r*_shift(R)-R != 1: raise ValueError('antidifference identity failed')
    return {'valid':True,'boundary_conditions_proved':False,'scope':'r(k)R(k+1)-R(k)=1 away from poles'}


def sum_from_antidifference(packet,start,stop,initial_term):
    """Sum t(start)..t(stop-1); initial_term=t(start) is a premise.

    Checks every ratio and certificate denominator in the bounded interval,
    including the final endpoint; refuses singular cancellation shortcuts.
    """
    replay_antidifference(packet)
    _integer(start,0,4096,'start'); _integer(stop,start,4096,'stop')
    budget=AlgebraBudget(); r=RF.parse(packet['ratio'],budget); R=RF.parse(packet['certificate'],budget)
    term=RF.parse(initial_term,budget).evaluate(0)
    if isinstance(initial_term,(dict,list,tuple)): raise ValueError('scalar initial term required')
    left=R.evaluate(start)*term
    for k in range(start,stop):
        R.evaluate(k); term*=r.evaluate(k)
        budget.check((term,))
    result=R.evaluate(stop)*term-left
    budget.check((result,))
    return {'schema':'pp-finite-antidifference/1','start':start,'stop':stop,
            'initial_term':str(initial_term),'sum':str(result),
            'domain_checked':True,'initial_term_is_premise':True}


def certify_hypergeometric_solution(packet, ratio):
    """Prove a supplied first-order solution equals the compiled finite sum.

    This checks a proposed closed form; it is not the complete Hyper algorithm.
    The initial value is fixed by the sum definition, not chosen by the caller.
    """
    p, order, coeff, _ = _checked(packet)
    budget=AlgebraBudget(); r=RF.parse(ratio,budget)
    if r.d[0]<=0 or any(c<0 for c in r.d):
        raise ValueError('ratio denominator not certified positive on n>=0')
    factor=RF([1],budget=budget); total=RF([0],budget=budget); shifted=r
    for j,a in enumerate(coeff):
        total += a*factor
        factor *= shifted; shifted=_shift(shifted)
    if total: raise ValueError('proposed hypergeometric solution does not satisfy recurrence')
    value=Q(packet['initial'][0])
    for n in range(order):
        if value!=Q(packet['initial'][n]): raise ValueError('proposed solution misses initial sums')
        value*=r.evaluate(n)
    return {'schema':'pp-binomial-hypergeometric/1','source':deepcopy(packet),
            'ratio':r.packet(),'initial':packet['initial'][0],
            'valid':True,'domain':'every integer n>=0',
            'uniqueness_reason':'normalized forward recurrence and matching initial sums',
            'lean_verified':False}


def replay_hypergeometric_solution(packet):
    if not isinstance(packet,dict) or packet.get('schema')!='pp-binomial-hypergeometric/1':
        raise ValueError('hypergeometric solution packet required')
    expected=certify_hypergeometric_solution(packet['source'],packet['ratio'])
    if packet!=expected: raise ValueError('hypergeometric solution metadata differs from replay')
    return {'valid':True,'domain':'every integer n>=0','lean_verified':False}


def export_lean_binomial(packet, namespace="PerfectPower.Generated.BinomialCertificate"):
    """Emit a source-bound all-index Lean theorem for the four compiled families.

    Lean checks the serialized rational recurrence against the actual binomial
    sum theorem. No Python acceptance Boolean enters the proof.
    """
    import hashlib, json, re
    p, order, coeff, _ = _checked(packet)
    if not isinstance(namespace,str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*",namespace):
        raise ValueError("Lean namespace must contain plain identifiers")
    canonical=discover_binomial_sum(p,max_order=2)
    if packet['order']!=canonical['order'] or packet['coefficients']!=canonical['coefficients']:
        raise ValueError("Lean emitter supports the retained canonical recurrence only")
    def rational(x):
        return str(x.numerator) if x.denominator==1 else "("+str(x.numerator)+"/"+str(x.denominator)+")"
    def poly(values):
        return "("+" + ".join("("+rational(x)+")*(n:ℚ)^"+str(i) for i,x in enumerate(values) if x)+")" if any(values) else "0"
    expressions=["("+poly(v.n)+"/"+poly(v.d)+")" for v in coeff]
    terms=[expression+"*S "+str(p)+" (n+"+str(j)+")" for j,expression in enumerate(expressions)]
    digest=hashlib.sha256(json.dumps(packet,sort_keys=True,separators=(",",":")).encode()).hexdigest()
    text="import PerfectPower.CertifiedTelescoping\n\nnamespace "+namespace+"\nopen PerfectPower.CertifiedTelescoping\n"
    text+="-- Source packet SHA-256: "+digest+"\n"
    text+="theorem compiled_recurrence (n : ℕ) :\n  "+" + ".join(terms)+" = 0 := by\n"
    if p==1:
        text+="  rw [first_power,first_power]\n  norm_num\n  ring\n"
    else:
        text+="  have h := recurrence"+str(p)+" n\n"
        for i,v in enumerate(coeff):
            text+="  have hd"+str(i)+" : "+poly(v.d)+" ≠ 0 := by positivity\n"
        text+="  field_simp\n  nlinarith [h]\n"
    text+="\n#print axioms compiled_recurrence\nend "+namespace+"\n"
    return text


def main():
    import argparse,json
    from pathlib import Path
    from .catalogue import encoded
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=('compile','replay','emit-lean'))
    parser.add_argument('path',type=Path)
    parser.add_argument('--out',type=Path)
    args=parser.parse_args(); data=json.loads(args.path.read_text())
    if args.command=='compile':
        from .generating_cli import execute
        result=execute(data)
    elif args.command=='emit-lean':
        text=export_lean_binomial(data.get('definition',data))
        if args.out: args.out.write_text(text)
        else: print(text,end='')
        return
    else:
        data=data.get('definition',data)
        schema=data.get('schema')
        checker={'pp-binomial-telescoping/1':replay_binomial_sum,
                 'pp-antidifference/1':replay_antidifference,
                 'pp-binomial-hypergeometric/1':replay_hypergeometric_solution}.get(schema)
        if checker is None: raise ValueError('unsupported replay schema')
        result=checker(data)
    text=encoded(result)+'\n'
    if args.out: args.out.write_text(text)
    else: print(text,end='')

if __name__=='__main__':main()
