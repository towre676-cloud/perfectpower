"""Exact arithmetic evidence alongside external global completeness results."""
import hashlib,re
from functools import reduce
from itertools import combinations
from math import gcd,isqrt
from .elliptic_arithmetic import EllipticCurve,encode_point,primes,q
from .elliptic_certificate_verifier import verify_independence
from .elliptic_reduction_saturation import replay_reduction_saturation


def torsion_bound(k):
    rows=[];bound=0
    for p in primes(97):
        if (6*k)%p==0:continue
        squares={y*y%p for y in range(1,p)}
        count=1
        for x in range(p):
            rhs=(x**3+k)%p
            count+=1 if rhs==0 else 2 if rhs in squares else 0
        rows.append(dict(prime=p,group_order=count));bound=gcd(bound,count)
        if bound==1:break
    if bound!=1:raise ArithmeticError('trivial torsion not established by good reductions')
    return dict(good_reductions=rows,torsion_order_bound=bound)


def subgroup_index(rows,rank):
    if rank not in (1,2) or any(len(r)!=rank or any(type(c) is not int for c in r) for r in rows):
        raise ValueError('bounded rank-one or rank-two integer relation matrix required')
    minors=([abs(r[0]) for r in rows] if rank==1 else
            [abs(a[0]*b[1]-a[1]*b[0]) for a,b in combinations(rows,2)])
    return reduce(gcd,minors,0)


def check_completion_arithmetic(packet,source):
    E=EllipticCurve([0,packet['k']]);basis=[E.checked(p) for p in packet['basis_points']]
    rank=source['rank_upper_bound']
    if (packet['curve']!=E.specification or packet['source_points']!=source['points']
            or packet['rank_upper_bound']!=rank or len(basis)!=rank):
        raise ArithmeticError('completion source and curve disagree')
    relations=packet['original_to_basis']
    if len(relations)!=len(source['points']):raise ArithmeticError('every source point needs a relation')
    for p,cs in zip(source['points'],relations):
        if len(cs)!=rank or any(type(c) is not int or abs(c)>10**6 for c in cs):raise ValueError('bounded exact relation required')
        total=None
        for c,b in zip(cs,basis):total=E.add(total,E.mul(b,c))
        if encode_point(total)!=p:raise ArithmeticError('source-to-basis relation mismatch')
    index=subgroup_index(relations,rank)
    if index!=packet['source_subgroup_index'] or index<1:raise ArithmeticError('subgroup index mismatch')
    independence=E.independence(packet['basis_points'],prime_bound=500,halving_limit=0)
    if independence['rank_lower_bound']!=rank or not verify_independence(independence):
        raise ArithmeticError('saturated point independence not established')
    points=packet['integral_points'];xs=[]
    for point in points:
        x,y=E.checked(point)
        if x.denominator!=1 or y.denominator!=1:raise ArithmeticError('nonintegral enumerated point')
        xs.append(int(x))
    if len({tuple(p) for p in points})!=len(points) or sorted(set(xs))!=packet['x_coordinates']:
        raise ArithmeticError('integral-list encoding mismatch')
    expected=[]
    for x in packet['x_coordinates']:
        n=x**3+packet['k'];y=isqrt(n)
        if y*y!=n:raise ArithmeticError('listed abscissa is not integral')
        expected.extend([(str(x),str(y))] if y==0 else [(str(x),str(y)),(str(x),str(-y))])
    if set(map(tuple,points))!=set(expected):raise ArithmeticError('both ordinate signs required')
    return dict(exact_relations_checked=True,exact_source_subgroup_index=index,
                basis_independence=independence,torsion_certificate=torsion_bound(packet['k']),
                exact_integral_points_checked=True)


def accept_completion(packet,source):
    """Check receipt integrity; global completion still trusts the named backend."""
    try:
        if (packet.get('schema')!='pp-mordell-completion/1'
            or packet.get('status')!='complete'
            or packet.get('saturation_max_prime')!=-1
            or packet.get('saturation_min_prime')!=2
            or packet.get('backend_saturation_ok') is not True
            or packet.get('unsaturated_primes')!=[]
            or packet.get('complete_basis_by_backend') is not True
            or packet.get('integral_list_complete_by_backend') is not True
            or packet.get('lean_complete_basis_proved') is not False
            or packet.get('lean_integral_list_proved') is not False):return False
        computed=check_completion_arithmetic(packet,source)
        if any(packet.get(k)!=v for k,v in computed.items()):return False
        bound=packet.get('backend_index_bound')
        required=packet.get('backend_required_saturation_primes')
        if (type(bound) is not int or not 1<=bound<=97 or not isinstance(required,list)
            or required!=sorted(set(required))
            or not set(primes(bound) if bound>=2 else [])<=set(required)):return False
        proofs=packet.get('exact_prime_saturation',[])
        if [p['prime'] for p in proofs]!=packet.get('backend_required_saturation_primes'):return False
        return all(p['k']==packet['k'] and p['points']==packet['basis_points']
                   and replay_reduction_saturation(p) for p in proofs)
    except (ValueError,KeyError,TypeError,ArithmeticError):return False


def verify_completion_log(packet,log):
    """Bind the retained global-bound and prime metadata to backend output."""
    bounds=[int(n) for n in re.findall(r'Saturation index bound[^=]*=\s*(\d+)',log)]
    required=sorted({int(p) for s in re.findall(r'Checking saturation at\s*\[([^]]*)\]',log)
                     for p in re.findall(r'\d+',s)})
    return (bool(bounds) and max(bounds)==packet.get('backend_index_bound')
            and required==packet.get('backend_required_saturation_primes')
            and hashlib.sha256(log.encode()).hexdigest()==packet.get('backend_log_sha256'))
