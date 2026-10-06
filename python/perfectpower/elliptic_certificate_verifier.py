"""Bounded, discovery-free checks of rational elliptic arithmetic packets.

The local characters and F2 elimination below do not call the producer's
local_matrix, binary_rows, halving search or independence search. Exact group
arithmetic and the existing signed-remainder Sturm checker are shared.
This is independently implemented Python checking, not a Lean proof.
"""
from math import lcm
from fractions import Fraction as Q
from . import polyalg as P
from .elliptic_arithmetic import EllipticCurve, encode_point, q, rational_literal, integer_literal
from .sturm_fibres import verify_roots
from .divisor_square import WorkLimit

SCOPE='certified lower bound for the rational witness span modulo torsion; not a complete basis'


class CheckBudget:
    def __init__(self, limit):
        if type(limit) is not int or not 1<=limit<=20000000:
            raise ValueError('checker work budget 1 through 20000000 required')
        self.remaining=limit

    def charge(self,n=1):
        self.remaining-=n
        if self.remaining<0:raise WorkLimit('elliptic certificate checker work budget exhausted')

    def packet(self,value):
        stack=[(value,0)]
        while stack:
            v,depth=stack.pop();self.charge()
            if depth>32:raise ValueError('certificate nesting limit')
            if isinstance(v,dict):
                if not all(type(k) is str for k in v):raise ValueError('string field names required')
                self.charge(len(v));stack.extend((x,depth+1) for x in v.values())
            elif isinstance(v,(list,tuple)):
                self.charge(len(v));stack.extend((x,depth+1) for x in v)
            elif type(v) is str:
                if len(v)>20000:raise ValueError('certificate string limit')
                self.charge(len(v)//256)
            elif type(v) is int:
                if abs(v).bit_length()>12000:raise ValueError('certificate integer bit limit')
                self.charge(abs(v).bit_length()//256)
            elif v is not None and type(v) is not bool:
                raise ValueError('exact JSON certificate required')


def fields(packet,names):
    if type(packet) is not dict or set(packet)!=set(names.split()):
        raise ValueError('unsupported or missing certificate fields')


def exact_int(value,lo,hi):
    if type(value) is not int or not lo<=value<=hi:raise ValueError('bounded integer required')
    return value


def model(spec):
    fields(spec,'ainvs')
    if type(spec['ainvs']) is not list or len(spec['ainvs'])!=5:raise ValueError('canonical model required')
    E=EllipticCurve(spec)
    if E.specification!=spec:raise ValueError('canonical rational model required')
    return E


def checked_point(E,p):
    if p is not None:
        if type(p) is not list or len(p)!=2:raise ValueError('canonical point required')
        for v in p:
            if type(v) is not str or rational_literal(q(v,12000))!=v:
                raise ValueError('canonical rational coordinate required')
    result=E.checked(p)
    if encode_point(result)!=p:raise ValueError('canonical point required')
    return result


def check_rational_roots(packet,f,node_limit,budget):
    fields(packet,'schema coefficients denominator_scale integer_certificate roots')
    if packet['schema']!='pp-rational-roots/1':raise ValueError('unsupported rational-root schema')
    f=P.monic(P.poly(f));n=P.degree(f);D=lcm(*(c.denominator for c in f))
    if packet['coefficients']!=[rational_literal(c) for c in f] or packet['denominator_scale']!=rational_literal(Q(D)):
        raise ValueError('rational-root polynomial mismatch')
    cert=packet['integer_certificate']
    fields(cert,'coefficients domain leading_coefficient squarefree_factors squarefree sturm_chain root_bound clipped_interval nodes roots nodes_checked complete execution_verified')
    if not isinstance(cert['squarefree_factors'],(list,tuple)) or len(cert['squarefree_factors'])>n:return_invalid()
    for factor in cert['squarefree_factors']:
        if not isinstance(factor,(list,tuple)) or len(factor)!=2 or not isinstance(factor[1],(list,tuple)) or len(factor[1])>n+1:return_invalid()
    if not isinstance(cert['sturm_chain'],(list,tuple)) or len(cert['sturm_chain'])>n+1:return_invalid()
    if not isinstance(cert['squarefree'],(list,tuple)) or len(cert['squarefree'])>n+1:return_invalid()
    if any(not isinstance(row,(list,tuple)) or len(row)>n+1 for row in cert['sturm_chain']):return_invalid()
    if not isinstance(cert['nodes'],(list,tuple)) or len(cert['nodes'])>node_limit:return_invalid()
    if not isinstance(cert['roots'],(list,tuple)) or len(cert['roots'])>n or any(type(r) is not int for r in cert['roots']):return_invalid()
    g=[int(c*D**(n-i)) for i,c in enumerate(f)]
    if list(cert['coefficients'])!=g or cert['domain']!=[None,None]:raise ValueError('integer-root transform mismatch')
    count=exact_int(cert['nodes_checked'],0,node_limit);budget.charge(count)
    if not verify_roots(cert,node_limit=node_limit):raise ValueError('invalid signed-remainder Sturm certificate')
    roots=[Q(r,D) for r in cert['roots']]
    if packet['roots']!=[rational_literal(r) for r in roots]:raise ValueError('rational-root list mismatch')
    return roots,count


def return_invalid():
    raise ValueError('rational-root certificate allocation limits')


def _verify_halves(cert,budget,node_limit):
    fields(cert,'schema curve target points complete execution_verified method anchor two_torsion_certificate division_certificate node_limit root_nodes')
    if cert['schema']!='pp-rational-halves/1' or cert['complete'] is not True or cert['execution_verified'] is not False:
        return False
    E=model(cert['curve']);target=checked_point(E,cert['target'])
    producer_limit=exact_int(cert['node_limit'],1,100000)
    roots,used=check_rational_roots(cert['two_torsion_certificate'],E.cubic,min(node_limit,producer_limit),budget)
    if len(roots) not in (0,1,3):return False
    two=[E.uncomplete((r,Q(0))) for r in roots]
    anchor=checked_point(E,cert['anchor']);division=cert['division_certificate']
    if target is None:
        if cert['method']!='two_torsion' or anchor is not None or division is not None:return False
        expected=[None,*two]
    else:
        candidates=None
        if division is not None:
            candidates,count=check_rational_roots(division,E.division_polynomial(target),min(node_limit,producer_limit)-used,budget)
            used+=count
        if anchor is not None:
            if cert['method']!='torsion_coset' or E.mul(anchor,2)!=target:return False
            if candidates is not None and anchor[0] not in candidates:return False
            expected=[E.add(anchor,t) for t in (None,*two)]
        else:
            if cert['method']!='empty_division_fibre' or candidates is None:return False
            # Complete x roots of [2]H=target. Test both completed y signs;
            # no root-discovery call is made during checking.
            from .elliptic_arithmetic import sqrtq
            for x in candidates:
                budget.charge();y=sqrtq(P.evaluate(E.cubic,x))
                if y is not None:
                    for yy in {y,-y}:
                        if E.mul(E.uncomplete((x,yy)),2)==target:return False
            expected=[]
    expected=sorted(expected,key=lambda p:encode_point(p) or [])
    if type(cert['points']) is not list:return False
    supplied=[checked_point(E,p) for p in cert['points']]
    return supplied==expected and type(cert['root_nodes']) is int and cert['root_nodes']==used and used<=node_limit


def verify_halves(cert,*,work_limit=2000000,node_limit=100000):
    try:
        exact_int(node_limit,1,100000);budget=CheckBudget(work_limit);budget.packet(cert)
        return _verify_halves(cert,budget,node_limit)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False


def sieve(bound,budget):
    exact_int(bound,2,20000);budget.charge(bound)
    prime=bytearray(b'\x01')*(bound+1);prime[:2]=b'\x00\x00'
    for p in range(2,bound+1):
        if prime[p]:
            for m in range(p*p,bound+1,p):prime[m]=0
    return [p for p in range(2,bound+1) if prime[p]]


def horner(f,x):
    v=0
    for c in reversed(f):v=v*x+c
    return v


def character_rows(E,points,bound,budget):
    """Independently enumerate every degree-one good-reduction character."""
    s=lcm(*(a.denominator for a in E.a))
    f=[int(16*s**6*E.b6),int(8*s**4*E.b4),int(s*s*E.b2),1]
    rows=[0]*len(points);packets=[];columns=0
    for p in sieve(bound,budget):
        if p<5 or s%p==0 or E.discriminant.numerator%p==0 or E.discriminant.denominator%p==0:continue
        budget.charge(p)
        roots=[r for r in range(p) if horner(f,r)%p==0]
        if not roots:continue
        packets.append(dict(prime=p,roots=roots))
        for i,point in enumerate(points):
            budget.charge(len(roots))
            if point is None:continue
            # x in the integral model. Nonintegral x has even negative
            # valuation and unit square class at infinity, hence zero bits.
            x=4*s*s*point[0]
            if x.denominator%p==0:continue
            residue=x.numerator*pow(x.denominator,-1,p)%p
            for j,r in enumerate(roots):
                value=(residue-r)%p
                if not value:value=(f[1]+2*f[2]*r+3*r*r)%p
                if not value:raise ValueError('bad integral-model reduction')
                if pow(value,(p-1)//2,p)==p-1:rows[i]+=1<<(columns+j)
        columns+=len(roots)
    return rows,packets,columns


def f2_rank(rows,columns,budget):
    """Column-pivot Gaussian elimination, distinct from producer row masks."""
    rows=list(rows);rank=0
    for column in range(columns):
        budget.charge(len(rows))
        pivot=next((i for i in range(rank,len(rows)) if rows[i]>>column&1),None)
        if pivot is None:continue
        rows[rank],rows[pivot]=rows[pivot],rows[rank]
        for i in range(rank+1,len(rows)):
            if rows[i]>>column&1:rows[i]^=rows[rank]
        rank+=1
        if rank==len(rows):break
    return rank


def verify_independence(cert,*,work_limit=2000000,node_limit=100000):
    try:
        exact_int(node_limit,1,100000);budget=CheckBudget(work_limit);budget.packet(cert)
        fields(cert,'schema curve original_points working_points auxiliary_torsion two_torsion_dimension two_torsion_proof primes matrix_rows columns matrix_rank rank_lower_bound halving_steps prime_bound independent scope complete_basis execution_verified')
        if cert['schema']!='pp-elliptic-independence/2' or cert['scope']!=SCOPE or cert['complete_basis'] is not False or cert['execution_verified'] is not False:return False
        if type(cert['independent']) is not bool:return False
        E=model(cert['curve'])
        for key,limit in (('original_points',64),('working_points',64),('auxiliary_torsion',15),('halving_steps',64)):
            if type(cert[key]) is not list or len(cert[key])>limit:return False
        work=[checked_point(E,p) for p in cert['original_points']]
        aux=[checked_point(E,p) for p in cert['auxiliary_torsion']]
        if len(set(aux))!=len(aux) or any(p is None or E.mul(p,16) is not None for p in aux):return False
        proof=cert['two_torsion_proof'];_,f=E.integral_cubic()
        if proof['kind']=='irreducible_cubic_mod_prime':
            fields(proof,'kind prime');p=exact_int(proof['prime'],5,20000)
            if p not in sieve(p,budget):return False
            budget.charge(p)
            if any(horner(f,r)%p==0 for r in range(p)):return False
            t=0
        elif proof['kind']=='complete_rational_roots':
            fields(proof,'kind certificate');roots,_=check_rational_roots(proof['certificate'],f,node_limit,budget)
            if len(roots) not in (0,1,3):return False
            t={0:0,1:1,3:2}[len(roots)]
        else:return False
        if type(cert['two_torsion_dimension']) is not int or t!=cert['two_torsion_dimension']:return False
        for step in cert['halving_steps']:
            fields(step,'indices offset replace half');ii=step['indices']
            if type(ii) is not list or not ii or len(ii)>len(work) or len(set(ii))!=len(ii):return False
            if any(type(i) is not int or not 0<=i<len(work) for i in ii):return False
            i=step['replace']
            if type(i) is not int or i not in ii:return False
            half=checked_point(E,step['half']);offset=checked_point(E,step['offset'])
            if half is None or E.mul(offset,16) is not None:return False
            budget.charge(len(ii)*16);total=offset
            for j in ii:total=E.add(total,work[j])
            if E.mul(half,2)!=total:return False
            work[i]=half
        if [encode_point(p) for p in work]!=cert['working_points']:return False
        bound=exact_int(cert['prime_bound'],2,2000)
        rows,packets,columns=character_rows(E,work+aux,bound,budget)
        rank=f2_rank(rows,columns,budget);lower=max(0,min(len(work),rank-t))
        if any(type(cert[k]) is not int for k in ('columns','matrix_rank','rank_lower_bound')):return False
        if type(cert['matrix_rows']) is not list or len(cert['matrix_rows'])!=len(rows):return False
        for supplied,wanted in zip(cert['matrix_rows'],rows):
            if type(supplied) is not str or str(integer_literal(supplied))!=supplied or integer_literal(supplied)!=wanted:return False
        if type(cert['primes']) is not list:return False
        for packet in cert['primes']:
            fields(packet,'prime roots')
            if type(packet['prime']) is not int or type(packet['roots']) is not list or any(type(r) is not int for r in packet['roots']):return False
        return packets==cert['primes'] and columns==cert['columns'] and rank==cert['matrix_rank'] and lower==cert['rank_lower_bound'] and cert['independent']==(lower==len(work))
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False
