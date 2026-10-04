"""Horner tail domination with complete exceptional residual-root fibres.

Unlike a cutoff that first dominates R away from zero, the certificate keeps
all integer roots of R explicitly. Absolute estimates cover both signs of x.
"""
from fractions import Fraction as Q
from dataclasses import asdict
from . import polyalg as P
from .core import rigid_certificate,verify_certificate,RigidCertificate,integer_power_root
from .residue_cover import integer_polynomial,evaluate,residue_cover,scan_cover
from .sturm_fibres import root_certificate,verify_roots
from .divisor_square import WorkLimit


def _admissible(q,r,d,denominator,bound):
    degree=len(q)-1
    lower=abs(q[-1])-sum(abs(c)*Q(1,bound**(degree-i)) for i,c in enumerate(q[:-1]))
    if lower<=0:return False
    residual=sum(abs(c)*Q(1,bound**((d-1)*degree-i)) for i,c in enumerate(r))
    if residual*denominator>=lower**(d-1):return False
    if d%2 and sum(abs(c)*Q(1,bound**(d*degree-i)) for i,c in enumerate(r))>=lower**d:return False
    return True


def sharp_bound(coefficients,d,*,root_node_limit=100000):
    f=integer_polynomial(coefficients)
    if type(d) is not int or not 2<=d<=64:raise ValueError('integer power in [2,64] required')
    rigid=rigid_certificate(f,d)
    if rigid is None or rigid.exact_identity:return None
    den=rigid.denominator;q=P.poly(Q(x,den) for x in rigid.root_numerators)
    r=P.poly(Q(x,den**d) for x in rigid.remainder_numerators)
    high=1
    while not _admissible(q,r,d,den,high):high*=2
    low=1
    while low<high:
        mid=(low+high)//2
        if _admissible(q,r,d,den,mid):high=mid
        else:low=mid+1
    exceptions=root_certificate(rigid.remainder_numerators,node_limit=root_node_limit)
    return {'kind':'sharp_horner','bound':low-1,'tail_start':low,'rigid_identity':asdict(rigid),
        'residual_roots':exceptions,'exceptional_coordinates':exceptions['roots'],
        'theorem':'Horner root-gap derivation with complete exceptional fibres; Python replay'}


def verify_bound(bound,coefficients,d,*,root_node_limit=100000):
    try:
        f=integer_polynomial(coefficients)
        if type(d) is not int or not 2<=d<=64 or bound['kind']!='sharp_horner':return False
        raw=bound['rigid_identity'];cert=RigidCertificate(**{k:tuple(v) if isinstance(v,list) else v for k,v in raw.items()})
        if any(type(x) is not int for x in (cert.d,cert.denominator,cert.cutoff,*cert.coefficients,*cert.root_numerators,*cert.remainder_numerators)):return False
        if cert.coefficients!=f or cert.d!=d or not verify_certificate(cert) or cert.exact_identity:return False
        b=bound['tail_start']
        if type(b) is not int or b<1 or type(bound['bound']) is not int or bound['bound']!=b-1:return False
        q=P.poly(Q(x,cert.denominator) for x in cert.root_numerators)
        r=P.poly(Q(x,cert.denominator**d) for x in cert.remainder_numerators)
        if not _admissible(q,r,d,cert.denominator,b):return False
        roots=bound['residual_roots']
        return integer_polynomial(roots['coefficients'])==cert.remainder_numerators and verify_roots(roots,node_limit=root_node_limit) and roots['roots']==bound['exceptional_coordinates']
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,OverflowError):return False


def scan_sharp(cover,bound,*,work_limit=100000):
    f=integer_polynomial(cover['coefficients']);d=cover['degree']
    if bound['residual_roots']['nodes_checked']>work_limit:raise WorkLimit('complete residual-root proof exceeds work budget')
    if not verify_bound(bound,f,d,root_node_limit=work_limit):raise ValueError('invalid sharp bound')
    b=bound['bound'];outside=sorted(x for x in bound['exceptional_coordinates'] if abs(x)>b)
    remaining=work_limit-len(outside)
    if remaining<1:raise WorkLimit('exceptional fibres exceed candidate budget')
    scan=scan_cover(cover,-b,b,work_limit=remaining);points=set(scan['points'])
    for x in outside:
        root=integer_power_root(evaluate(f,x),d)
        if root is not None:points.update((x,y) for y in ({root,-root} if d%2==0 else {root}))
    return {**scan,'points':sorted(points),'candidates_checked':scan['candidates_checked']+len(outside),
        'exceptional_coordinates_checked':outside}
