"""Complete rational tripling and staged 2/3 division, with exact evidence.

An exact anchor translates the complete rational torsion kernel. Without an
anchor, a full rational-root certificate closes the finite target fibre.
All coordinate lifts are checked against the full generalized group law.
"""
from fractions import Fraction as Q
from . import polyalg as P
from .elliptic_arithmetic import (encode_point, q, sqrtq, root_budget,
                                 rational_root_certificate, discovered_roots)
from .divisor_square import WorkLimit


def ordered(points):
    return sorted(set(points),key=lambda h:encode_point(h) or [])


def tripling_polynomials(E):
    """Return psi_3 and phi_3 in the original completed x coordinate.

    On u=x+A/3, Y²=u³+p*u+q, [3]u=phi_3(u)/psi_3(u)².
    The returned numerator remains a SHORT coordinate numerator.
    """
    C,B,A,_=E.cubic
    p=B-A*A/3;r=C-A*B/3+2*A**3/27
    f=(r,p,Q(0),Q(1))
    psi=P.poly((-p*p,12*r,6*p,0,3))
    six=P.poly((-8*r*r-p**3,-4*p*r,-5*p*p,20*r,5*p,0,1))
    phi=P.add(P.mul(P.X,P.power(psi,2)),P.scale(P.mul(f,six),-8))
    return P.compose_linear(psi,A/3,1),P.compose_linear(phi,A/3,1)


def tripling_equation(E,target):
    target=E.checked(target)
    if target is None:raise ValueError('finite target required')
    psi,phi=tripling_polynomials(E);A=E.cubic[2]
    return P.add(phi,P.scale(P.power(psi,2),-target[0]-A/3))


def lifts(E,roots,scalar,target):
    out=[]
    for x in roots:
        y=sqrtq(P.evaluate(E.cubic,x))
        if y is not None:
            for yy in sorted({y,-y}):
                h=E.uncomplete((x,yy))
                if E.mul(h,scalar)==target:out.append(h)
    return ordered(out)


def rational_thirds(E,p,node_limit=100000):
    root_budget(node_limit);p=E.checked(p)
    psi,_=tripling_polynomials(E)
    torsion=rational_root_certificate(psi,node_limit)
    used=torsion['integer_certificate']['nodes_checked']
    kernel=ordered([None,*lifts(E,(q(x) for x in torsion['roots']),3,None)])
    anchor=None;division=None
    if p is None:
        out=kernel;method='three_torsion'
    else:
        f=tripling_equation(E,p)
        # Discovery need only provide one exact point. Completeness comes from
        # the kernel certificate, never from exhaustion of this shortcut.
        for x in discovered_roots(f):
            candidates=lifts(E,[x],3,p)
            if candidates:
                anchor=candidates[0];break
        if anchor is None:
            if used>=node_limit:raise WorkLimit('shared tripling root budget exhausted')
            division=rational_root_certificate(f,node_limit-used)
            used+=division['integer_certificate']['nodes_checked']
            candidates=lifts(E,(q(x) for x in division['roots']),3,p)
            if candidates:anchor=candidates[0]
        out=[] if anchor is None else ordered(E.add(anchor,t) for t in kernel)
        method='empty_division_fibre' if anchor is None else 'torsion_coset'
    if not all(E.mul(h,3)==p for h in out):raise ArithmeticError('tripling polynomial/group mismatch')
    result=dict(schema='pp-rational-thirds/1',curve=E.specification,target=encode_point(p),
                points=[encode_point(h) for h in out],complete=True,execution_verified=False,
                method=method,anchor=encode_point(anchor),three_torsion_certificate=torsion,
                division_certificate=division,node_limit=node_limit,root_nodes=used)
    from .elliptic_certificate_verifier import CheckBudget
    CheckBudget(2000000).packet(result)
    return result


def factors(scalar):
    if type(scalar) is not int or not 1<=scalar<=36:
        raise ValueError('positive scalar 1 through 36 required')
    n=scalar;out=[]
    for p in (2,3):
        while n%p==0:out.append(p);n//=p
    if n!=1:raise ValueError('only prime factors 2 and 3 supported')
    return out


def rational_division(E,p,scalar,node_limit=100000,branch_limit=64):
    fs=factors(scalar);root_budget(node_limit)
    if type(branch_limit) is not int or not 1<=branch_limit<=64:
        raise ValueError('branch limit 1 through 64 required')
    p=E.checked(p);frontier=[p];stages=[];used=0
    for prime in fs:
        packets=[];out=[]
        for target in frontier:
            if used>=node_limit:raise WorkLimit('shared division root budget exhausted')
            packet=(E.rational_halves(target,node_limit-used) if prime==2
                    else rational_thirds(E,target,node_limit-used))
            used+=packet['root_nodes'];packets.append(packet)
            out.extend(E.checked(h) for h in packet['points'])
            if len(out)>branch_limit:raise WorkLimit('division branch budget exhausted')
        next_frontier=ordered(out)
        stages.append(dict(prime=prime,targets=[encode_point(h) for h in frontier],
                           fibres=packets,points=[encode_point(h) for h in next_frontier]))
        frontier=next_frontier
    if not all(E.mul(h,scalar)==p for h in frontier):raise ArithmeticError('composed division mismatch')
    result=dict(schema='pp-rational-division/1',curve=E.specification,target=encode_point(p),
                scalar=scalar,factors=fs,stages=stages,points=[encode_point(h) for h in frontier],
                complete=True,execution_verified=False,node_limit=node_limit,
                root_nodes=used,branch_limit=branch_limit)
    from .elliptic_certificate_verifier import CheckBudget
    CheckBudget(2000000).packet(result)
    return result
