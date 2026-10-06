"""Discovery-free replay for tripling and composed rational division packets.

The coordinate numerator is expanded independently of the producer's division
polynomial recurrence. Shared exact point arithmetic and Sturm replay are used.
No claim of Lean verification of this Python interpreter is made.
"""
from fractions import Fraction as Q
from . import polyalg as P
from .elliptic_arithmetic import encode_point, sqrtq
from .elliptic_certificate_verifier import (CheckBudget,fields,exact_int,model,
    checked_point,check_rational_roots,_verify_halves)
from .divisor_square import WorkLimit


def polynomials(E,target):
    # Independent expanded phi_3; p=-c4/48, q=-c6/864 are short invariants.
    a=-E.c4/48;b=-E.c6/864;shift=E.b2/12
    psi=(-a*a,12*b,6*a,0,3)
    phi=(8*a**3*b+64*b**3,9*a**4+96*a*b*b,48*a*a*b,
         36*a**3+48*b*b,-24*a*b,30*a*a,-96*b,-12*a,0,1)
    psi=P.compose_linear(P.poly(psi),shift,1)
    phi=P.compose_linear(P.poly(phi),shift,1)
    f=None if target is None else P.add(phi,P.scale(P.power(psi,2),-target[0]-shift))
    return psi,f


def lifted(E,roots,target,budget):
    out=set()
    for x in roots:
        budget.charge();y=sqrtq(P.evaluate(E.cubic,x))
        if y is not None:
            for yy in {y,-y}:
                h=E.uncomplete((x,yy))
                if E.mul(h,3)==target:out.add(h)
    return out


def canonical(points):return sorted(set(points),key=lambda h:encode_point(h) or [])


def _verify_thirds(cert,budget,node_limit):
    fields(cert,'schema curve target points complete execution_verified method anchor three_torsion_certificate division_certificate node_limit root_nodes')
    if cert['schema']!='pp-rational-thirds/1' or cert['complete'] is not True or cert['execution_verified'] is not False:return False
    E=model(cert['curve']);target=checked_point(E,cert['target'])
    limit=min(node_limit,exact_int(cert['node_limit'],1,100000))
    psi,f=polynomials(E,target)
    roots,used=check_rational_roots(cert['three_torsion_certificate'],psi,limit,budget)
    kernel=canonical({None,*lifted(E,roots,None,budget)})
    anchor=checked_point(E,cert['anchor']);division=cert['division_certificate']
    if target is None:
        if cert['method']!='three_torsion' or anchor is not None or division is not None:return False
        expected=kernel
    else:
        candidates=None
        if division is not None:
            candidates,count=check_rational_roots(division,f,limit-used,budget);used+=count
        if anchor is None:
            if cert['method']!='empty_division_fibre' or candidates is None:return False
            if lifted(E,candidates,target,budget):return False
            expected=[]
        else:
            if cert['method']!='torsion_coset' or E.mul(anchor,3)!=target:return False
            if candidates is not None and anchor[0] not in candidates:return False
            expected=canonical(E.add(anchor,t) for t in kernel)
    if type(cert['points']) is not list or len(cert['points'])>9:return False
    supplied=[checked_point(E,h) for h in cert['points']]
    return supplied==expected and type(cert['root_nodes']) is int and cert['root_nodes']==used and used<=limit


def verify_thirds(cert,*,work_limit=2000000,node_limit=100000):
    try:
        exact_int(node_limit,1,100000);budget=CheckBudget(work_limit);budget.packet(cert)
        return _verify_thirds(cert,budget,node_limit)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False


def _verify_division(cert,budget,node_limit):
    fields(cert,'schema curve target scalar factors stages points complete execution_verified node_limit root_nodes branch_limit')
    if cert['schema']!='pp-rational-division/1' or cert['complete'] is not True or cert['execution_verified'] is not False:return False
    E=model(cert['curve']);target=checked_point(E,cert['target'])
    scalar=exact_int(cert['scalar'],1,36);n=scalar;fs=[]
    for prime in (2,3):
        while n%prime==0:fs.append(prime);n//=prime
    if n!=1 or type(cert['factors']) is not list or any(type(p) is not int for p in cert['factors']) or cert['factors']!=fs:return False
    branch=exact_int(cert['branch_limit'],1,64)
    limit=min(node_limit,exact_int(cert['node_limit'],1,100000));used=0
    if type(cert['stages']) is not list or len(cert['stages'])!=len(fs):return False
    frontier=[target]
    for prime,stage in zip(fs,cert['stages']):
        fields(stage,'prime targets fibres points')
        if type(stage['prime']) is not int or stage['prime']!=prime or stage['targets']!=[encode_point(h) for h in frontier]:return False
        if type(stage['fibres']) is not list or len(stage['fibres'])!=len(frontier):return False
        out=[]
        for h,packet in zip(frontier,stage['fibres']):
            if type(packet) is not dict or packet.get('curve')!=cert['curve'] or packet.get('target')!=encode_point(h):return False
            # Enforce the producer's shared remainder, not a fresh budget per fibre.
            if type(packet.get('node_limit')) is not int or packet['node_limit']!=cert['node_limit']-used:return False
            check=_verify_halves if prime==2 else _verify_thirds
            if not check(packet,budget,limit-used):return False
            used+=packet['root_nodes']
            out.extend(checked_point(E,v) for v in packet['points'])
            if len(out)>branch:return False
        frontier=canonical(out)
        if stage['points']!=[encode_point(h) for h in frontier]:return False
    if type(cert['points']) is not list or cert['points']!=[encode_point(h) for h in frontier]:return False
    budget.charge(len(frontier)*scalar)
    return (type(cert['root_nodes']) is int and cert['root_nodes']==used and used<=limit
            and all(E.mul(h,scalar)==target for h in frontier))


def verify_division(cert,*,work_limit=2000000,node_limit=100000):
    try:
        exact_int(node_limit,1,100000);budget=CheckBudget(work_limit);budget.packet(cert)
        return _verify_division(cert,budget,node_limit)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False
