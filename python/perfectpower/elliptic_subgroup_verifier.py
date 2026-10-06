"""Discovery-free finite relation-space and subgroup preimage replay.

RREF correctness is checked by exhaustive finite-field span membership rather
than by the producer's elimination implementation. Prime fibres use existing
exact replay. The resulting group-generation argument is documented separately.
"""
from itertools import product
from .elliptic_arithmetic import encode_point
from .elliptic_certificate_verifier import (CheckBudget,fields,exact_int,model,
    checked_point,_verify_halves)
from .elliptic_division_verifier import _verify_thirds
from .divisor_square import WorkLimit


def _check(cert,budget,node_limit):
    fields(cert,'schema curve source_points prime kernel_fibre projective_fibres relation_basis relation_dimension replacement_equations replacement_points generators complete scope complete_mordell_weil_group execution_verified node_limit root_nodes')
    if (cert['schema']!='pp-elliptic-subgroup-preimage/1' or cert['complete'] is not True
        or cert['execution_verified'] is not False or cert['complete_mordell_weil_group'] is not False
        or cert['scope']!='complete generators for the rational prime-preimage of the supplied subgroup'):return False
    p=exact_int(cert['prime'],2,3);E=model(cert['curve'])
    if type(cert['source_points']) is not list or len(cert['source_points'])>4:return False
    source=[checked_point(E,h) for h in cert['source_points']];r=len(source)
    limit=min(node_limit,exact_int(cert['node_limit'],1,100000))
    replay=_verify_halves if p==2 else _verify_thirds
    kernel=cert['kernel_fibre']
    if type(kernel) is not dict or kernel.get('curve')!=cert['curve'] or kernel.get('target') is not None or kernel.get('node_limit')!=cert['node_limit']:return False
    if not replay(kernel,budget,limit):return False
    used=kernel['root_nodes'];rows=cert['projective_fibres'];expected_lines=[]
    for pivot in range(r):
        # Unique representative: zeros before the pivot, then 1, then any tail.
        for tail in product(range(p),repeat=r-pivot-1):expected_lines.append((0,)*pivot+(1,)+tail)
    expected_lines.sort()
    if type(rows) is not list or len(rows)!=len(expected_lines):return False
    divisible=set();lookup={}
    for row,v in zip(rows,expected_lines):
        fields(row,'coefficients fibre')
        if type(row['coefficients']) is not list or any(type(c) is not int for c in row['coefficients']) or row['coefficients']!=list(v):return False
        target=None
        for h,c in zip(source,v):target=E.add(target,E.mul(h,c))
        fibre=row['fibre']
        if type(fibre) is not dict or fibre.get('curve')!=cert['curve'] or fibre.get('target')!=encode_point(target):return False
        if type(fibre.get('node_limit')) is not int or fibre['node_limit']!=cert['node_limit']-used:return False
        if not replay(fibre,budget,limit-used):return False
        used+=fibre['root_nodes'];lookup[v]=fibre
        if fibre['points']:divisible.add(v)
    basis=cert['relation_basis'];dim=exact_int(cert['relation_dimension'],0,r)
    if type(basis) is not list or len(basis)!=dim:return False
    pivots=[]
    for row in basis:
        if type(row) is not list or len(row)!=r or any(type(c) is not int or not 0<=c<p for c in row):return False
        pivot=next((i for i,c in enumerate(row) if c),None)
        if pivot is None or row[pivot]!=1 or (pivots and pivot<=pivots[-1]):return False
        pivots.append(pivot)
    if any(basis[i][j]!=(1 if i==k else 0) for i in range(dim) for k,j in enumerate(pivots)):return False
    # Compute every vector in the given basis span, and independently classify
    # every scalar multiple of every completely tested projective line.
    span={tuple(sum(c*b[j] for c,b in zip(cs,basis))%p for j in range(r)) for cs in product(range(p),repeat=dim)}
    actual={(0,)*r}
    for v in divisible:
        for c in range(1,p):actual.add(tuple(c*x%p for x in v))
    budget.charge(len(span)+len(actual))
    if span!=actual:return False
    replacements=list(source);equations=[]
    for row,pivot in zip(basis,pivots):
        fibre=lookup[tuple(row)];anchor=checked_point(E,fibre['points'][0])
        total=None
        for h,c in zip(source,row):total=E.add(total,E.mul(h,c))
        if E.mul(anchor,p)!=total:return False
        replacements[pivot]=anchor
        equations.append(dict(pivot=pivot,coefficients=row,preimage=encode_point(anchor)))
    # JSON equality alone identifies bool with int; strict finite pivot typing.
    if type(cert['replacement_equations']) is not list or len(cert['replacement_equations'])!=dim:return False
    for given,want in zip(cert['replacement_equations'],equations):
        fields(given,'pivot coefficients preimage')
        if type(given['pivot']) is not int or type(given['coefficients']) is not list or any(type(c) is not int for c in given['coefficients']) or given!=want:return False
    if cert['replacement_points']!=[encode_point(h) for h in replacements]:return False
    expected=set(replacements)
    expected.update(checked_point(E,h) for h in kernel['points']);expected.discard(None)
    expected=sorted(expected,key=lambda h:encode_point(h))
    return (type(cert['generators']) is list and cert['generators']==[encode_point(h) for h in expected]
            and type(cert['root_nodes']) is int and cert['root_nodes']==used and used<=limit)


def verify_subgroup_preimage(cert,*,work_limit=2000000,node_limit=100000):
    try:
        exact_int(node_limit,1,100000);budget=CheckBudget(work_limit);budget.packet(cert)
        return _check(cert,budget,node_limit)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False
