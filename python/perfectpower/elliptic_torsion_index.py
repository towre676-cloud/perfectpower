"""Complete relation lattices and prime-preimage indices with finite torsion.

Supplied free coordinates must span the free witness space. Finite torsion
coordinates are certified injectively by exact point arithmetic, not by a
classification of the full rational torsion subgroup. Replay is not Lean.
"""
from itertools import product
from math import prod
from .elliptic_arithmetic import EllipticCurve, encode_point
from .integer_lifting import smith_certificate, verify_smith
from .elliptic_lattice_verifier import verify_subgroup_presentation
from .elliptic_certificate_verifier import CheckBudget, fields, exact_int, checked_point
from .elliptic_saturation_verifier import combination
from .divisor_square import WorkLimit


def _augmented(rows, r, orders):
    d=r+len(orders)
    return [[row[i] for row in rows]+[-n*int(i==r+j) for j,n in enumerate(orders)] for i in range(d)]


def _relations(smith, count):
    # U A V = D: the zero-diagonal columns of V are a complete Z-kernel.
    V=smith['right'];rank=smith['rank']
    return [[V[i][j] for i in range(count)] for j in range(rank,len(V))]


def _lattice(rows, r, orders):
    smith=smith_certificate(_augmented(rows,r,orders),operation_limit=20000,entry_bit_limit=4096)
    if smith['rank']!=r+len(orders):raise ValueError('coordinates must span the free witness space')
    relations=_relations(smith,len(rows))
    relation_smith=smith_certificate([list(col) for col in zip(*relations)],operation_limit=20000,entry_bit_limit=4096) if relations else None
    return dict(smith=smith,relation_basis=relations,relation_smith=relation_smith,
                group_invariant_factors=[n for n in relation_smith['smith_factors'] if n>1] if relation_smith else [],
                free_rank=r,ambient_lattice_index=prod(smith['smith_factors']))


def torsion_subgroup_index(presentation,basis,torsion_basis,torsion_orders,
                          source_coordinates,generator_coordinates):
    """Index [p^-1 Gamma : Gamma], including every rational p-kernel point.

    Arbitrary dependent source generators and a rank-zero finite group are
    supported. Coordinates are witnesses; they are never inferred by a
    negative bounded membership search.
    """
    if not verify_subgroup_presentation(presentation):raise ValueError('complete subgroup presentation required')
    E=EllipticCurve(presentation['preimage']['curve']);points=[E.checked(p) for p in basis]
    result=dict(schema='pp-elliptic-torsion-subgroup-index/1',presentation=presentation,
                basis=[encode_point(p) for p in points],
                independence=E.independence(points) if points else None,
                torsion_basis=[encode_point(E.checked(p)) for p in torsion_basis],
                torsion_orders=torsion_orders,source_coordinates=source_coordinates,
                generator_coordinates=generator_coordinates,
                source_lattice=_lattice(source_coordinates,len(basis),torsion_orders),
                generator_lattice=_lattice(generator_coordinates,len(basis),torsion_orders),
                actual_subgroup_index=0,complete_mordell_weil_group=False,execution_verified=False)
    a=result['source_lattice']['ambient_lattice_index'];b=result['generator_lattice']['ambient_lattice_index']
    if a%b:raise ValueError('nonintegral inclusion index')
    result['actual_subgroup_index']=a//b
    if not verify_torsion_subgroup_index(result):raise ValueError('torsion coordinate or relation replay failed')
    return result


def verify_torsion_subgroup_index(cert,*,work_limit=8000000,node_limit=100000):
    """Replay exact finite-group injection, coordinates and Smith transcripts."""
    try:
        from .elliptic_certificate_verifier import verify_independence
        budget=CheckBudget(work_limit);budget.packet(cert)
        fields(cert,'schema presentation basis independence torsion_basis torsion_orders source_coordinates generator_coordinates source_lattice generator_lattice actual_subgroup_index complete_mordell_weil_group execution_verified')
        if (cert['schema']!='pp-elliptic-torsion-subgroup-index/1' or
            cert['complete_mordell_weil_group'] is not False or cert['execution_verified'] is not False):return False
        if not verify_subgroup_presentation(cert['presentation'],work_limit=work_limit,node_limit=node_limit):return False
        core=cert['presentation']['preimage'];E=EllipticCurve(core['curve'])
        if type(cert['basis']) is not list or not 0<=len(cert['basis'])<=4:return False
        if type(cert['torsion_basis']) is not list or not 0<=len(cert['torsion_basis'])<=2:return False
        r=len(cert['basis']);t=len(cert['torsion_basis']);d=r+t
        if not d:return False
        basis=[checked_point(E,p) for p in cert['basis']]
        torsion=[checked_point(E,p) for p in cert['torsion_basis']];orders=cert['torsion_orders']
        if type(orders) is not list or len(orders)!=t:return False
        if any(type(n) is not int or not 2<=n<=32 for n in orders) or prod(orders)>256:return False
        if r:
            proof=cert['independence']
            if (type(proof) is not dict or proof.get('curve')!=core['curve'] or
                proof.get('original_points')!=cert['basis'] or proof.get('independent') is not True or
                not verify_independence(proof,work_limit=work_limit,node_limit=node_limit)):return False
        elif cert['independence'] is not None:return False
        # A homomorphism from the product of cyclic groups, plus injectivity.
        for P,n in zip(torsion,orders):
            budget.charge(n)
            if E.mul(P,n) is not None:return False
        images={}
        for cs in product(*(range(n) for n in orders)):
            P=combination(E,torsion,cs,budget)
            if P in images:return False
            images[P]=cs
        all_basis=basis+torsion;indices=[]
        for name,point_key,lattice_key in [('source_coordinates','source_points','source_lattice'),
                                          ('generator_coordinates','generators','generator_lattice')]:
            rows=cert[name];points=core[point_key]
            if type(rows) is not list or len(rows)!=len(points) or len(rows)>16:return False
            if any(type(row) is not list or len(row)!=d or
                   any(type(x) is not int or abs(x)>256 for x in row) for row in rows):return False
            for row,P in zip(rows,points):
                if combination(E,all_basis,row,budget)!=checked_point(E,P):return False
            L=cert[lattice_key];fields(L,'smith relation_basis relation_smith group_invariant_factors free_rank ambient_lattice_index')
            smith=L['smith'];A=_augmented(rows,r,orders)
            if type(smith) is not dict or smith.get('matrix')!=A:return False
            if not verify_smith(smith,operation_limit=20000,entry_bit_limit=4096) or smith['rank']!=d:return False
            relations=L['relation_basis']
            if type(relations) is not list or any(type(row) is not list or
                any(type(x) is not int for x in row) for row in relations):return False
            if relations!=_relations(smith,len(rows)):return False
            R=L['relation_smith']
            if relations:
                if type(R) is not dict or R.get('matrix')!=[list(col) for col in zip(*relations)]:return False
                if not verify_smith(R,operation_limit=20000,entry_bit_limit=4096) or R['rank']!=len(rows)-r:return False
                factors=[n for n in R['smith_factors'] if n>1]
            else:
                if R is not None:return False
                factors=[]
            if type(L['free_rank']) is not int or L['free_rank']!=r:return False
            if type(L['group_invariant_factors']) is not list or any(type(n) is not int for n in L['group_invariant_factors']) or L['group_invariant_factors']!=factors:return False
            index=prod(smith['smith_factors'])
            if exact_int(L['ambient_lattice_index'],1,2**128)!=index:return False
            indices.append(index)
        # Nesting already follows from complete preimage replay; verify it in
        # the ambient coordinates too using the generator Smith divisibility.
        S=cert['generator_lattice']['smith'];U=S['left'];factors=S['smith_factors']
        for row in cert['source_coordinates']:
            if any(sum(a*b for a,b in zip(u,row))%n for u,n in zip(U,factors)):return False
        a,b=indices
        return a%b==0 and exact_int(cert['actual_subgroup_index'],1,2**128)==a//b
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False
