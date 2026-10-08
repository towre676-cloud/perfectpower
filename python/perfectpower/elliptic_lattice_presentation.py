"""Exact row-Hermite/Smith presentations for complete prime-preimage packets.

The lattice is {a in Z^r : sum a_i P_i lies in p E(Q)}. Its index is not
an index of actual elliptic subgroups when the source generators depend.
"""
from .elliptic_subgroups import subgroup_preimage, linear_combination
from .elliptic_arithmetic import encode_point
from .elliptic_saturation import bounded_saturation


def identity(n):return [[int(i==j) for j in range(n)] for i in range(n)]

def lattice_data(preimage):
    p=preimage['prime'];r=len(preimage['source_points']);R=preimage['relation_basis']
    pivots=[next(j for j,x in enumerate(row) if x) for row in R]
    lookup=dict(zip(pivots,R));nonpivots=[j for j in range(r) if j not in lookup]
    H=[list(lookup[j]) if j in lookup else [p*int(j==k) for k in range(r)] for j in range(r)]
    C=identity(r)
    for pivot,row in lookup.items():
        for j in nonpivots:C[pivot][j]=-row[j]
    order=pivots+nonpivots
    U=[[int(order[i]==j) for j in range(r)] for i in range(r)]
    V=[[C[i][order[j]] for j in range(r)] for i in range(r)]
    inclusion=identity(r)
    for pivot,row in lookup.items():
        inclusion[pivot]=[p if j==pivot else -row[j] for j in range(r)]
    return dict(row_hermite=H,smith_left=U,smith_right=V,
                smith_diagonal=[1]*len(R)+[p]*len(nonpivots),
                coefficient_lattice_index=p**len(nonpivots),
                residue_relation_cardinality=p**len(R),source_inclusion=inclusion)


def from_preimage(preimage):
    return dict(schema='pp-elliptic-prime-preimage-presentation/1',preimage=preimage,
                lattice=lattice_data(preimage),actual_subgroup_index=None,
                scope='coefficient lattice normal forms and complete rational prime-preimage generators',
                complete_mordell_weil_group=False,execution_verified=False)


def subgroup_presentation(E,points,prime=5,node_limit=100000):
    return from_preimage(subgroup_preimage(E,points,prime,node_limit))


def saturation_presentation(E,points,primes=None,max_steps=8,coefficient_bound=2,
                            membership_limit=100000,node_limit=100000):
    cert=bounded_saturation(E,points,[5,7] if primes is None else primes,max_steps,
                            coefficient_bound,membership_limit,node_limit)
    return dict(schema='pp-elliptic-prime-saturation-presentation/1',saturation=cert,
                stage_lattices=[lattice_data(s['preimage']) for s in cert['stages']],
                actual_subgroup_indices=None,complete_mordell_weil_group=False,
                execution_verified=False)


def subgroup_index(presentation,basis,source_coordinates,replacement_coordinates):
    """Actual subgroup index when a free witness basis and both coordinates exist.

    The rational p-kernel must be trivial. Independence modulo torsion is
    certified by the existing good-reduction engine, not guessed from height.
    """
    from .elliptic_arithmetic import EllipticCurve
    from .elliptic_lattice_verifier import verify_subgroup_presentation,verify_subgroup_index,determinant,matrix
    if not verify_subgroup_presentation(presentation):raise ValueError('complete subgroup presentation required')
    core=presentation['preimage'];E=EllipticCurve(core['curve']);r=len(basis)
    if not 1<=r<=4 or len(core['source_points'])!=r:raise ValueError('one through four square free-basis coordinates required')
    if not matrix(source_coordinates,r) or not matrix(replacement_coordinates,r):raise ValueError('bounded integer coordinate matrices required')
    if core['kernel_fibre']['points']!=[None]:raise ValueError('trivial rational prime kernel required for this free-index certificate')
    points=[E.checked(p) for p in basis];independence=E.independence(points)
    if not independence['independent']:raise ValueError('independent witness basis not certified')
    a=abs(determinant(source_coordinates));b=abs(determinant(replacement_coordinates))
    if not a or not b or a%b:raise ValueError('full-rank nested integer coordinate lattices required')
    result=dict(schema='pp-elliptic-subgroup-index/1',presentation=presentation,
                basis=[encode_point(p) for p in points],independence=independence,
                source_coordinates=source_coordinates,replacement_coordinates=replacement_coordinates,
                actual_subgroup_index=a//b,complete_mordell_weil_group=False,execution_verified=False)
    if not verify_subgroup_index(result):raise ValueError('coordinate equations or actual index replay failed')
    return result
