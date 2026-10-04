"""Exact graph weight repairs through a small Woodbury defect matrix.

Reuse a supplied base measure. Weight decreases, zero weights and simultaneous
changes are permitted; rank loss returns an undefined distribution explicitly.
Classical determinant-lemma/Woodbury arithmetic in the cyclotomic field.
"""
from .connection_measure import (ConnectionMeasure,verify_measure,_multiply,
    _inverse,_encode,_decode,_matrix_encode)
from .connection_polytope import algebra_determinant
from .divisor_square import WorkLimit


def _prepare(measure,weights,work_limit):
    if not isinstance(measure,ConnectionMeasure):raise ValueError('ConnectionMeasure required')
    if measure.inverse is None:raise ValueError('full-rank base measure required')
    weights=measure.graph.weights(weights);indices=[i for i,(a,b) in enumerate(zip(measure.weights,weights)) if a!=b]
    n=measure.graph.vertices;m=len(weights);k=len(indices)
    if type(work_limit) is not int or work_limit<1:raise ValueError('positive algebra budget required')
    if k>64 or 3*n*n*k+3*n*k*k+k**3+m*m*n>work_limit:raise WorkLimit('weight update work estimate exceeds budget')
    field=measure.field;zero=field.element(0);one=field.element(1)
    delta=[weights[i]-measure.weights[i] for i in indices]
    rows=[measure.b[i] for i in indices]
    # U=B_J* diag(delta), V=B_J. No inversion of diag(delta), allowing
    # negative changes and complete deletion of an edge weight.
    u=[[measure.graph.conjugate(rows[j][i])*delta[j] for j in range(k)] for i in range(n)]
    pu=_multiply(measure.inverse,u,field) if k else [[] for _ in range(n)]
    vp=_multiply(rows,measure.inverse,field) if k else []
    s=_multiply(rows,pu,field) if k else []
    s=[[x+(one if i==j else zero) for j,x in enumerate(row)] for i,row in enumerate(s)]
    return weights,indices,u,rows,pu,vp,s


def _updated_receipt(measure,weights,inverse,determinant):
    graph=measure.graph;field=measure.field;n=graph.vertices
    support=graph.support([i for i,w in enumerate(weights) if w])
    kernel=None
    if inverse is not None:
        adjoint=[[graph.conjugate(row[j]) for row in measure.b] for j in range(n)]
        kernel=_multiply(_multiply([[x*w for x in row] for w,row in zip(weights,measure.b)],inverse,field),adjoint,field)
    return {'vertices':n,'edges':graph.edges,'power':graph.power,'weights':[str(w) for w in weights],
        'status':'EXACT_BASIS_MEASURE' if inverse is not None else 'RANK_DEFICIENT',
        'positive_support':support,'normalizing_determinant':_encode(determinant),
        'laplacian_inverse':None if inverse is None else _matrix_encode(inverse),
        'transfer_kernel':None if kernel is None else _matrix_encode(kernel),
        'edge_marginals':None if kernel is None else [_encode(kernel[i][i]) for i in range(len(weights))],
        'basis_enumerations':0,'execution_verified':False,
        'scope':'exact determinant-weighted graph bases; not probabilities of integer solutions'}


def reweight(measure,weights,*,work_limit=2000000):
    new,indices,u,v,pu,vp,s=_prepare(measure,weights,work_limit);field=measure.field;k=len(indices)
    ratio=algebra_determinant(s,field);zero=field.element(0)
    sinv=None if ratio==zero else _inverse(s,field) if k else []
    inverse=None
    if sinv is not None:
        repair=_multiply(_multiply(pu,sinv,field),vp,field) if k else [[zero for _ in row] for row in measure.inverse]
        inverse=[[x-y for x,y in zip(row,change)] for row,change in zip(measure.inverse,repair)]
    updated=_updated_receipt(measure,new,inverse,measure.z*ratio)
    if (updated['positive_support']['rank']<measure.graph.vertices)!=(ratio==zero):raise AssertionError('update determinant and support disagree')
    receipt={'schema':'pp-connection-reweight/1','base':measure.receipt(),'updated':updated,
        'changed_edges':indices,'defect_matrix':_matrix_encode(s),
        'defect_inverse':None if sinv is None else _matrix_encode(sinv),
        'determinant_ratio':_encode(ratio),'inversion_dimension':k if k and sinv is not None else 0,
        'execution_verified':False,'scope':'exact simultaneous nonnegative graph weight changes from a full-rank base'}
    if not verify_reweight(receipt,work_limit=work_limit):raise AssertionError('connection update replay failed')
    return receipt


def verify_reweight(receipt,*,work_limit=2000000):
    """Validate the base once, then small repair identities; no new n×n inverse.

    Determinant of the updated large Laplacian is not rediscovered. Full-rank
    base determinant/inverse are checked by the established base verifier.
    """
    try:
        if receipt['schema']!='pp-connection-reweight/1' or receipt['execution_verified'] is not False:return False
        # from_receipt validates the base; only the supplied k×k inverse is used.
        base=ConnectionMeasure.from_receipt(receipt['base'],work_limit=work_limit)
        weights,indices,u,v,pu,vp,s=_prepare(base,receipt['updated']['weights'],work_limit)
        field=base.field;zero=field.element(0);one=field.element(1);k=len(indices)
        ratio=algebra_determinant(s,field)
        if receipt['changed_edges']!=indices or receipt['defect_matrix']!=_matrix_encode(s) or _decode(receipt['determinant_ratio'],field)!=ratio:return False
        if type(receipt['inversion_dimension']) is not int or receipt['inversion_dimension']!=(k if k and ratio!=zero else 0):return False
        inverse=None
        if ratio==zero:
            if receipt['defect_inverse'] is not None:return False
        else:
            sinv=[[_decode(x,field) for x in row] for row in receipt['defect_inverse']]
            if len(sinv)!=k or any(len(row)!=k for row in sinv):return False
            identity=_multiply(s,sinv,field) if k else []
            if any(identity[i][j]!=(one if i==j else zero) for i in range(k) for j in range(k)):return False
            repair=_multiply(_multiply(pu,sinv,field),vp,field) if k else [[zero for _ in row] for row in base.inverse]
            inverse=[[x-y for x,y in zip(row,change)] for row,change in zip(base.inverse,repair)]
        expected=_updated_receipt(base,weights,inverse,base.z*ratio)
        if (expected['positive_support']['rank']<base.graph.vertices)!=(ratio==zero):return False
        # Normalize tuple/list differences after JSON round trips.
        supplied=dict(receipt['updated']);supplied['edges']=tuple(tuple(e) for e in supplied['edges'])
        return supplied==expected
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,OverflowError):return False
