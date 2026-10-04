"""Exact supplied polynomial decomposition certificates, without cancellation.

A check f=phi∘F and g=phi∘G does NOT imply f(x)=g(y) iff F(x)=G(y).
No Bilu–Tichy converse or rational/integer point completeness is claimed.
"""
from . import polyalg as P
from .core import mul


def compose(outer,inner):
    outer,inner=P.poly(outer),P.poly(inner)
    result=P.ZERO
    for coefficient in reversed(outer):
        result=P.add(mul(result,inner),P.poly((coefficient,)))
    return result


def supplied_decomposition(f,g,outer,F,G):
    f,g,outer,F,G=map(P.poly,(f,g,outer,F,G))
    if compose(outer,F)!=f or compose(outer,G)!=g:
        raise ValueError('supplied decomposition identity is false')
    # Only rational-affine injectivity is discharged here.
    affine_injective=P.degree(outer)==1
    return {'identities_checked':True,'execution_verified':False,
            'outer':list(map(str,outer)),'left_inner':list(map(str,F)),
            'right_inner':list(map(str,G)),
            'equivalence_to_inner_equality':affine_injective,
            'status':'EQUIVALENT_AFFINE_OUTER' if affine_injective else 'FORWARD_ONLY',
            'residual_obligation':None if affine_injective else
                'classify distinct outer fibres; do not cancel the outer polynomial',
            'bilu_tichy_classification':False}
