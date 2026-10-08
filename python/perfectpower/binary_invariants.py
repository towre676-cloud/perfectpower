"""Exact alternating-tensor contractions of binary forms over Q.

Coefficients are low-to-high in x: f[i] multiplies x^i y^(degree-i).
The degree is explicit, so a root at projective infinity is never discarded.
This is classical SL2 invariant theory, not an equivalence classifier.
"""
from fractions import Fraction as Q
from math import comb, factorial
from functools import lru_cache


def form(values, degree):
    if type(degree) is not int or not 0 <= degree <= 32:
        raise ValueError('binary degree from zero through 32 required')
    if not 1 <= len(values) <= degree + 1:
        raise ValueError('coefficients exceed homogeneous degree')
    if any(isinstance(v, (float, bool)) for v in values):
        raise ValueError('exact rational coefficients required')
    return tuple(Q(v) for v in values) + (Q(0),) * (degree + 1 - len(values))


def symmetric_tensor(values, degree):
    """Value of each symmetric component with i x-indices (binomial convention)."""
    return tuple(v / comb(degree, i) for i, v in enumerate(form(values, degree)))


def _partial(f, degree, dx, dy):
    out = [Q(0)] * (degree - dx - dy + 1)
    for i, a in enumerate(f):
        if i >= dx and degree-i >= dy:
            out[i-dx] += a * (factorial(i)//factorial(i-dx)) * (factorial(degree-i)//factorial(degree-i-dy))
    return out


def transvectant(left, m, right, n, contractions):
    """Normalized r-fold epsilon contraction; output has degree m+n-2r.

    (m-r)!(n-r)!/(m!n!) sum_j (-1)^j binom(r,j)
    d_x^(r-j)d_y^j F * d_x^j d_y^(r-j) G.
    """
    f, g = form(left, m), form(right, n)
    r = contractions
    if type(r) is not int or not 0 <= r <= min(m, n):
        raise ValueError('contraction count outside tensor degrees')
    out = [Q(0)] * (m+n-2*r+1)
    for j in range(r+1):
        a, b = _partial(f, m, r-j, j), _partial(g, n, j, r-j)
        for i, av in enumerate(a):
            for h, bv in enumerate(b):
                out[i+h] += (-1)**j * comb(r, j) * av * bv
    scale = Q(factorial(m-r)*factorial(n-r), factorial(m)*factorial(n))
    return tuple(v*scale for v in out)


@lru_cache(maxsize=1024)
def _substitution_columns(degree, entries):
    a,b,c,d = entries
    columns=[]
    for i in range(degree+1):
        out = [Q(0)] * (degree+1)
        for j in range(i+1):
            for h in range(degree-i+1):
                out[j+h] += comb(i,j)*a**j*b**(i-j)*comb(degree-i,h)*c**h*d**(degree-i-h)
        columns.append(tuple(out))
    return tuple(columns)


def binary_substitute(values, degree, matrix):
    """F(ax+by,cx+dy), without affine-degree trimming."""
    f = form(values, degree)
    if len(matrix) != 2 or any(len(row) != 2 for row in matrix):
        raise ValueError('two by two matrix required')
    if any(isinstance(v,(float,bool)) for row in matrix for v in row):
        raise ValueError('exact matrix entries required')
    entries=tuple(Q(v) for row in matrix for v in row);a,b,c,d=entries
    if not a*d-b*c:raise ValueError('nonsingular coordinate matrix required')
    columns=_substitution_columns(degree,entries)
    return tuple(sum(v*columns[i][j] for i,v in enumerate(f)) for j in range(degree+1))


def quartic_invariants(values):
    e,d,c,b,a = form(values, 4)
    I = 12*a*e-3*b*d+c*c
    J = 72*a*c*e+9*b*c*d-27*a*d*d-27*b*b*e-2*c**3
    return dict(I=I, J=J, discriminant=(4*I**3-J**2)/27,
                jacobian_ainvs=(Q(0),Q(0),Q(0),-27*I,-27*J))


def quartic_covariants(values):
    f = form(values, 4)
    h = transvectant(f, 4, f, 4, 2)
    return dict(hessian=h, jacobian=transvectant(f, 4, h, 4, 1))


def contraction_invariants(values):
    """Recover I,J through contractions rather than their coefficient formulas."""
    f = form(values, 4)
    h = transvectant(f, 4, f, 4, 2)
    return dict(I=6*transvectant(f, 4, f, 4, 4)[0],
                J=72*transvectant(f, 4, h, 4, 4)[0])


def compile_contractions(inputs, nodes):
    """Evaluate a bounded, typed epsilon-contraction DAG and serialize exact forms.

    Inputs are {coefficients, degree}; nodes are {left, right, contractions,
    scale?}. References index the concatenation of inputs and prior nodes.
    No implicit basis, polynomial factorization, or numerical eigenvectors.
    """
    if not 1<=len(inputs)<=32 or len(nodes)>256:
        raise ValueError('at most 32 inputs and 256 contraction nodes')
    forms=[(form(item['coefficients'],item['degree']),item['degree']) for item in inputs]
    for node in nodes:
        left,right=node['left'],node['right']
        if any(type(i) is not int or not 0<=i<len(forms) for i in (left,right)):
            raise ValueError('contraction references must be earlier forms')
        f,m=forms[left];g,n=forms[right];r=node['contractions']
        result=transvectant(f,m,g,n,r);degree=m+n-2*r
        if degree>32:raise ValueError('intermediate binary degree exceeds 32')
        scale=form([node.get('scale',1)],0)[0]
        forms.append((tuple(scale*v for v in result),degree))
    return dict(schema='pp-binary-contraction-dag/1',
                forms=[dict(degree=n,coefficients=[str(v) for v in f]) for f,n in forms])


def cubic_discriminant(values):
    """Degree-three discriminant from two successive alternating contractions."""
    h=transvectant(values,3,values,3,2)
    return Q(27,2)*transvectant(h,2,h,2,2)[0]
