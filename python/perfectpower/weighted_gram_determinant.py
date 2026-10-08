"""Exact unordered weighted Cauchy--Binet over Gaussian rationals.

One size-n row subset contributes once. Complex weights, zero weights,
rank-deficient matrices and rectangular supports are permitted.
"""
from fractions import Fraction
from itertools import combinations
from math import comb
from .residue_atlas import _canonical_equal

ZERO=(Fraction(0),Fraction(0));ONE=(Fraction(1),Fraction(0))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def star(a):return (a[0],-a[1])
def div(a,b):
    q=b[0]*b[0]+b[1]*b[1]
    if not q:raise ZeroDivisionError('Gaussian divisor zero')
    c=mul(a,star(b));return (c[0]/q,c[1]/q)
def encode(a):return [str(a[0]),str(a[1])]
def parse(a):
    pair=a if isinstance(a,list) and len(a)==2 else [a,0]
    values=[]
    for v in pair:
        if type(v) not in (int,str) or (isinstance(v,str) and (len(v)>150 or any(c not in '+-0123456789/ ' for c in v))):
            raise ValueError('exact rational scalar or [real,imaginary] required')
        try:q=Fraction(v)
        except (ValueError,ZeroDivisionError):raise ValueError('invalid rational literal') from None
        if max(q.numerator.bit_length(),q.denominator.bit_length())>256:raise ValueError('256-bit rational required')
        values.append(q)
    return tuple(values)
def determinant(a):
    b=[list(row) for row in a];n=len(b);result=ONE
    for k in range(n):
        pivot=next((i for i in range(k,n) if b[i][k]!=ZERO),None)
        if pivot is None:return ZERO
        if pivot!=k:b[k],b[pivot]=b[pivot],b[k];result=neg(result)
        p=b[k][k];result=mul(result,p)
        for i in range(k+1,n):
            q=div(b[i][k],p)
            for j in range(k+1,n):b[i][j]=add(b[i][j],neg(mul(q,b[k][j])))
    return result

def weighted_determinant(matrix,weights,*,columns=None):
    if not isinstance(matrix,list) or len(matrix)>16:raise ValueError('at most sixteen matrix rows required')
    n=len(matrix[0]) if matrix else columns
    if type(n) is not int or not 0<=n<=8:raise ValueError('zero through eight columns required; empty rows need columns')
    if any(not isinstance(r,list) or len(r)!=n for r in matrix):raise ValueError('rectangular matrix required')
    if not isinstance(weights,list) or len(weights)!=len(matrix):raise ValueError('one weight per row required')
    if comb(len(matrix),n)>2048:raise ValueError('complete unordered subset budget exceeded')
    B=[[parse(v) for v in r] for r in matrix];w=[parse(v) for v in weights]
    gram=[[ZERO for _ in range(n)] for _ in range(n)]
    for i,row in enumerate(B):
        for a in range(n):
            for b in range(n):gram[a][b]=add(gram[a][b],mul(mul(star(row[a]),w[i]),row[b]))
    terms=[];total=ZERO
    for subset in combinations(range(len(B)),n):
        minor=determinant([B[i] for i in subset]);weight=ONE
        for i in subset:weight=mul(weight,w[i])
        contribution=mul(mul(weight,star(minor)),minor);total=add(total,contribution)
        terms.append({'rows':list(subset),'minor':encode(minor),'weight_product':encode(weight),'contribution':encode(contribution)})
    value=determinant(gram)
    if total!=value:raise ArithmeticError('exact unordered identity mismatch')
    nonnegative=all(z[1]==0 and z[0]>=0 for z in w)
    supported=[r['rows'] for r in terms if parse(r['weight_product'])!=ZERO and parse(r['minor'])!=ZERO]
    return {'schema':'pp-weighted-gram-determinant/1','matrix':[[encode(v) for v in r] for r in B],
      'weights':[encode(v) for v in w],'columns':n,'gram':[[encode(v) for v in r] for r in gram],
      'terms':terms,'subset_count':len(terms),'determinant':encode(value),'unordered_sum':encode(total),
      'nonnegative_real_weights':nonnegative,'nonzero_supported_minors':supported,
      'positive_determinant':nonnegative and value[0]>0,'execution_verified':False}

def verify_weighted_determinant(packet):
    try:
        return _canonical_equal(packet,weighted_determinant(packet['matrix'],packet['weights'],columns=packet['columns']))
    except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OverflowError):return False
