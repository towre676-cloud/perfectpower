"""Exact determinant-weighted basis events without basis enumeration.

For cyclotomic incidence B, L=B* W B and T=W B L^-1 B*.
Principal minors give inclusion probabilities; signed mixed minors give
joint include/exclude events. No square-root weights or floating arithmetic.
This is classical determinantal probability applied to the recovered graphs.
"""
from fractions import Fraction as Q
from .connection_polytope import ConnectionGraph,algebra_determinant
from .divisor_square import WorkLimit


def _multiply(a,b,field):
    zero=field.element(0)
    return [[sum((x*y for x,y in zip(row,column)),zero) for column in zip(*b)] for row in a]


def _inverse(matrix,field):
    n=len(matrix);zero=field.element(0);one=field.element(1)
    a=[list(row)+[one if i==j else zero for j in range(n)] for i,row in enumerate(matrix)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]!=zero),None)
        if pivot is None:raise ValueError('singular connection metric')
        a[j],a[pivot]=a[pivot],a[j];inv=a[j][j].inverse();a[j]=[x*inv for x in a[j]]
        for i in range(n):
            if i!=j and a[i][j]!=zero:
                c=a[i][j];a[i]=[x-c*y for x,y in zip(a[i],a[j])]
    return [row[n:] for row in a]


def _encode(value):return [str(x) for x in value.coefficients]
def _matrix_encode(matrix):return [[_encode(x) for x in row] for row in matrix]


def _decode(values,field):
    if not isinstance(values,(list,tuple)) or not values or any(type(v) not in (str,int,Q) for v in values):raise ValueError('exact field coefficients required')
    return field.element([Q(v) for v in values])


class ConnectionMeasure:
    def __init__(self,graph,weights=None,*,work_limit=2000000):
        if not isinstance(graph,ConnectionGraph):raise ValueError('ConnectionGraph required')
        if type(work_limit) is not int or work_limit<1:raise ValueError('positive algebra work budget required')
        n,m=graph.vertices,len(graph.edges)
        # Apply a dense matrix-shape work estimate before discovery. Rational
        # coefficient growth and field degree have additional costs.
        if m>256 or n**3+2*m*n*n+m*m*n>work_limit:raise WorkLimit('connection inverse/kernel work exceeds budget')
        self.graph=graph;self.weights=graph.weights(weights);self.field=graph.field;self.work_limit=work_limit
        self.support=graph.support([i for i,w in enumerate(self.weights) if w])
        self.b=graph.incidence();self.l=graph.laplacian(self.weights)
        self.z=algebra_determinant(self.l,self.field);self.inverse=None;self.kernel=None
        if self.support['rank']<n:
            if self.z!=self.field.element(0):raise AssertionError('support and determinant disagree')
            return
        self.inverse=_inverse(self.l,self.field)
        adjoint=[[graph.conjugate(row[j]) for row in self.b] for j in range(n)]
        weighted=[[x*w for x in row] for w,row in zip(self.weights,self.b)]
        self.kernel=_multiply(_multiply(weighted,self.inverse,self.field),adjoint,self.field)
        self._verify_projection()

    def _verify_projection(self):
        n=self.graph.vertices;field=self.field;zero=field.element(0)
        # T=W B L^-1 B*. Check the small inverse identity instead of T^2
        # as an m^3 dense multiplication; the displayed factorization proves it.
        identity=_multiply(self.l,self.inverse,field)
        if any(identity[i][j]!=field.element(i==j) for i in range(n) for j in range(n)):raise AssertionError('inverse identity failed')
        if sum((self.kernel[i][i] for i in range(len(self.kernel))),zero)!=field.element(n):raise AssertionError('basis-size identity failed')

    @classmethod
    def from_receipt(cls,receipt,*,work_limit=2000000):
        """Reuse a checked supplied inverse; do not discover an inverse again."""
        if not verify_measure(receipt,work_limit=work_limit):raise ValueError('invalid connection measure certificate')
        self=cls.__new__(cls);self.graph=ConnectionGraph(receipt['vertices'],tuple(receipt['edges']),receipt['power'])
        self.field=self.graph.field;self.weights=self.graph.weights(receipt['weights']);self.work_limit=work_limit
        self.support=receipt['positive_support'];self.b=self.graph.incidence();self.l=self.graph.laplacian(self.weights)
        self.z=_decode(receipt['normalizing_determinant'],self.field)
        self.inverse=None if receipt['laplacian_inverse'] is None else [[_decode(x,self.field) for x in row] for row in receipt['laplacian_inverse']]
        self.kernel=None if receipt['transfer_kernel'] is None else [[_decode(x,self.field) for x in row] for row in receipt['transfer_kernel']]
        return self

    def _indices(self,values):
        values=tuple(values)
        if len(set(values))!=len(values) or any(type(i) is not int or not 0<=i<len(self.graph.edges) for i in values):raise ValueError('distinct valid edge indices required')
        return values

    def event(self,included=(),excluded=()):
        """Exact probability of all specified inclusion/exclusion decisions."""
        included=self._indices(included);excluded=self._indices(excluded)
        if set(included)&set(excluded):raise ValueError('contradictory edge decisions')
        if self.kernel is None:raise ValueError('basis distribution undefined on rank-deficient positive support')
        indices=included+excluded;k=len(indices)
        if k**3>self.work_limit:raise WorkLimit('event determinant exceeds work budget')
        zero=self.field.element(0);one=self.field.element(1)
        matrix=[[self.kernel[i][j]-(one if row==col and row>=len(included) else zero)
            for col,j in enumerate(indices)] for row,i in enumerate(indices)]
        return algebra_determinant(matrix,self.field)*((-1)**len(excluded))

    def conditional(self,included=(),excluded=()):
        included=self._indices(included);excluded=self._indices(excluded);p=self.event(included,excluded)
        if p==self.field.element(0):raise ValueError('conditioning event has zero probability')
        inv=p.inverse();one=self.field.element(1);zero=self.field.element(0)
        marginals=[one if i in included else zero if i in excluded else self.event(included+(i,),excluded)*inv for i in range(len(self.graph.edges))]
        return {'included':list(included),'excluded':list(excluded),'event_probability':_encode(p),
            'edge_marginals':[_encode(x) for x in marginals]}

    def receipt(self):
        return {'vertices':self.graph.vertices,'edges':self.graph.edges,'power':self.graph.power,
            'weights':[str(w) for w in self.weights],'status':'EXACT_BASIS_MEASURE' if self.kernel is not None else 'RANK_DEFICIENT',
            'positive_support':self.support,'normalizing_determinant':_encode(self.z),
            'laplacian_inverse':None if self.inverse is None else _matrix_encode(self.inverse),
            'transfer_kernel':None if self.kernel is None else _matrix_encode(self.kernel),
            'edge_marginals':None if self.kernel is None else [_encode(self.kernel[i][i]) for i in range(len(self.kernel))],
            'basis_enumerations':0,'execution_verified':False,'scope':'exact determinant-weighted graph bases; not probabilities of integer solutions'}


def verify_measure(receipt,*,work_limit=2000000):
    """Check supplied inverse and factorized kernel, without basis enumeration."""
    try:
        if receipt['execution_verified'] is not False or receipt['basis_enumerations']!=0:return False
        graph=ConnectionGraph(receipt['vertices'],tuple(receipt['edges']),receipt['power']);field=graph.field
        weights=graph.weights(receipt['weights']);n=graph.vertices;m=len(graph.edges)
        if type(work_limit) is not int or work_limit<1 or m>256 or n**3+2*m*n*n+m*m*n>work_limit:return False
        support=graph.support([i for i,w in enumerate(weights) if w]);l=graph.laplacian(weights);z=algebra_determinant(l,field)
        if support!=receipt['positive_support'] or z!=_decode(receipt['normalizing_determinant'],field):return False
        if support['rank']<n:return receipt['status']=='RANK_DEFICIENT' and all(receipt[k] is None for k in ('laplacian_inverse','transfer_kernel','edge_marginals'))
        if receipt['status']!='EXACT_BASIS_MEASURE':return False
        inv=[[_decode(x,field) for x in row] for row in receipt['laplacian_inverse']]
        if len(inv)!=n or any(len(row)!=n for row in inv):return False
        identity=_multiply(l,inv,field)
        if any(identity[i][j]!=field.element(i==j) for i in range(n) for j in range(n)):return False
        b=graph.incidence();adjoint=[[graph.conjugate(row[j]) for row in b] for j in range(n)]
        kernel=_multiply(_multiply([[x*w for x in row] for w,row in zip(weights,b)],inv,field),adjoint,field)
        return _matrix_encode(kernel)==receipt['transfer_kernel'] and [_encode(kernel[i][i]) for i in range(m)]==receipt['edge_marginals'] and sum((kernel[i][i] for i in range(m)),field.element(0))==field.element(n)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,OverflowError):return False


def verify_conditioning(receipt,conditioning,*,work_limit=2000000):
    try:
        measure=ConnectionMeasure.from_receipt(receipt,work_limit=work_limit)
        return measure.conditional(conditioning['included'],conditioning['excluded'])==conditioning
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False
