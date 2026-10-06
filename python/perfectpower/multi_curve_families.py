"""Several exact deformation parameters, replayed reductions and flatness."""
from copy import deepcopy
from fractions import Fraction as Q
from .parameter_functions import ParameterFunction as PF, fraction_free_system
from .rational_functions import AlgebraBudget, solve_many, determinant
from .curve_families import encode_matrix
from . import field_polynomials as F
from .projective_deformation import quotient


class MultiCurveFamily:
    def __init__(self,specification):
        if not isinstance(specification,dict) or not {'parameters','coefficients'}<=set(specification) or set(specification)-{'parameters','coefficients','work_limit','degree_limit','bit_limit'}:raise ValueError('parameters, coefficients and optional algebra budgets required')
        names=specification['parameters']
        if not isinstance(names,list) or not 1<=len(names)<=3 or len(set(names))!=len(names) or any(not isinstance(n,str) or not n.isidentifier() or len(n)>32 for n in names):raise ValueError('one through three distinct parameter names required')
        raw=specification['coefficients']
        if not isinstance(raw,list) or len(raw) not in (4,6,8):raise ValueError('monic x degree 3, 5 or 7 required')
        self.specification=deepcopy(specification);self.parameters=tuple(names)
        self.limits={k:specification[k] for k in ('work_limit','degree_limit','bit_limit') if k in specification}
        budget=AlgebraBudget(**self.limits);self.f=[PF.parse(names,a,budget) for a in raw]
        if self.f[-1]!=1:raise ValueError('monic x polynomial required')
        m=len(self.f)-1;self.genus=(m-1)//2;self.dimension=m-1;zero=self.f[0].coerce(0);dx=F.derivative(self.f)
        sylvester=[]
        for k in range(m-1):sylvester.append([zero]*k+list(reversed(self.f))+[zero]*(m-2-k))
        for k in range(m):sylvester.append([zero]*k+list(reversed(dx))+[zero]*(m-1-k))
        dense=lambda matrix:sum(bool(v) for row in matrix for v in row)>3*len(matrix)
        self.discriminant=(-1)**(m*(m-1)//2)*(fraction_free_system(sylvester)[0] if dense(sylvester) else determinant(sylvester))
        if not self.discriminant:raise ValueError('generically singular family')
        size=2*m-1;pad=lambda a:list(a)+[zero]*(size-len(a))
        columns=[pad([zero]*j+self.f) for j in range(m-1)]
        for k in range(m):
            r=[zero]*k+[zero.coerce(1)]
            columns.append(pad(F.add(F.product(F.derivative(r),self.f),F.scale(F.product(r,dx),-Q(1,2)))))
        targets=[]
        for name in names:
            dt=[a.derivative(name) for a in self.f]
            targets.extend(pad([zero]*i+[-a/2 for a in dt]) for i in range(m-1))
        matrix=list(map(list,zip(*columns)));rhs=list(map(list,zip(*targets)))
        solution=fraction_free_system(matrix,rhs)[1] if dense(matrix) else solve_many(matrix,rhs)
        if solution is None:raise AssertionError('smooth multiparameter reduction failed')
        rows=list(map(list,zip(*solution)));self.connections={};self.reductions={}
        for k,name in enumerate(names):
            self.connections[name]=[row[:m-1] for row in rows[k*(m-1):(k+1)*(m-1)]]
            self.reductions[name]=[row[m-1:] for row in rows[k*(m-1):(k+1)*(m-1)]]
            for i,(b,r) in enumerate(zip(self.connections[name],self.reductions[name])):
                replay=F.add(F.product(b,self.f),F.add(F.product(F.derivative(r),self.f),F.scale(F.product(r,dx),-Q(1,2))))
                if pad(replay)!=targets[k*(m-1)+i]:raise AssertionError('multivariate reduction replay failed')
        flatness=[]
        for i,name in enumerate(names):
            for other in names[i+1:]:
                a,b=self.connections[name],self.connections[other];ab,ba=F.matrix_product(a,b),F.matrix_product(b,a)
                curvature=[[a[r][c].derivative(other)-b[r][c].derivative(name)+ab[r][c]-ba[r][c] for c in range(m-1)] for r in range(m-1)]
                if any(v for row in curvature for v in row):raise AssertionError('Gauss-Manin curvature is nonzero')
                flatness.append(dict(parameters=[name,other],curvature=encode_matrix(curvature),zero=True))
        self.packet=dict(schema='pp-multi-curve-family/1',parameters=names,genus=self.genus,state_dimension=self.dimension,
            discriminant=self.discriminant.packet(),connections={n:encode_matrix(a) for n,a in self.connections.items()},
            reductions={n:encode_matrix(a) for n,a in self.reductions.items()},flatness=flatness,
            exact_reduction_identities_checked=len(names)*(m-1),algebra_work=budget.work,execution_verified=False,
            scope='exact iterated rational-function field and simultaneous flat de Rham connections for monic odd-degree smooth families; no numerical multi-parameter transport or new kernel proof')

    def summary(self):return dict(parameters=list(self.parameters),genus=self.genus,state_dimension=self.dimension,flatness_pairs=len(self.packet['flatness']))
    def evidence(self):return deepcopy(self.packet)
    def specialize(self,parameters):
        d=self.discriminant.evaluate(parameters)
        if not d:raise ValueError('singular parameter fibre')
        return dict(discriminant=d,coefficients=[a.evaluate(parameters) for a in self.f],connections={n:[[a.evaluate(parameters) for a in row] for row in matrix] for n,matrix in self.connections.items()})
    def projective_deformation(self,parameter):
        if parameter not in self.parameters:raise ValueError('unknown deformation parameter')
        budget=AlgebraBudget(**self.limits);f=[a.with_budget(budget) for a in self.f]
        return quotient(f,[a.derivative(parameter) for a in f],len(f))
    def deformation(self):
        budget=AlgebraBudget(**self.limits);f=[a.with_budget(budget) for a in self.f]
        packets={};tangents=[]
        for name in self.parameters:
            packet,tangent=quotient(f,[a.derivative(name) for a in f],len(f),with_tangent=True)
            packets[name]=packet;tangents.append(tangent)
        return dict(parameters=list(self.parameters),projective_quotient_dimension=len(f)-3,
            essential_parameter_rank=F.matrix_rank(tangents),essential_tangents=encode_matrix(tangents),
            directions=packets,scope='generic rank of simultaneous parameter motion in the full projective tangent quotient; no global moduli injectivity asserted')
    def root_motion(self,parameter):
        if parameter not in self.parameters:raise ValueError('unknown deformation parameter')
        budget=AlgebraBudget(**self.limits);f=[a.with_budget(budget) for a in self.f]
        dx=F.derivative(f);dt=[a.derivative(parameter) for a in f];inverse=F.polynomial_inverse(dx,f)
        velocity=F.divide(F.scale(F.product(dt,inverse),-1),f)[1]
        q,r=F.divide(F.add(dt,F.product(dx,velocity)),f)
        if any(r):raise AssertionError('partial root motion replay failed')
        return dict(parameter=parameter,velocity=[a.packet() for a in velocity],identity_quotient=[a.packet() for a in q],identity_checked=True)
    def observable(self,parameter,coefficients=None):
        if parameter not in self.parameters:raise ValueError('unknown deformation parameter')
        budget=AlgebraBudget(**self.limits)
        row=[PF.parse(self.parameters,c,budget) for c in (coefficients if coefficients is not None else [1]+[0]*(self.dimension-1))]
        if len(row)!=self.dimension:raise ValueError('one observable coefficient per basis form')
        rows=[];a=[[v.with_budget(budget) for v in r] for r in self.connections[parameter]];zero=PF(self.parameters,budget=budget)
        while True:
            decoder=solve_many(list(map(list,zip(*rows))),[[v] for v in row]) if rows else ([] if not any(row) else None)
            if decoder is not None:break
            rows.append(row)
            if len(rows)>self.dimension:raise AssertionError('observable closure failed')
            row=[v.derivative(parameter)+sum((rows[-1][k]*a[k][j] for k in range(self.dimension)),zero) for j,v in enumerate(rows[-1])]
        return dict(parameter=parameter,order=len(rows),monic_operator=[v.packet() for v in [-r[0] for r in decoder]+[zero.coerce(1)]],derivative_rows=encode_matrix(rows),minimal_universal_order=True,
            scope='directional scalar operator over all parameters; other parameters are held fixed, not independent commuting scalar equations')
