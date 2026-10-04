"""Exact power-coordinate quotients and integer lifting, with explicit domains.

Sparse polynomial expressions are parsed as arithmetic, never evaluated as
Python. Completeness of supplied outer point lists is a separate assumption.
"""
import ast
from fractions import Fraction as Q
from .core import integer_power_root
from .divisor_square import WorkLimit
from . import linear_perturbation as LP


def _q(q):
    if type(q) is not int or not 2<=q<=64:raise ValueError('power must be an integer in [2,64]')


def _sparse(p):
    if not isinstance(p,dict) or len(p)>2048:raise ValueError('bounded sparse polynomial required')
    first=next(iter(p)) if p else ()
    if not isinstance(first,tuple):raise ValueError('exponent tuples required')
    n=len(first) if p else None
    if any(not isinstance(e,tuple) or len(e)!=n or any(type(j) is not int or not 0<=j<=256 for j in e)
           or type(v) not in (int,Q) for e,v in p.items()):
        raise ValueError('nonnegative bounded exponent tuples and exact coefficients required')
    return {e:Q(v) for e,v in p.items() if v}


def parse_sparse(expression, variables):
    variables=tuple(variables)
    if not 1<=len(variables)<=8 or len(set(variables))!=len(variables) or any(not isinstance(v,str) or not v.isidentifier() for v in variables):
        raise ValueError('one to eight distinct variable names required')
    if not isinstance(expression,str) or len(expression)>100_000:raise ValueError('bounded expression required')
    tree=ast.parse(expression.strip(),mode='eval')
    if sum(1 for _ in ast.walk(tree))>12_000:raise WorkLimit('expression node budget exceeded')
    zero=(0,)*len(variables); operations=0
    def add(a,b,sign=1):
        out=dict(a)
        for e,c in b.items():out[e]=out.get(e,Q(0))+sign*c
        return _sparse(out)
    def mul(a,b):
        nonlocal operations
        operations+=len(a)*len(b)
        if operations>1_000_000:raise WorkLimit('polynomial product budget exceeded')
        out={}
        for e,c in a.items():
            for f,d in b.items():
                g=tuple(x+y for x,y in zip(e,f));out[g]=out.get(g,Q(0))+c*d
        return _sparse(out)
    def visit(node):
        if isinstance(node,ast.Constant) and type(node.value) is int:return {zero:Q(node.value)} if node.value else {}
        if isinstance(node,ast.Name) and node.id in variables:
            return {tuple(int(i==variables.index(node.id)) for i in range(len(variables))):Q(1)}
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,(ast.UAdd,ast.USub)):
            p=visit(node.operand);return p if isinstance(node.op,ast.UAdd) else {e:-c for e,c in p.items()}
        if isinstance(node,ast.BinOp):
            if isinstance(node.op,ast.Pow):
                if not isinstance(node.right,ast.Constant) or type(node.right.value) is not int or not 0<=node.right.value<=64:
                    raise ValueError('bounded nonnegative integer polynomial exponent required')
                out={zero:Q(1)};base=visit(node.left);k=node.right.value
                while k:
                    if k&1:out=mul(out,base)
                    k//=2
                    if k:base=mul(base,base)
                return out
            a,b=visit(node.left),visit(node.right)
            if isinstance(node.op,ast.Add):return add(a,b)
            if isinstance(node.op,ast.Sub):return add(a,b,-1)
            if isinstance(node.op,ast.Mult):return mul(a,b)
        raise ValueError('only integer constants, named variables, +, -, *, ** are permitted')
    return _sparse(visit(tree.body))


def power_coordinate(polynomial, coordinate, power, *, quotient=False):
    _q(power);p=_sparse(polynomial)
    if type(quotient) is not bool:raise ValueError('quotient flag must be boolean')
    if type(coordinate) is not int or coordinate<0 or (p and coordinate>=len(next(iter(p)))):
        raise ValueError('valid coordinate required')
    out={}
    for e,c in p.items():
        if quotient and e[coordinate]%power:raise ValueError('polynomial does not descend to the requested power coordinate')
        f=list(e);f[coordinate]=f[coordinate]//power if quotient else f[coordinate]*power;out[tuple(f)]=c
    return _sparse(out)


def deweight(polynomial, power_coordinate_index, scale_coordinate_index, scale_power, common_power):
    p=_sparse(polynomial)
    if any(type(v) is not int or v<0 for v in (power_coordinate_index,scale_coordinate_index,scale_power,common_power)):
        raise ValueError('nonnegative integer indices and weights required')
    if power_coordinate_index==scale_coordinate_index or (p and max(power_coordinate_index,scale_coordinate_index)>=len(next(iter(p)))):
        raise ValueError('two distinct valid coordinates required')
    out={}
    for e,c in p.items():
        f=list(e);f[scale_coordinate_index]+=scale_power*f[power_coordinate_index]-common_power
        if f[scale_coordinate_index]<0:raise ValueError('deweighting requires a Laurent polynomial; inverse coordinate excludes scale zero')
        out[tuple(f)]=c
    return _sparse(out)


def evaluate_sparse(polynomial, values):
    p=_sparse(polynomial);values=tuple(values)
    if any(type(v) not in (int,Q) for v in values) or (p and len(values)!=len(next(iter(p)))):
        raise ValueError('matching exact coordinate values required')
    result=Q(0)
    for e,c in p.items():
        for x,k in zip(values,e):c*=x**k
        result+=c
    return result


def power_composition(coefficients, power):
    _q(power);f=tuple(coefficients)
    if not f or len(f)>257 or any(type(c) is not int for c in f):raise ValueError('bounded integer polynomial required')
    while len(f)>1 and not f[-1]:f=f[:-1]
    if any(c and i%power for i,c in enumerate(f)):raise ValueError('nonzero exponents do not all descend')
    return f[::power]


def pullback_points(outer_coefficients, points, power):
    _q(power);outer=tuple(outer_coefficients)
    if not outer or len(outer)>257 or any(type(c) is not int for c in outer):raise ValueError('bounded integer polynomial required')
    def evaluate(x):
        v=0
        for c in reversed(outer):v=v*x+c
        return v
    points=tuple(tuple(p) for p in points)
    if len(points)>100_000:raise WorkLimit('supplied point budget exceeded')
    out=set(); rejected=set()
    for point in points:
        if len(point)!=2 or any(type(t) is not int for t in point):raise ValueError('integer (u,y) points required')
        u,y=point
        if y*y!=evaluate(u):raise ValueError('supplied point fails the outer equation')
        root=integer_power_root(u,power)
        if root is None:rejected.add(point);continue
        for x in ({root,-root} if power%2==0 else {root}):
            if x**power!=u or y*y!=evaluate(x**power):raise AssertionError('lift identity failed')
            out.add((x,y))
    return {'power':power,'outer_coefficients':outer,'points':sorted(out),
            'rejected_outer_points':sorted(rejected),'complete_if_outer_list_complete':True,
            'outer_completeness_verified_here':False,'execution_verified':False,
            'domain':'all integer x and y; exact power-coordinate lifting'}


def solve_power_composition(coefficients, power, *, work_limit=100_000):
    outer=power_composition(coefficients,power);m=LP.match(outer)
    if m:result=LP.solve(*m,work_limit=work_limit)
    else:
        m=LP.match_square_leading(outer)
        if not m:raise ValueError('outer quartic requires a supported nonzero perturbation')
        result=LP.solve_square_leading(*m,work_limit=work_limit)
    lifted=pullback_points(outer,result['points'],power)
    lifted.update({'complete':True,'outer_theorem':result['theorem'],
                   'outer_coordinate_bound':result['coordinate_bound'],
                   'proof_status':'exact Python transport of an existing Lean-proved outer bound; no new Lean theorem'})
    return lifted
