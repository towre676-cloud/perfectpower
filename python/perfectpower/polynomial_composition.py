"""Automatic exact polynomial coordinates and complete integer pullbacks.

For each proper degree divisor, a normalized approximate root supplies the
unique monic zero-constant candidate right component. Exact substitution
accepts a decomposition; it never cancels a shared nonlinear outer map.
Classical characteristic-zero decomposition, with explicit work budgets.
"""
from copy import deepcopy
from fractions import Fraction as Q
from math import gcd, lcm
import json
from . import polyalg as P
from .decomposition import compose
from .residue_cover import integer_polynomial, evaluate
from .divisor_square import WorkLimit
from .sturm_fibres import root_certificate, verify_roots
from .core import integer_power_root


class _AlgebraBudget:
    def __init__(self, limit):
        if type(limit) is not int or limit < 1: raise ValueError('positive algebra work budget required')
        self.limit=limit; self.used=0
    def spend(self, count=1):
        self.used += count
        if self.used > self.limit: raise WorkLimit('polynomial decomposition algebra budget exceeded')
    def check(self, polynomial):
        for c in polynomial:
            if max(abs(c.numerator).bit_length(),c.denominator.bit_length()) > 16384:
                raise WorkLimit('decomposition intermediate coefficient bit budget exceeded')
        return polynomial
    def mul(self,a,b):
        self.spend(len(a)*len(b))
        return self.check(P.mul(a,b))
    def power(self,a,k):
        out=P.ONE
        while k:
            if k&1: out=self.mul(out,a)
            k >>= 1
            if k: a=self.mul(a,a)
        return out


def discover_decompositions(coefficients, *, algebra_limit=2000000):
    """Discover all proper right-component degrees over Q, modulo affine maps.

    Inner components are returned as primitive integer polynomials with zero
    constant term and positive leading coefficient. Rational outer coefficients
    are retained exactly. The degree-64 and coefficient budgets are inherited.
    """
    f=integer_polynomial(coefficients); n=len(f)-1; budget=_AlgebraBudget(algebra_limit)
    if n < 4: return {'coefficients':f,'decompositions':[],'tested_degrees':[], 'algebra_work':0, 'complete':True}
    monic=P.monic(P.poly(f)); found=[]; tested=[]
    for m in range(2,n):
        if n%m: continue
        tested.append(m); k=n//m; inner=[Q(0)]*m+[Q(1)]
        # Degrees N-1 through N-m+1 cannot receive lower outer terms.
        for j in range(1,m):
            current=budget.power(P.poly(inner),k)
            known=current[n-j] if n-j<len(current) else Q(0)
            inner[m-j]=(monic[n-j]-known)/k
            budget.check(inner)
        inner=P.poly(inner); powers=[P.ONE]
        for j in range(k): powers.append(budget.mul(powers[-1],inner))
        remainder=P.poly(f); outer=[Q(0)]*(k+1)
        for j in range(k,-1,-1):
            index=m*j
            coefficient=remainder[index] if index<len(remainder) else Q(0)
            outer[j]=coefficient
            remainder=P.subtract(remainder,P.scale(powers[j],coefficient))
            budget.check(remainder)
        if not P.is_zero(remainder): continue
        denominator=lcm(*(c.denominator for c in inner))
        ints=[int(c*denominator) for c in inner]; content=0
        for c in ints: content=gcd(content,abs(c))
        coordinate=integer_polynomial(c//content for c in ints)
        scale=Q(denominator,content)
        outer=P.poly(c/scale**j for j,c in enumerate(outer))
        if compose(outer,coordinate)!=P.poly(f): raise AssertionError('decomposition identity failed')
        found.append({'inner_degree':m,'outer_degree':k,'inner':coordinate,
                      'outer':[str(c) for c in outer]})
    return {'coefficients':f,'decompositions':found,'tested_degrees':tested,
            'algebra_work':budget.used,'complete':True,
            'scope':'all rational proper right-component degrees, modulo affine normalization',
            'execution_verified':False}


def verify_decomposition(coefficients, decomposition):
    """Identity replay suffices for using a supplied decomposition."""
    try:
        f=integer_polynomial(coefficients); inner=integer_polynomial(decomposition['inner'])
        outer=P.poly(Q(c) for c in decomposition['outer'])
        return (len(inner)>2 and len(outer)>2 and inner[0]==0 and inner[-1]>0
                and len(inner)-1==decomposition['inner_degree']
                and len(outer)-1==decomposition['outer_degree']
                and compose(outer,inner)==P.poly(f))
    except (ValueError,TypeError,KeyError,ArithmeticError): return False


def _mordell_result(f,d):
    if d!=2 or len(f)!=4: return None
    from .compiler import match_affine_cube,mordell_complete
    affine=match_affine_cube(f)
    if affine is None: return None
    a,b,k=affine; known=mordell_complete(k)
    if known is None: return None
    table,theorems=known; points=set()
    for u,roots in table.items():
        if (u-b)%a: continue
        points.update(((u-b)//a,v) for root in roots for v in {root,-root})
    return {'coefficients':f,'degree':d,'domain':'all integer x and y',
            'status':'COMPLETE','points':sorted(points),'execution_verified':False,
            'proof':{'kind':'mordell_registry','affine':[a,b,k],
                     'theorems':theorems,'outer_points':sorted((u,v) for u,roots in table.items() for r in roots for v in {r,-r})}}


class PolynomialCompiler:
    """Shared finite leaves with automatically discovered nonlinear fibres."""
    def __init__(self, *, work_limit=100000, algebra_limit=2000000, engine=None):
        from .arithmetic_engine import ArithmeticEngine
        self.work_limit=work_limit; self.algebra_limit=algebra_limit
        if any(type(n) is not int or n<1 for n in (work_limit,algebra_limit)): raise ValueError('positive budgets required')
        self.engine=engine or ArithmeticEngine(work_limit=work_limit)

    def solve(self,coefficients,degree=2,*,strict=False):
        f=integer_polynomial(coefficients)
        if type(degree) is not int or not 2<=degree<=64: raise ValueError('integer power in [2,64] required')
        self._fibre_used=0; self._algebra_used=0
        result=self._node(f,degree)
        if strict and result['status']=='UNRESOLVED': raise WorkLimit(result['reason'])
        return result

    def _node(self,f,d):
        base={'coefficients':f,'degree':d,'domain':'all integer x and y','execution_verified':False}
        try: direct=self.engine.solve(f,d,decomposition=False)
        except WorkLimit: direct=None
        if direct is not None and direct['status'] in ('COMPLETE','GENERATOR'): return direct
        known=_mordell_result(f,d)
        if known is not None: return known
        attempts=[]
        content=0
        for c in f: content=gcd(content,abs(c))
        content_root=integer_power_root(content,d)
        if content_root is not None and content_root>1:
            before=self._fibre_used
            child=self._node(tuple(c//content for c in f),d)
            if child['status'] in ('COMPLETE','GENERATOR'):
                if child['status']=='GENERATOR':
                    return {**base,'status':'GENERATOR','points':None,
                            'generator':{'kind':'scaled_witness','scale':content_root,'source':child['generator']},
                            'proof':{'kind':'content_power','root':content_root,'outer_result':child}}
                return {**base,'status':'COMPLETE',
                        'points':sorted((x,content_root*y) for x,y in child['points']),
                        'proof':{'kind':'content_power','root':content_root,'outer_result':child}}
            self._fibre_used=before
        try:
            remaining=self.algebra_limit-self._algebra_used
            if remaining<1: raise WorkLimit('shared polynomial algebra budget exhausted')
            discovered=discover_decompositions(f,algebra_limit=remaining)
            self._algebra_used+=discovered['algebra_work']
        except WorkLimit as error:
            return {**base,'status':'UNRESOLVED','points':None,'reason':str(error)}
        for reduction in discovered['decompositions']:
            outer=P.poly(Q(c) for c in reduction['outer'])
            scale=lcm(*(c.denominator for c in outer))
            leaf=integer_polynomial(int(c*scale**d) for c in outer)
            before=self._fibre_used
            child=self._node(leaf,d)
            if child['status']=='GENERATOR':
                return {**base,'status':'GENERATOR','points':None,
                        'generator':{'kind':'polynomial_pullback','inner':list(reduction['inner']),
                                     'witness_scale':scale,'outer':child['generator']},
                        'proof':{'kind':'polynomial_composition','decomposition':reduction,
                                 'witness_scale':scale,'outer_result':child,'fibres':[]}}
            if child['status']!='COMPLETE':
                self._fibre_used=before; attempts.append({'inner_degree':reduction['inner_degree'],'reason':'outer equation is not complete finite'}); continue
            inner=tuple(reduction['inner']); fibres=[]; points=set()
            values=sorted({u for u,v in child['points'] if v%scale==0})
            try:
                for u in values:
                    remaining=self.work_limit-self._fibre_used
                    if remaining<1: raise WorkLimit('shared complete fibre budget exhausted')
                    cert=root_certificate((inner[0]-u,)+inner[1:],node_limit=remaining)
                    self._fibre_used+=cert['nodes_checked']; fibres.append({'value':u,'certificate':cert})
                    ys={v//scale for cu,v in child['points'] if cu==u and v%scale==0}
                    points.update((x,y) for x in cert['roots'] for y in ys)
            except WorkLimit as error:
                self._fibre_used=before; attempts.append({'inner_degree':reduction['inner_degree'],'reason':str(error)}); continue
            if any(y**d!=evaluate(f,x) for x,y in points): raise AssertionError('polynomial pullback failed original equation')
            return {**base,'status':'COMPLETE','points':sorted(points),
                    'proof':{'kind':'polynomial_composition','decomposition':reduction,
                             'witness_scale':scale,'outer_result':child,'fibres':fibres},
                    'statistics':{'original_degree':len(f)-1,'outer_degree':len(leaf)-1,
                                  'fibre_nodes':self._fibre_used,'algebra_work':self._algebra_used}}
        return {**base,'status':'UNRESOLVED','points':None,'attempts':attempts,
                'reason':'no supported complete finite equation along discovered polynomial coordinates'}


def verify_compiled(result,*,work_limit=100000):
    """Replay the accepted path; decomposition discovery is not repeated."""
    from .arithmetic_engine import verify_result
    used=0
    def walk(node):
        nonlocal used
        if node['domain']!='all integer x and y' or node['execution_verified'] is not False: return False
        f=integer_polynomial(node['coefficients']); d=node['degree']
        if type(d) is not int or not 2<=d<=64: return False
        kind=node['proof']['kind']
        if kind=='mordell_registry':
            rebuilt=_mordell_result(f,d)
            return rebuilt is not None and json.dumps(rebuilt,sort_keys=True)==json.dumps(node,sort_keys=True)
        if kind=='content_power':
            root=node['proof']['root']; child=node['proof']['outer_result']
            if type(root) is not int or root<=1 or child['status'] not in ('COMPLETE','GENERATOR') or child['degree']!=d:return False
            if tuple(root**d*c for c in child['coefficients'])!=f or not walk(child):return False
            if child['status']=='GENERATOR':
                return node['status']=='GENERATOR' and node['points'] is None and json.dumps(node['generator'],sort_keys=True)==json.dumps({'kind':'scaled_witness','scale':root,'source':child['generator']},sort_keys=True)
            return node['status']=='COMPLETE' and json.dumps(sorted((x,root*y) for x,y in child['points']))==json.dumps(node['points'])
        if kind!='polynomial_composition': return verify_result(node,work_limit=work_limit)
        if node['status'] not in ('COMPLETE','GENERATOR'): return False
        proof=node['proof']; reduction=proof['decomposition']
        if not verify_decomposition(f,reduction): return False
        outer=P.poly(Q(c) for c in reduction['outer']); scale=proof['witness_scale']
        if type(scale) is not int or scale<1: return False
        scaled=P.scale(outer,scale**d)
        if any(c.denominator!=1 for c in scaled): return False
        child=proof['outer_result']
        if child['degree']!=d or tuple(child['coefficients'])!=tuple(map(int,scaled)) or child['status'] not in ('COMPLETE','GENERATOR') or not walk(child): return False
        if child['status']=='GENERATOR':
            expected={'kind':'polynomial_pullback','inner':list(reduction['inner']),'witness_scale':scale,'outer':child['generator']}
            return node['status']=='GENERATOR' and node['points'] is None and proof['fibres']==[] and json.dumps(node['generator'],sort_keys=True)==json.dumps(expected,sort_keys=True)
        if node['status']!='COMPLETE':return False
        inner=tuple(reduction['inner']); values=sorted({u for u,v in child['points'] if v%scale==0}); points=set()
        if [r['value'] for r in proof['fibres']]!=values: return False
        for fibre in proof['fibres']:
            u=fibre['value']; cert=fibre['certificate']
            if tuple(cert['coefficients'])!=(inner[0]-u,)+inner[1:] or cert['domain']!=[None,None]: return False
            if used>=work_limit or not verify_roots(cert,node_limit=work_limit-used): return False
            used+=cert['nodes_checked']
            ys={v//scale for cu,v in child['points'] if cu==u and v%scale==0}
            points.update((x,y) for x in cert['roots'] for y in ys)
        return json.dumps(sorted(points))==json.dumps(node['points'])
    try: return walk(result)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError): return False
