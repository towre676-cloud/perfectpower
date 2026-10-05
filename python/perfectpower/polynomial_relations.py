"""Two-sided polynomial equations and whole-query finite projection.

Completing a quadratic square, or recognizing an exact polynomial power,
transports a complete superelliptic solve back through integer witness fibres.
Affine sides have exact filtered generators. General residual curves remain.
"""
from dataclasses import dataclass
from . import polyalg as P
from .core import rigid_certificate
from .residue_cover import integer_polynomial, evaluate
from .polynomial_composition import PolynomialCompiler, verify_compiled
from .sturm_fibres import root_certificate, verify_roots
from .divisor_square import WorkLimit
import json


def _presentations(side, other):
    if len(side)==3:
        c,b,a=side
        transformed=list(4*a*v for v in other); transformed[0]+=b*b-4*a*c
        yield {'kind':'quadratic','degree':2,'witness':[b,2*a],
               'scale':4*a,'offset':b*b-4*a*c,'transformed':transformed}
    n=len(side)-1
    for d in range(2,n+1):
        if n%d: continue
        cert=rigid_certificate(side,d)
        if cert is not None and cert.exact_identity:
            if any(c%cert.denominator for c in cert.root_numerators): continue
            witness=[c//cert.denominator for c in cert.root_numerators]
            yield {'kind':'exact_power','degree':d,'witness':witness,
                   'scale':1,'offset':0,'transformed':list(other)}


def solve_relation(left, right, *, work_limit=100000, algebra_limit=2000000):
    """All integer pairs with left(x)=right(y), for supported finite leaves.

    Unlike a pure power interface, an arbitrary quadratic may occupy either
    side. Complete lists retain every nonlinear witness fibre and both signs.
    """
    left=integer_polynomial(left);right=integer_polynomial(right)
    if len(left)<2 or len(right)<2: raise ValueError('two nonconstant integer polynomials required')
    base={'schema':'pp-polynomial-relation/1','left':left,'right':right,
          'domain':'all integer x and y','execution_verified':False}
    for side,other,swapped in ((right,left,False),(left,right,True)):
        if len(side)==2:
            c,b=side
            return {**base,'status':'GENERATOR','points':None,
                    'generator':{'free_coordinate':'y' if swapped else 'x',
                                 'dependent_coordinate':'x' if swapped else 'y',
                                 'numerator':(other[0]-c,)+other[1:],'denominator':b,
                                 'admissibility':'denominator divides numerator at the free coordinate'},
                    'proof':{'kind':'affine','swapped':swapped}}
    from .polynomial_charts import parameterize_relation
    try:
        charts=parameterize_relation(left,right,node_limit=work_limit,algebra_limit=algebra_limit)
        if charts['complete']:
            if any(c[n]['kind']=='fibre' for c in charts['charts'] for n in ('x','y')):
                from .polynomial_images import refine_charts
                try:refined=refine_charts(charts,work_limit=work_limit)
                except WorkLimit:refined={'complete':False}
                if refined['complete']:
                    return {**base,'status':'COMPLETE','points':refined['points'],
                            'proof':{'kind':'chart_refinement','refinement':refined}}
            return {**base,'status':charts['status'],'points':charts['points'],
                    'generator':{'kind':'polynomial_charts','charts':charts['charts']},
                    'proof':{'kind':'polynomial_charts','parameterization':charts}}
    except WorkLimit:
        pass
    compiler=PolynomialCompiler(work_limit=work_limit,algebra_limit=algebra_limit);attempts=[]
    for side,other,swapped in ((right,left,False),(left,right,True)):
        for presentation in _presentations(side,other):
            power=compiler.solve(presentation['transformed'],presentation['degree'])
            if power['status']!='COMPLETE':
                attempts.append({'swapped':swapped,'kind':presentation['kind'],'degree':presentation['degree'],'reason':'power equation not complete finite'});continue
            witness=integer_polynomial(presentation['witness']);fibres=[];points=set();used=0
            try:
                for v in sorted({v for u,v in power['points']}):
                    if used>=work_limit:raise WorkLimit('two-sided polynomial fibres exceed node budget')
                    cert=root_certificate((witness[0]-v,)+witness[1:],node_limit=work_limit-used)
                    used+=cert['nodes_checked'];fibres.append({'value':v,'certificate':cert})
                    for u,w in power['points']:
                        if w==v:
                            points.update((y,u) if swapped else (u,y) for y in cert['roots'])
            except WorkLimit as error:
                attempts.append({'swapped':swapped,'reason':str(error)});continue
            if any(evaluate(left,x)!=evaluate(right,y) for x,y in points):raise AssertionError('two-sided lift fails original equation')
            return {**base,'status':'COMPLETE','points':sorted(points),
                    'proof':{'kind':'power_transport','swapped':swapped,'presentation':presentation,
                             'power_result':power,'fibres':fibres},'fibre_nodes':used}
    return {**base,'status':'UNRESOLVED','points':None,'attempts':attempts,
            'reason':'no supported complete finite polynomial presentation'}


def verify_relation(result,*,work_limit=100000):
    try:
        if result['schema']!='pp-polynomial-relation/1' or result['domain']!='all integer x and y' or result['execution_verified'] is not False:return False
        left=integer_polynomial(result['left']);right=integer_polynomial(result['right']);proof=result['proof']
        if proof['kind']=='chart_refinement':
            from .polynomial_images import verify_refinement
            r=proof['refinement'];same=lambda a,b:json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)
            return result['status']=='COMPLETE' and same(r['generator']['left'],left) and same(r['generator']['right'],right) and verify_refinement(r,work_limit=work_limit) and same(result['points'],r['points'])
        if proof['kind']=='polynomial_charts':
            from .polynomial_charts import verify_parameterization
            charts=proof['parameterization']
            same=lambda a,b:json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)
            return (same(charts['left'],left) and same(charts['right'],right)
                    and verify_parameterization(charts,node_limit=work_limit)
                    and result['status']==charts['status'] and same(result['points'],charts['points'])
                    and same(result['generator'],{'kind':'polynomial_charts','charts':charts['charts']}))
        swapped=proof['swapped']
        if type(swapped) is not bool or len(left)<2 or len(right)<2:return False
        side,other=(left,right) if swapped else (right,left)
        if proof['kind']=='affine':
            if len(side)!=2 or result['status']!='GENERATOR' or result['points'] is not None:return False
            expected=solve_relation(left,right,work_limit=work_limit)
            return json.dumps(expected,sort_keys=True)==json.dumps(result,sort_keys=True)
        if proof['kind']!='power_transport' or result['status']!='COMPLETE':return False
        presentation=proof['presentation'];d=presentation['degree'];scale=presentation['scale'];offset=presentation['offset']
        if type(d) is not int or not 2<=d<=64 or type(scale) is not int or not scale or type(offset) is not int:return False
        witness=integer_polynomial(presentation['witness'])
        expected=list(scale*c for c in side);expected[0]+=offset
        if P.power(P.poly(witness),d)!=P.poly(expected):return False
        transformed=list(scale*c for c in other);transformed[0]+=offset
        if tuple(presentation['transformed'])!=tuple(transformed):return False
        power=proof['power_result']
        if power['status']!='COMPLETE' or power['degree']!=d or tuple(power['coefficients'])!=tuple(transformed) or not verify_compiled(power,work_limit=work_limit):return False
        if [r['value'] for r in proof['fibres']]!=sorted({v for u,v in power['points']}):return False
        points=set();used=0
        for fibre in proof['fibres']:
            v=fibre['value'];cert=fibre['certificate']
            if tuple(cert['coefficients'])!=(witness[0]-v,)+witness[1:] or cert['domain']!=[None,None]:return False
            if used>=work_limit or not verify_roots(cert,node_limit=work_limit-used):return False
            used+=cert['nodes_checked']
            for u,w in power['points']:
                if w==v:points.update((y,u) if swapped else (u,y) for y in cert['roots'])
        return json.dumps(sorted(points))==json.dumps(result['points']) and used==result['fibre_nodes']
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


@dataclass
class PolynomialProjection:
    smt:str
    eliminated_symbols:tuple
    remaining_symbols:tuple
    points:tuple
    solution:dict


def project_polynomial_query(script,*,branch_limit=128,work_limit=100000):
    from .integer_projection import _parse_integer_query
    from .finite_formula import _poly
    from .smt_adapter import _padd
    from .finite_projection import _substitute,_simplify,_render
    from .industrial_router import route_lia
    if type(branch_limit) is not int or branch_limit<1:raise ValueError('positive branch budget required')
    names,atoms=_parse_integer_query(script)
    for atom in atoms:
        if not isinstance(atom,list) or len(atom)!=3 or atom[0]!='=':continue
        try:polynomial=_padd(_poly(atom[1],names),_poly(atom[2],names),-1)
        except ValueError:continue
        variables=sorted({v for m in polynomial for v,e in m})
        if len(variables)!=2 or any(len(m)>1 for m in polynomial):continue
        x,y=variables
        dx=max(e for m in polynomial for v,e in m if v==x)
        dy=max(e for m in polynomial for v,e in m if v==y)
        left=[polynomial.get((),0)]+[polynomial.get(((x,i),),0) for i in range(1,dx+1)]
        right=[0]+[-polynomial.get(((y,i),),0) for i in range(1,dy+1)]
        result=solve_relation(left,right,work_limit=work_limit)
        if result['status']!='COMPLETE':continue
        points=tuple(tuple(p) for p in result['points'])
        if len(points)>branch_limit:raise WorkLimit('complete polynomial relation exceeds branch budget')
        remaining=tuple(n for n in names if n not in (x,y));branches=[]
        for a,b in points:
            bindings={x:a,y:b}
            branches.append(_simplify(['and']+[_substitute(p,bindings) for p in atoms if p is not atom]))
        assertion=_simplify(['or']+branches)
        out='\n'.join(['(set-logic QF_NIA)']+[f'(declare-const {n} Int)' for n in remaining]+[f'(assert {_render(assertion)})','(check-sat)'])+'\n'
        out,_=route_lia(out)
        return PolynomialProjection(out,(x,y),remaining,points,result)
    raise ValueError('no complete finite polynomial relation recognized')
