"""Complete signed power-curve charts with explicit integer coordinate images.

Recognize A(x)^p+k=B(y)^q+k, reduce p,q by their gcd, and retain every sign.
Affine coordinates give exact semilinear parameter images. Nonlinear ones
give complete per-parameter integer fibres, without claiming a periodic image.
"""
from fractions import Fraction as Q
from math import gcd
import json
from . import polyalg as P
from .residue_cover import integer_polynomial,evaluate
from .core import integer_power_root
from .polynomial_composition import _AlgebraBudget
from .semilinear_domains import semilinear_domain,verify_domain,contains
from .sturm_fibres import root_certificate,verify_roots
from .divisor_square import WorkLimit


def power_presentations(coefficients,*,algebra_limit=2000000):
    """All integral proper power-root presentations with constant residual."""
    f=integer_polynomial(coefficients);n=len(f)-1;budget=_AlgebraBudget(algebra_limit);found=[]
    for p in range(n,1,-1):
        if n%p:continue
        lead=integer_power_root(f[-1],p)
        if lead is None:continue
        m=n//p;root=[Q(0)]*m+[Q(lead)]
        for j in range(1,m+1):
            current=budget.power(P.poly(root),p);index=n-j
            known=current[index] if index<len(current) else Q(0)
            root[m-j]=(Q(f[index])-known)/(p*lead**(p-1));budget.check(root)
        if any(c.denominator!=1 for c in root):continue
        coordinate=integer_polynomial(int(c) for c in root)
        residual=P.subtract(P.poly(f),budget.power(P.poly(coordinate),p))
        if len(residual)==1:found.append({'power':p,'coordinate':coordinate,'offset':int(residual[0])})
    return found


def _coordinate(root,sign,power):
    target=[0]*power+[sign]
    if len(root)==2:
        b,a=root;numerator=[-b]+[0]*(power-1)+[sign]
        if a<0:numerator=[-c for c in numerator]
        return {'kind':'polynomial','numerator':numerator,'denominator':abs(a)}
    return {'kind':'fibre','coordinate':list(root),'target':target}


def _predicate(chart,index):
    atoms=[{'poly':[-(0 if index==0 else 1),1],'relation':'>='}]
    for name in ('x','y'):
        c=chart[name]
        if c['kind']=='polynomial':atoms.append({'poly':c['numerator'],'modulus':c['denominator'],'relation':'=','value':0})
    return {'op':'and','args':atoms}


def parameterize_relation(left,right,*,algebra_limit=2000000,period_limit=65536,node_limit=100000):
    left=integer_polynomial(left);right=integer_polynomial(right)
    if len(left)<3 or len(right)<3:raise ValueError('two nonlinear polynomial sides required')
    base={'schema':'pp-polynomial-charts/1','left':left,'right':right,'domain':'all integer x and y','execution_verified':False}
    lp=power_presentations(left,algebra_limit=algebra_limit);rp=power_presentations(right,algebra_limit=algebra_limit)
    pairs=[(a,b) for a in lp for b in rp if a['offset']==b['offset']]
    if not pairs:
        from .coefficient_charts import parameterize_coefficients
        return parameterize_coefficients(left,right,algebra_limit=algebra_limit,period_limit=period_limit,node_limit=node_limit)
    # Prefer explicit affine coordinates, then the strongest exponent reduction.
    a,b=min(pairs,key=lambda pair:(len(pair[0]['coordinate'])+len(pair[1]['coordinate']),-pair[0]['power']-pair[1]['power']))
    p,q=a['power'],b['power'];g=gcd(p,q);px,py=q//g,p//g;charts=[];used=0
    for sx in (1,-1):
        for sy in (1,-1):
            if sx**p!=sy**q:continue
            chart={'signs':[sx,sy],'x':_coordinate(a['coordinate'],sx,px),'y':_coordinate(b['coordinate'],sy,py)}
            chart['predicate']=_predicate(chart,len(charts))
            if used>=node_limit:raise WorkLimit('shared parameter-domain node budget exceeded')
            domain=semilinear_domain(chart['predicate'],node_limit=node_limit-used,period_limit=period_limit)
            used+=domain['root_nodes'];chart['parameter_domain']=domain;charts.append(chart)
    explicit=all(c['x']['kind']==c['y']['kind']=='polynomial' for c in charts)
    empty=all(c['parameter_domain']['cardinality']==0 for c in charts)
    return {**base,'status':'COMPLETE' if empty else 'GENERATOR','points':[] if empty else None,
            'complete':True,'left_presentation':a,'right_presentation':b,'gcd':g,'charts':charts,
            'image_scope':'complete semilinear parameter images' if explicit else 'complete integer fibres per parameter; nonlinear image not classified',
            'root_nodes':used}


def verify_parameterization(result,*,node_limit=100000,period_limit=65536):
    """Replay chosen identities and sign charts; do not discover presentations."""
    try:
        if result.get('schema')=='pp-coefficient-polynomial-charts/1':
            from .coefficient_charts import verify_coefficient_parameterization
            return verify_coefficient_parameterization(result,node_limit=node_limit,period_limit=period_limit)
        if result['schema']!='pp-polynomial-charts/1' or result['complete'] is not True or result['execution_verified'] is not False or result['domain']!='all integer x and y':return False
        a,b=result['left_presentation'],result['right_presentation'];left=integer_polynomial(result['left']);right=integer_polynomial(result['right'])
        for f,r in ((left,a),(right,b)):
            root=integer_polynomial(r['coordinate']);p=r['power'];offset=r['offset']
            if type(p) is not int or not 2<=p<=64 or len(root)<2 or type(offset) is not int:return False
            rebuilt=list(P.power(P.poly(root),p));rebuilt[0]+=offset
            if P.poly(rebuilt)!=P.poly(f):return False
        if a['offset']!=b['offset']:return False
        p,q=a['power'],b['power'];g=gcd(p,q)
        if result['gcd']!=g:return False
        signs=[[sx,sy] for sx in (1,-1) for sy in (1,-1) if sx**p==sy**q]
        if [c['signs'] for c in result['charts']]!=signs:return False
        same=lambda a,b:json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True);used=0
        for i,c in enumerate(result['charts']):
            if not same(c['x'],_coordinate(a['coordinate'],c['signs'][0],q//g)) or not same(c['y'],_coordinate(b['coordinate'],c['signs'][1],p//g)):return False
            if not same(c['predicate'],_predicate(c,i)) or not same(c['parameter_domain']['predicate'],c['predicate']):return False
            if used>=node_limit or not verify_domain(c['parameter_domain'],node_limit=node_limit-used,period_limit=period_limit):return False
            used+=c['parameter_domain']['root_nodes']
        explicit=all(c['x']['kind']==c['y']['kind']=='polynomial' for c in result['charts'])
        empty=all(c['parameter_domain']['cardinality']==0 for c in result['charts'])
        scope='complete semilinear parameter images' if explicit else 'complete integer fibres per parameter; nonlinear image not classified'
        return result['status']==('COMPLETE' if empty else 'GENERATOR') and same(result['points'],[] if empty else None) and used==result['root_nodes'] and result['image_scope']==scope
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


def chart_points(chart,t,*,node_limit=100000,image_index=None):
    """Every original pair in one chart at t; exact complete nonlinear fibres."""
    if type(t) is not int or abs(t).bit_length()>16384:raise ValueError('bounded integer parameter required')
    if not contains(chart['parameter_domain'],t):return {'parameter':t,'points':[],'fibres':[],'root_nodes':0,'complete':True,'execution_verified':False}
    values=[];fibres=[];used=0
    for name in ('x','y'):
        c=chart[name]
        if c['kind']=='polynomial':
            value=evaluate(c['numerator'],t);den=c['denominator']
            if value%den:raise AssertionError('parameter violates certified integer image')
            values.append([value//den])
        else:
            target=evaluate(c['target'],t);f=list(c['coordinate']);f[0]-=target
            if used>=node_limit:raise WorkLimit('shared nonlinear fibre budget exceeded')
            cert=(image_index.fibre(f,node_limit=node_limit-used) if image_index is not None else root_certificate(f,node_limit=node_limit-used));used+=cert['nodes_checked']
            fibres.append({'coordinate':name,'target':target,'certificate':cert});values.append(cert['roots'])
    return {'parameter':t,'points':sorted((x,y) for x in values[0] for y in values[1]),'fibres':fibres,'root_nodes':used,'complete':True,'execution_verified':False}


def evaluate_parameterization(result,t,*,node_limit=100000,image_index=None):
    points=set();rows=[];used=0
    if result.get('complete') is not True:raise ValueError('complete chart generator required')
    for i,chart in enumerate(result['charts']):
        if used>=node_limit:raise WorkLimit('shared parameter evaluation root budget exceeded')
        row=chart_points(chart,t,node_limit=node_limit-used,image_index=image_index);used+=row['root_nodes'];rows.append({'chart':i,**row});points.update(row['points'])
    if any(evaluate(result['left'],x)!=evaluate(result['right'],y) for x,y in points):raise AssertionError('chart point violates original relation')
    return {'schema':'pp-chart-evaluation/1','parameter':t,'points':sorted(points),'charts':rows,'root_nodes':used,'complete':True,'execution_verified':False}


def checked_chart_points(chart,row,t,*,node_limit=100000):
    """Replay one supplied evaluation without discovering fibre roots."""
    if row['parameter']!=t or row['complete'] is not True or row['execution_verified'] is not False:raise ValueError('invalid chart evaluation header')
    values=[];used=0;fibres=iter(row['fibres'])
    if not contains(chart['parameter_domain'],t):points=[]
    else:
        for name in ('x','y'):
            c=chart[name]
            if c['kind']=='polynomial':
                n=evaluate(c['numerator'],t);d=c['denominator']
                if n%d:raise ValueError('invalid integer coordinate image')
                values.append([n//d])
            else:
                fibre=next(fibres);target=evaluate(c['target'],t);f=list(c['coordinate']);f[0]-=target;cert=fibre['certificate']
                if fibre['coordinate']!=name or fibre['target']!=target or tuple(cert['coefficients'])!=tuple(f) or cert['domain']!=[None,None]:raise ValueError('invalid coordinate fibre')
                if used>=node_limit or not verify_roots(cert,node_limit=node_limit-used):raise ValueError('invalid complete root transcript')
                used+=cert['nodes_checked'];values.append(cert['roots'])
        points=sorted((x,y) for x in values[0] for y in values[1])
    if next(fibres,None) is not None or json.dumps(points)!=json.dumps(row['points']) or used!=row['root_nodes']:raise ValueError('inconsistent chart points')
    return points,used


def verify_evaluation(generator,result,*,node_limit=100000):
    try:
        if not verify_parameterization(generator,node_limit=node_limit) or result['schema']!='pp-chart-evaluation/1' or result['complete'] is not True or result['execution_verified'] is not False:return False
        t=result['parameter'];used=0;points=set()
        if type(t) is not int or [r['chart'] for r in result['charts']]!=list(range(len(generator['charts']))):return False
        for chart,row in zip(generator['charts'],result['charts']):
            values,nodes=checked_chart_points(chart,row,t,node_limit=node_limit-used);used+=nodes;points.update(values)
        return json.dumps(sorted(points))==json.dumps(result['points']) and used==result['root_nodes']
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,StopIteration):return False
