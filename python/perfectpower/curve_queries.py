"""Complete counting and polynomial optimization on explicit power-curve charts.

Polynomial side conditions and coordinate congruences are substituted as exact
rational polynomials, with positive denominator clearing and integer images.
No finite box is scanned. Nonlinear inverse-coordinate images stay unresolved.
"""
from copy import deepcopy
from fractions import Fraction as Q
import json
from . import polyalg as P
from .polynomial_symmetry import parse_sparse
from .polynomial_composition import _AlgebraBudget
from .polynomial_charts import parameterize_relation,verify_parameterization,chart_points
from .semilinear_domains import (semilinear_domain,optimize_semilinear,
    verify_domain,verify_optimization,select)
from .residue_cover import integer_polynomial
from .polynomial_domains import _holds
from .divisor_square import WorkLimit


def _coordinates(chart):
    return {n:P.poly(Q(c,chart[n]['denominator']) for c in chart[n]['numerator']) for n in ('x','y')}


def _expression(expression,coordinates,budget):
    sparse=parse_sparse(expression,('x','y'));out=P.ZERO
    for exponents,c in sparse.items():
        if sum(e*P.degree(coordinates[n]) for n,e in zip(('x','y'),exponents))>64:
            raise WorkLimit('substituted polynomial exceeds degree 64')
        term=P.poly([c])
        for n,e in zip(('x','y'),exponents):term=budget.mul(term,budget.power(coordinates[n],e))
        out=budget.check(P.add(out,term))
    return out


def _clear(polynomial):
    denominator=P.common_denominator(polynomial)
    if denominator.bit_length()>16384:raise WorkLimit('rational objective denominator bit budget exceeded')
    return list(integer_polynomial(int(c*denominator) for c in polynomial)),denominator


def substitute_predicate(predicate,coordinates,budget):
    nodes=atoms=0
    def walk(node,depth=0):
        nonlocal nodes,atoms
        nodes+=1
        if nodes>2048 or depth>64:raise WorkLimit('curve predicate node budget exceeded')
        if type(node) is bool:return node
        if not isinstance(node,dict):raise ValueError('structured curve predicate required')
        if 'expr' in node:
            atoms+=1
            if atoms>120:raise WorkLimit('curve predicate atom budget exceeded')
            modular='modulus' in node;fields={'expr','relation','modulus','value'} if modular else {'expr','relation'}
            if set(node)!=fields or node['relation'] not in ('=','!=','<','<=','>','>='):raise ValueError('polynomial expression comparison required')
            numerator,denominator=_clear(_expression(node['expr'],coordinates,budget))
            out={'poly':numerator,'relation':node['relation']}
            if modular:
                m,v=node['modulus'],node['value']
                if type(m) is not int or m<1 or type(v) is not int:raise ValueError('positive modulus and integer threshold required')
                out.update(modulus=denominator*m,value=denominator*v)
            return out
        op,args=node.get('op'),node.get('args')
        if set(node)!={'op','args'} or op not in ('and','or','not') or not isinstance(args,(list,tuple)) or op=='not' and len(args)!=1:
            raise ValueError('Boolean curve predicate required')
        return {'op':op,'args':[walk(a,depth+1) for a in args]}
    return walk(predicate)


def _materialize(generator,rows,point_limit):
    total=sum(r['domain']['cardinality'] or 0 for r in rows)
    if any(r['domain']['cardinality'] is None for r in rows) or total>point_limit:return None
    points=[]
    for row in rows:
        c=generator['charts'][row['chart']]
        for rank in range(row['domain']['cardinality']):points.extend(chart_points(c,select(row['domain'],rank))['points'])
    if len(set(points))!=total:raise AssertionError('canonical charts failed disjoint point counting')
    return sorted(points)


def _answer(generator,rows,sense,point_limit):
    count=None if any(r['domain']['cardinality'] is None for r in rows) else sum(r['domain']['cardinality'] for r in rows)
    answer={'solution_count':count,'points':_materialize(generator,rows,point_limit),'optimization':None}
    if not rows or rows[0]['optimum'] is None:return answer
    if any(r['optimum']['status']=='UNBOUNDED' for r in rows):
        answer['optimization']={'status':'UNBOUNDED','value':None,'optimizer_count':0,'optimizer_points':[],'optimizer_charts':[]};return answer
    available=[r for r in rows if r['optimum']['status']=='OPTIMAL']
    if not available:
        answer['optimization']={'status':'EMPTY','value':None,'optimizer_count':0,'optimizer_points':[],'optimizer_charts':[]};return answer
    values=[Q(r['optimum']['value'],r['objective_denominator']) for r in available]
    value=(min if sense=='min' else max)(values);winners=[r for r,v in zip(available,values) if v==value]
    charts=[];optimizer_count=0;points=[];infinite=False
    for r in winners:
        opt=r['optimum'];c=generator['charts'][r['chart']]
        if opt['points'] is None:
            domain=opt['optimizer_domain'];n=domain['cardinality']
            charts.append({'chart':r['chart'],'parameters':{'kind':'domain','domain':domain}})
            if n is None:infinite=True
            else:
                optimizer_count+=n
                if optimizer_count<=point_limit:
                    for rank in range(n):points.extend(chart_points(c,select(domain,rank))['points'])
        else:
            optimizer_count+=len(opt['points']);charts.append({'chart':r['chart'],'parameters':{'kind':'points','values':opt['points']}})
            if optimizer_count<=point_limit:
                for t in opt['points']:points.extend(chart_points(c,t)['points'])
    answer['optimization']={'status':'OPTIMAL','value':str(value),'optimizer_count':None if infinite else optimizer_count,
                            'optimizer_points':None if infinite or optimizer_count>point_limit else sorted(points),'optimizer_charts':charts}
    return answer


def _finite_answer(refinement,predicate,objective,sense,point_limit,algebra_limit):
    budget=_AlgebraBudget(algebra_limit);points=[];values=[]
    def truth(node):
        if type(node) is bool:return node
        if 'poly' in node:
            value=node['poly'][0];target=0
            if 'modulus' in node:value%=node['modulus'];target=node['value']
            return _holds(value-target,node['relation'])
        args=[truth(a) for a in node['args']]
        return all(args) if node['op']=='and' else any(args) if node['op']=='or' else not args[0]
    for x,y in refinement['points']:
        coordinates={'x':P.poly([x]),'y':P.poly([y])}
        if not truth(substitute_predicate(predicate,coordinates,budget)):continue
        points.append((x,y))
        if objective is not None:values.append((_expression(objective,coordinates,budget)[0],(x,y)))
    answer={'solution_count':len(points),'points':points if len(points)<=point_limit else None,'optimization':None}
    if objective is not None:
        value=(min if sense=='min' else max)(v for v,p in values) if values else None
        winners=[p for v,p in values if v==value]
        answer['optimization']={'status':'OPTIMAL' if values else 'EMPTY','value':str(value) if value is not None else None,
                                'optimizer_count':len(winners),'optimizer_points':winners if len(winners)<=point_limit else None}
    return answer


def query_curve(left,right,predicate=True,*,objective=None,sense='min',point_limit=128,
                node_limit=100000,period_limit=65536,work_limit=1000000,algebra_limit=2000000):
    """All original pairs, exact count and global polynomial optimum/all ties.

    Predicate atoms use {expr: polynomial in x,y, relation: comparison to 0},
    or add modulus and value to compare expr mod modulus with value.
    Constant objectives can return infinite optimizer charts.
    """
    if sense not in ('min','max') or type(point_limit) is not int or point_limit<0:raise ValueError('sense and nonnegative point budget required')
    generator=parameterize_relation(left,right,node_limit=node_limit,period_limit=period_limit,algebra_limit=algebra_limit)
    return _query_prepared_curve(generator,predicate,objective=objective,sense=sense,point_limit=point_limit,
                                 node_limit=node_limit,period_limit=period_limit,work_limit=work_limit,algebra_limit=algebra_limit)


def _query_prepared_curve(generator,predicate=True,*,objective=None,sense='min',point_limit=128,
                          node_limit=100000,period_limit=65536,work_limit=1000000,algebra_limit=2000000):
    if sense not in ('min','max') or type(point_limit) is not int or point_limit<0:raise ValueError('sense and nonnegative point budget required')
    if generator.get('root_nodes',0)>node_limit:raise WorkLimit('prepared generator exceeds query root budget')
    base={'schema':'pp-polynomial-curve-query/1','generator':generator,'predicate':deepcopy(predicate),
          'objective':objective,'sense':sense,'point_limit':point_limit,'execution_verified':False}
    if not generator['complete']:return {**base,'status':'UNRESOLVED','complete':False,'reason':generator['reason']}
    if any(c[n]['kind']!='polynomial' for c in generator['charts'] for n in ('x','y')):
        from .polynomial_images import refine_charts
        refinement=refine_charts(generator,work_limit=node_limit)
        if refinement['complete']:
            return {**base,'schema':'pp-finite-curve-query/1','status':'COMPLETE','complete':True,'refinement':refinement,
                    **_finite_answer(refinement,predicate,objective,sense,point_limit,algebra_limit)}
        return {**base,'status':'UNRESOLVED','complete':False,'reason':'complete fibre generator available, but nonlinear parameter image not classified for this query'}
    rows=[];used=generator['root_nodes'];budget=_AlgebraBudget(algebra_limit)
    for i,c in enumerate(generator['charts']):
        coordinates=_coordinates(c);translated=substitute_predicate(predicate,coordinates,budget)
        condition={'op':'and','args':[c['predicate'],translated]}
        if used>=node_limit:raise WorkLimit('shared curve-query root budget exceeded')
        if objective is None:
            numerator=denominator=None;optimum=None
            domain=semilinear_domain(condition,node_limit=node_limit-used,period_limit=period_limit,work_limit=work_limit)
            used+=domain['root_nodes']
        else:
            numerator,denominator=_clear(_expression(objective,coordinates,budget))
            optimum=optimize_semilinear(condition,numerator,sense=sense,node_limit=node_limit-used,period_limit=period_limit,work_limit=work_limit)
            domain=optimum['feasible_domain'];used+=optimum['root_nodes']
        rows.append({'chart':i,'predicate':condition,'domain':domain,'objective_numerator':numerator,'objective_denominator':denominator,'optimum':optimum})
    return {**base,'status':'COMPLETE','complete':True,'charts':rows,'root_nodes':used,'algebra_work':budget.used,
            **_answer(generator,rows,sense,point_limit)}


def verify_curve_query(result,*,node_limit=100000,period_limit=65536,work_limit=1000000,algebra_limit=2000000):
    try:
        same=lambda a,b:json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)
        if result['schema']=='pp-finite-curve-query/1':
            from .polynomial_images import verify_refinement
            if result['status']!='COMPLETE' or result['complete'] is not True or result['execution_verified'] is not False or result['sense'] not in ('min','max') or type(result['point_limit']) is not int or result['point_limit']<0:return False
            if not same(result['generator'],result['refinement']['generator']) or not verify_refinement(result['refinement'],work_limit=node_limit):return False
            answer=_finite_answer(result['refinement'],result['predicate'],result['objective'],result['sense'],result['point_limit'],algebra_limit)
            return all(same(result[k],v) for k,v in answer.items())
        if result['schema']!='pp-polynomial-curve-query/1' or result['status']!='COMPLETE' or result['complete'] is not True or result['execution_verified'] is not False:return False
        generator=result['generator'];sense=result['sense'];limit=result['point_limit']
        if sense not in ('min','max') or type(limit) is not int or limit<0 or not verify_parameterization(generator,node_limit=node_limit,period_limit=period_limit):return False
        if any(c[n]['kind']!='polynomial' for c in generator['charts'] for n in ('x','y')):return False
        rows=result['charts'];used=generator['root_nodes'];budget=_AlgebraBudget(algebra_limit)
        if [r['chart'] for r in rows]!=list(range(len(generator['charts']))):return False
        for r,c in zip(rows,generator['charts']):
            coordinates=_coordinates(c);condition={'op':'and','args':[c['predicate'],substitute_predicate(result['predicate'],coordinates,budget)]}
            if not same(condition,r['predicate']) or not same(condition,r['domain']['predicate']) or used>=node_limit:return False
            if result['objective'] is None:
                if any(r[k] is not None for k in ('objective_numerator','objective_denominator','optimum')):return False
                if not verify_domain(r['domain'],node_limit=node_limit-used,period_limit=period_limit,work_limit=work_limit):return False
                used+=r['domain']['root_nodes']
            else:
                numerator,denominator=_clear(_expression(result['objective'],coordinates,budget));opt=r['optimum']
                if not same(numerator,r['objective_numerator']) or denominator!=r['objective_denominator'] or not same(opt['objective'],numerator) or opt['sense']!=sense or not same(opt['feasible_domain'],r['domain']):return False
                if not verify_optimization(opt,node_limit=node_limit-used,period_limit=period_limit,work_limit=work_limit):return False
                used+=opt['root_nodes']
        expected=_answer(generator,rows,sense,limit)
        return used==result['root_nodes'] and budget.used==result['algebra_work'] and all(same(result[k],v) for k,v in expected.items())
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False
