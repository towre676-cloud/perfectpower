"""Finite sign-domain search and finite-image refinement of power charts.

Negative-leading even-degree inputs have a finite nonnegative-value domain.
Nonlinear chart coordinates can inherit complete finite parameter restrictions
from smaller separated-polynomial relations. Every branch must close.
"""
from .polynomial_domains import integer_domain,verify_domain
from .polynomial_charts import chart_points,checked_chart_points,verify_parameterization
from .semilinear_domains import contains
from .residue_cover import integer_polynomial,residue_cover,verify_cover,scan_cover
from .factored_sieve import adaptive_cover
from .divisor_square import WorkLimit
import json


def sign_domain_solve(coefficients,degree=2,*,work_limit=100000):
    f=integer_polynomial(coefficients)
    if type(degree) is not int or not 2<=degree<=64:raise ValueError('power exponent 2..64 required')
    if degree%2 or len(f)<3 or (len(f)-1)%2 or f[-1]>=0:raise ValueError('negative leading even-degree polynomial and even power required')
    domain=integer_domain({'poly':list(f),'relation':'>='},node_limit=work_limit)
    if domain['cardinality'] is None:raise AssertionError('finite sign domain expected')
    initial=residue_cover(f,degree);scans=[];points=set();used=0
    for lo,hi in domain['intervals']:
        if used>=work_limit:raise WorkLimit('shared sign-domain candidate budget exhausted')
        cover=adaptive_cover(initial,lo,hi);scan=scan_cover(cover,lo,hi,work_limit=work_limit-used)
        used+=scan['candidates_checked'];scans.append({'cover':cover,**scan});points.update(scan['points'])
    return {'coefficients':f,'degree':degree,'domain':'all integer x and y','status':'COMPLETE','points':sorted(points),
            'execution_verified':False,'proof':{'kind':'finite_sign_domain','domain':domain,'scans':scans},
            'statistics':{'nonnegative_arguments':domain['cardinality'],'candidates_checked':used,'root_nodes':domain['root_nodes']}}


def verify_sign_solve(result,*,work_limit=100000):
    try:
        same=lambda a,b:json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)
        f=integer_polynomial(result['coefficients']);d=result['degree'];proof=result['proof'];domain=proof['domain']
        if result['status']!='COMPLETE' or result['domain']!='all integer x and y' or result['execution_verified'] is not False or proof['kind']!='finite_sign_domain':return False
        if type(d) is not int or not 2<=d<=64 or d%2 or len(f)<3 or (len(f)-1)%2 or f[-1]>=0 or not same(domain['predicate'],{'poly':list(f),'relation':'>='}) or not verify_domain(domain,node_limit=work_limit):return False
        if domain['cardinality'] is None or [r['interval'] for r in proof['scans']]!=domain['intervals']:return False
        points=set();used=0
        for row in proof['scans']:
            cover=row['cover'];lo,hi=row['interval']
            if tuple(cover['coefficients'])!=f or cover['degree']!=d or not verify_cover(cover) or used>=work_limit:return False
            scan=scan_cover(cover,lo,hi,work_limit=work_limit-used);used+=scan['candidates_checked'];points.update(scan['points'])
            if any(not same(row[k],v) for k,v in scan.items()):return False
        expected={'nonnegative_arguments':domain['cardinality'],'candidates_checked':used,'root_nodes':domain['root_nodes']}
        return same(result['points'],sorted(points)) and same(result['statistics'],expected)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


def refine_charts(generator,*,work_limit=100000):
    """Close a whole fibre generator only when every chart image is finite."""
    from .polynomial_relations import solve_relation
    if not generator['complete']:raise ValueError('complete chart generator required')
    rows=[];points=set();used=0
    for i,chart in enumerate(generator['charts']):
        domain=chart['parameter_domain']
        if domain['cardinality']==0:
            rows.append({'chart':i,'coordinate':None,'restriction':None,'parameters':[],'evaluations':[]});continue
        if chart.get('zero_chart'):
            if domain['cardinality']!=1 or not contains(domain,0):raise ValueError('invalid canonical zero chart')
            if used>=work_limit:raise WorkLimit('shared zero-fibre node budget exceeded')
            evaluation=chart_points(chart,0,node_limit=work_limit-used)
            used+=evaluation['root_nodes'];points.update(evaluation['points'])
            rows.append({'chart':i,'coordinate':'zero_chart','restriction':None,'parameters':[0],'evaluations':[evaluation]})
            continue
        restriction=None;coordinate=None
        for name in ('x','y'):
            c=chart[name]
            if c['kind']!='fibre':continue
            solved=solve_relation(c['coordinate'],c['target'],work_limit=work_limit)
            if solved['status']=='COMPLETE':restriction=solved;coordinate=name;break
        if restriction is None:
            return {'schema':'pp-polynomial-chart-refinement/1','generator':generator,'status':'UNRESOLVED','complete':False,
                    'points':None,'closed_charts':rows,'reason':'at least one nonlinear parameter image remains unclassified','execution_verified':False}
        parameters=sorted({t for x,t in restriction['points'] if contains(domain,t)});evaluations=[]
        for t in parameters:
            if used>=work_limit:raise WorkLimit('shared finite-image fibre budget exceeded')
            row=chart_points(chart,t,node_limit=work_limit-used);used+=row['root_nodes'];evaluations.append(row);points.update(row['points'])
        rows.append({'chart':i,'coordinate':coordinate,'restriction':restriction,'parameters':parameters,'evaluations':evaluations})
    return {'schema':'pp-polynomial-chart-refinement/1','generator':generator,'status':'COMPLETE','complete':True,
            'points':sorted(points),'charts':rows,'root_nodes':used,'execution_verified':False}


def verify_refinement(result,*,work_limit=100000):
    from .polynomial_relations import verify_relation
    try:
        same=lambda a,b:json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)
        generator=result['generator']
        if result['schema']!='pp-polynomial-chart-refinement/1' or result['status']!='COMPLETE' or result['complete'] is not True or result['execution_verified'] is not False or not verify_parameterization(generator,node_limit=work_limit):return False
        if [r['chart'] for r in result['charts']]!=list(range(len(generator['charts']))):return False
        points=set();used=0
        for chart,row in zip(generator['charts'],result['charts']):
            domain=chart['parameter_domain'];name=row['coordinate'];restriction=row['restriction']
            if name is None:
                if domain['cardinality']!=0 or restriction is not None or row['parameters']!=[] or row['evaluations']!=[]:return False
                continue
            if name=='zero_chart':
                if chart.get('zero_chart') is not True or domain['cardinality']!=1 or not contains(domain,0) or restriction is not None or row['parameters']!=[0] or len(row['evaluations'])!=1:return False
                values,nodes=checked_chart_points(chart,row['evaluations'][0],0,node_limit=work_limit-used)
                used+=nodes;points.update(values);continue
            if name not in ('x','y') or chart[name]['kind']!='fibre':return False
            c=chart[name]
            if not same(restriction['left'],c['coordinate']) or not same(restriction['right'],c['target']) or restriction['status']!='COMPLETE' or not verify_relation(restriction,work_limit=work_limit):return False
            parameters=sorted({t for x,t in restriction['points'] if contains(domain,t)})
            if row['parameters']!=parameters or [r['parameter'] for r in row['evaluations']]!=parameters:return False
            for t,evaluation in zip(parameters,row['evaluations']):
                values,nodes=checked_chart_points(chart,evaluation,t,node_limit=work_limit-used);used+=nodes;points.update(values)
        return used==result['root_nodes'] and same(result['points'],sorted(points))
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,StopIteration):return False
