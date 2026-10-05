"""Complete per-parameter evaluation of composed arithmetic generators.

Infinite coverage follows from the source generator proof. Every evaluation
returns finite, complete integer fibres, with one shared root-node budget.
Evaluation does not classify the nonlinear parameter image globally.
"""
from .arithmetic_engine import verify_result
from .polynomial_charts import chart_points,checked_chart_points
from .residue_cover import evaluate
from .sturm_fibres import root_certificate,verify_roots
from .divisor_square import WorkLimit


def family_points(result,parameter,*,node_limit=100000):
    if result['status']!='GENERATOR' or not verify_result(result,work_limit=node_limit):raise ValueError('complete arithmetic generator required')
    if type(parameter) is not int or abs(parameter).bit_length()>16384 or type(node_limit) is not int or node_limit<1:
        raise ValueError('bounded integer parameter and positive node budget required')
    used=0
    def walk(node):
        nonlocal used
        proof=node['proof'];kind=proof['kind'];evidence={'kind':kind}
        if kind=='constant':points=[(parameter,y) for y in node['generator']['y']]
        elif kind=='exact_power':
            y=evaluate(proof['root_coefficients'],parameter)
            points=sorted({(parameter,v) for v in ({y,-y} if node['degree']%2==0 else {y})})
        elif kind=='power_charts':
            points=set();rows=[]
            for i,chart in enumerate(proof['parameterization']['charts']):
                if used>=node_limit:raise WorkLimit('shared generator evaluation node budget exceeded')
                row=chart_points(chart,parameter,node_limit=node_limit-used);used+=row['root_nodes'];points.update(row['points']);rows.append({'chart':i,**row})
            points=sorted(points);evidence['charts']=rows
        elif kind=='content_power':
            child,evidence['child']=walk(proof['outer_result']);points=sorted((x,proof['root']*y) for x,y in child)
        elif kind=='polynomial_composition':
            child,evidence['child']=walk(proof['outer_result']);scale=proof['witness_scale'];inner=proof['decomposition']['inner'];points=set();fibres=[]
            for u in sorted({u for u,v in child if v%scale==0}):
                if used>=node_limit:raise WorkLimit('shared generator pullback node budget exceeded')
                f=list(inner);f[0]-=u;cert=root_certificate(f,node_limit=node_limit-used);used+=cert['nodes_checked'];fibres.append({'value':u,'certificate':cert})
                points.update((x,v//scale) for x in cert['roots'] for cu,v in child if cu==u and v%scale==0)
            points=sorted(points);evidence['fibres']=fibres
        else:raise ValueError('unsupported generator interpreter')
        if any(y**node['degree']!=evaluate(node['coefficients'],x) for x,y in points):raise AssertionError('generator violates original equation')
        evidence['points']=points
        return points,evidence
    points,evidence=walk(result)
    return {'schema':'pp-arithmetic-family-evaluation/1','coefficients':result['coefficients'],'degree':result['degree'],
            'parameter':parameter,'points':points,'evidence':evidence,'root_nodes':used,'complete':True,'execution_verified':False}


def verify_family_evaluation(source,result,*,node_limit=100000):
    import json
    try:
        same=lambda a,b:json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)
        if source['status']!='GENERATOR' or not verify_result(source,work_limit=node_limit):return False
        if result['schema']!='pp-arithmetic-family-evaluation/1' or result['complete'] is not True or result['execution_verified'] is not False:return False
        if not same(result['coefficients'],source['coefficients']) or result['degree']!=source['degree']:return False
        t=result['parameter'];used=0
        if type(t) is not int:return False
        def walk(node,evidence):
            nonlocal used
            proof=node['proof'];kind=proof['kind']
            if evidence['kind']!=kind:raise ValueError('generator kind mismatch')
            if kind=='constant':points=[(t,y) for y in node['generator']['y']]
            elif kind=='exact_power':
                y=evaluate(proof['root_coefficients'],t);points=sorted({(t,v) for v in ({y,-y} if node['degree']%2==0 else {y})})
            elif kind=='power_charts':
                charts=proof['parameterization']['charts'];rows=evidence['charts'];points=set()
                if [r['chart'] for r in rows]!=list(range(len(charts))):raise ValueError('missing generator chart')
                for chart,row in zip(charts,rows):
                    values,nodes=checked_chart_points(chart,row,t,node_limit=node_limit-used);used+=nodes;points.update(values)
                points=sorted(points)
            elif kind=='content_power':points=sorted((x,proof['root']*y) for x,y in walk(proof['outer_result'],evidence['child']))
            elif kind=='polynomial_composition':
                child=walk(proof['outer_result'],evidence['child']);scale=proof['witness_scale'];inner=proof['decomposition']['inner'];points=set()
                if [r['value'] for r in evidence['fibres']]!=sorted({u for u,v in child if v%scale==0}):raise ValueError('missing pullback fibre')
                for fibre in evidence['fibres']:
                    u=fibre['value'];cert=fibre['certificate'];f=list(inner);f[0]-=u
                    if tuple(cert['coefficients'])!=tuple(f) or cert['domain']!=[None,None] or used>=node_limit or not verify_roots(cert,node_limit=node_limit-used):raise ValueError('invalid pullback roots')
                    used+=cert['nodes_checked'];points.update((x,v//scale) for x in cert['roots'] for cu,v in child if cu==u and v%scale==0)
                points=sorted(points)
            else:raise ValueError('unsupported generator')
            if not same(points,evidence['points']):raise ValueError('incorrect generator output')
            return points
        points=walk(source,result['evidence'])
        return used==result['root_nodes'] and same(points,result['points'])
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,StopIteration):return False
