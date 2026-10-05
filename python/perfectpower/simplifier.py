"""Exact reductions with explicit scope; no unsupported global-solving promise.

The SMT compiler keeps a replayable equivalence chain. The power interface
keeps necessary local information even when a global height bound is unknown.
"""
import json
from copy import deepcopy
from .arithmetic_engine import ArithmeticEngine
from .residue_cover import residue_cover, scan_cover, integer_polynomial, evaluate
from .divisor_square import WorkLimit


def analyze_power(coefficients, degree=2, *, interval=None, work_limit=100000):
    f=integer_polynomial(coefficients)
    engine=ArithmeticEngine(work_limit=work_limit)
    global_result=engine.solve(f,degree)
    cover=residue_cover(f,degree)
    result={'schema':'pp-arithmetic-analysis/1','coefficients':f,'degree':degree,
            'global':global_result,'necessary':[{'kind':'residue_cover','certificate':cover}],
            'bounded':None,'residual':{'coefficients':f,'degree':degree},
            'execution_verified':False}
    if interval is not None:
        if not isinstance(interval,(list,tuple)) or len(interval)!=2:
            raise ValueError('closed interval pair required')
        lo,hi=interval
        from .factored_sieve import adaptive_cover
        bounded_cover=adaptive_cover(cover,lo,hi)
        try:
            scan=scan_cover(bounded_cover,lo,hi,work_limit=work_limit)
            result['bounded']={'status':'COMPLETE','scope':'closed x interval',
                               'cover':bounded_cover,**scan}
        except WorkLimit as error:
            result['bounded']={'status':'UNRESOLVED','interval':[lo,hi],'reason':str(error)}
    if global_result['status'] in ('COMPLETE','GENERATOR'):result['residual']=None
    return result


def verify_analysis(result, *, work_limit=100000):
    """Replay all advertised fields, including unresolved scope and residual."""
    try:
        if result['schema']!='pp-arithmetic-analysis/1':return False
        bounded=result['bounded']
        interval=None if bounded is None else bounded['interval']
        rebuilt=analyze_power(result['coefficients'],result['degree'],interval=interval,work_limit=work_limit)
        return json.dumps(result,sort_keys=True)==json.dumps(rebuilt,sort_keys=True)
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def answer_points(analysis, predicate):
    """Answer a question over the declared complete scope, or give a witness.

    Predicates: {coordinate: x|y, op: <=|>=|=|mod, value: integer,
    modulus: positive integer (mod only)}. No opaque executable callbacks.
    """
    coordinate=predicate.get('coordinate');op=predicate.get('op');value=predicate.get('value')
    if coordinate not in ('x','y') or op not in ('<=','>=','=','mod','unique') or (op!='unique' and type(value) is not int):
        raise ValueError('supported integer predicate required')
    modulus=predicate.get('modulus')
    if op=='mod' and (type(modulus) is not int or modulus<1):raise ValueError('positive modulus required')
    if coordinate=='x' and op=='mod':
        cover=analysis['necessary'][0]['certificate']
        if cover['modulus']%modulus==0 and all(r%modulus==value%modulus for r in cover['allowed']):
            return {'answer':'ALL','witness':None,'scope':'all integers',
                    'reason':'necessary residue cover implies the predicate'}
    if coordinate=='y' and op=='mod' and modulus<=256:
        cover=analysis['necessary'][0]['certificate']
        if cover['modulus']%modulus==0:
            residues={evaluate(analysis['coefficients'],r)%modulus for r in cover['allowed']}
            possible=[y for y in range(modulus) if pow(y,analysis['degree'],modulus) in residues]
            if all(y%modulus==value%modulus for y in possible):
                return {'answer':'ALL','witness':None,'scope':'all integers',
                        'reason':'necessary power residues imply the predicate'}
    global_result=analysis['global'];bounded=analysis['bounded']
    source=global_result if global_result['status']=='COMPLETE' else bounded
    if source is None or source['status']!='COMPLETE':return {'answer':'UNKNOWN','scope':None}
    index=0 if coordinate=='x' else 1
    if op=='unique':
        values=sorted({p[index] for p in source['points']})
        return {'answer':'EMPTY' if not values else 'UNIQUE' if len(values)==1 else 'MULTIPLE',
                'values':values,'scope':'all integers' if source is global_result else {'x_interval':source['interval']}}

    def holds(point):
        n=point[index]
        return n<=value if op=='<=' else n>=value if op=='>=' else n==value if op=='=' else n%modulus==value%modulus
    bad=next((list(p) for p in source['points'] if not holds(p)),None)
    return {'answer':'COUNTEREXAMPLE' if bad is not None else 'ALL', 'witness':bad,
            'scope':'all integers' if source is global_result else {'x_interval':source['interval']}}


def polynomial_pullback(outer,inner,degree=2,*,work_limit=100000):
    """Complete outer points lifted through ALL integer polynomial fibres."""
    from .decomposition import compose
    from .sturm_fibres import root_certificate
    outer=integer_polynomial(outer);inner=integer_polynomial(inner)
    if len(inner)<2:raise ValueError('nonconstant integer inner polynomial required')
    f=integer_polynomial(int(c) for c in compose(outer,inner))
    solved=ArithmeticEngine(work_limit=work_limit).solve(outer,degree)
    result={'schema':'pp-polynomial-pullback/1','coefficients':f,'outer':outer,'inner':inner,
            'degree':degree,'outer_result':solved,'status':'UNRESOLVED','points':None,'fibres':[]}
    if solved['status']!='COMPLETE':return result
    points=set()
    try:
        for u,v in solved['points']:
            shifted=list(inner);shifted[0]-=u
            cert=root_certificate(shifted,node_limit=work_limit)
            result['fibres'].append({'outer_point':[u,v],'certificate':cert})
            points.update((x,v) for x in cert['roots'])
    except WorkLimit:
        result['fibres']=[];return result
    result.update(status='COMPLETE',points=sorted(points));return result


def _square_cube(script):
    from .integer_projection import _parse_integer_query
    from .finite_projection import _render,_simplify
    names,atoms=_parse_integer_query(script)
    for atom in atoms:
        for x in names:
            for y in names:
                if x==y:continue
                left=['*',x,x];right=['*',y,y,y]
                if atom not in (['=',left,right],['=',right,left]):continue
                t='_pp_power'
                while t in names:t+='_'
                bindings={x:['*',t,t,t],y:['*',t,t]}
                def substitute(node):
                    if isinstance(node,str):return deepcopy(bindings.get(node,node))
                    return [node[0]]+[substitute(a) for a in node[1:]]
                remaining=[n for n in names if n not in (x,y)]+[t]
                residual=_simplify(['and']+[substitute(a) for a in atoms if a is not atom])
                out='\n'.join(['(set-logic QF_NIA)']+[f'(declare-const {n} Int)' for n in remaining]+[f'(assert {_render(residual)})','(check-sat)'])+'\n'
                return out
    raise ValueError('no direct square cube relation')


def _coprime_power(script):
    from math import gcd
    from .integer_projection import _parse_integer_query
    from .finite_formula import _poly
    from .smt_adapter import _padd
    from .finite_projection import _render,_simplify
    names,atoms=_parse_integer_query(script)
    for atom in atoms:
        if not isinstance(atom,list) or len(atom)!=3 or atom[0]!='=':continue
        try:polynomial=_padd(_poly(atom[1],names),_poly(atom[2],names),-1)
        except ValueError:continue
        if len(polynomial)!=2:continue
        terms=list(polynomial.items())
        (m,a),(n,b)=terms
        if len(m)!=1 or len(n)!=1 or a!=-b or not a:continue
        (x,p),(y,q)=m[0],n[0]
        if x==y or min(p,q)<2 or gcd(p,q)!=1:continue
        t='_pp_power'
        while t in names:t+='_'
        bindings={x:['*']+[t]*q,y:['*']+[t]*p}
        def substitute(node):
            if isinstance(node,str):return deepcopy(bindings.get(node,node))
            return [node[0]]+[substitute(a) for a in node[1:]]
        residual=_simplify(['and']+[substitute(a) for a in atoms if a is not atom])
        remaining=[n for n in names if n not in (x,y)]+[t]
        return '\n'.join(['(set-logic QF_NIA)']+[f'(declare-const {n} Int)' for n in remaining]+[f'(assert {_render(residual)})','(check-sat)'])+'\n'
    raise ValueError('no equal-coefficient coprime power relation')


def _definition(script):
    from .integer_projection import _parse_integer_query
    from .finite_projection import _render,_simplify
    names,atoms=_parse_integer_query(script)
    def contains(node,name):
        return node==name if isinstance(node,str) else any(contains(a,name) for a in node[1:])
    for atom in atoms:
        if not isinstance(atom,list) or len(atom)!=3 or atom[0]!='=':continue
        for name,expression in (atom[1:],atom[1:][::-1]):
            if not isinstance(name,str) or name not in names or contains(expression,name):continue
            def substitute(node):
                if isinstance(node,str):return deepcopy(expression) if node==name else node
                return [node[0]]+[substitute(a) for a in node[1:]]
            residual=_simplify(['and']+[substitute(a) for a in atoms if a is not atom])
            return '\n'.join(['(set-logic QF_NIA)']+[f'(declare-const {n} Int)' for n in names if n!=name]+[f'(assert {_render(residual)})','(check-sat)'])+'\n'
    raise ValueError('no acyclic direct integer definition')


def _local_filters(script):
    """Expose necessary congruences directly to the host's residual solver."""
    from .integer_projection import _parse_integer_query
    from .finite_formula import _poly
    from .smt_adapter import _padd
    from .finite_projection import _literal,_render,_simplify
    try:names,atoms=_parse_integer_query(script)
    except ValueError:return script,[]
    restrictions=[];certificates=[]
    for atom in atoms:
        if not isinstance(atom,list) or len(atom)!=3 or atom[0]!='=':continue
        try:polynomial=_padd(_poly(atom[1],names),_poly(atom[2],names),-1)
        except ValueError:continue
        for y in names:
            yt=[(m,c) for m,c in polynomial.items() if any(v==y for v,e in m)]
            if len(yt)!=1:continue
            (m,c),=yt
            if len(m)!=1 or abs(c)!=1 or not 2<=m[0][1]<=8:continue
            d=m[0][1];other={m:v for m,v in polynomial.items() if m!=yt[0][0]}
            xs={v for m in other for v,e in m}
            if len(xs)!=1 or any(len(m)>1 for m in other):continue
            x,=xs;n=max((e for m in other for v,e in m),default=0)
            f=[-other.get((),0)//c]+[-other.get(((x,i),),0)//c for i in range(1,n+1)]
            cover=residue_cover(f,d)
            clauses=[]
            for table in cover['tables']:
                modulus=table['modulus'];allowed=table['allowed']
                if len(allowed)==modulus:continue
                clauses.append(_simplify(['or']+[['=', ['mod',x,str(modulus)],_literal(r)] for r in allowed]))
            if clauses:
                restrictions.extend(clauses)
                certificates.append({'input_symbol':x,'power_symbol':y,'relation':atom,'cover':cover})
            break
    if not restrictions:return script,[]
    assertion=_simplify(['and']+atoms+restrictions)
    out='\n'.join(['(set-logic QF_NIA)']+[f'(declare-const {n} Int)' for n in names]+[f'(assert {_render(assertion)})','(check-sat)'])+'\n'
    return out,certificates


def simplify_query(script, *, rounds=16, branch_limit=128):
    """Cost-gated fixed point of whole-query equivalences, with residual SMT.

    Reductions must remove an integer variable; branch expansion is budgeted.
    No SAT answer is inferred from an unhandled residual query.
    """
    from .integer_projection import project_integer_query,_parse_integer_query
    from .monomial_projection import project_monomial_query
    from .finite_projection import project_finite_query
    from .polynomial_relations import project_polynomial_query
    if any(type(n) is not int or n<1 for n in (rounds,branch_limit)):raise ValueError('positive budgets required')
    _parse_integer_query(script)
    current=script;steps=[];attempts=[]
    routes=[('square_cube',_square_cube),('coprime_power',_coprime_power),('substitution',_definition),('integer_lattice',lambda s:project_integer_query(s).smt),
            ('positive_monomial',lambda s:project_monomial_query(s,point_limit=branch_limit).smt),
            ('finite_relation',lambda s:project_finite_query(s,branch_limit=branch_limit).smt),
            ('polynomial_relation',lambda s:project_polynomial_query(s,branch_limit=branch_limit).smt)]
    import re
    def size(s):return len(re.findall(r'\(declare-(?:const|fun)\s',s))
    for _ in range(rounds):
        changed=False
        for name,route in routes:
            try:reduced=route(current)
            except ValueError as error:
                attempts.append({'method':name,'reason':str(error)});continue
            if size(reduced)>=size(current) or len(reduced)>max(4096,4*len(current)):
                attempts.append({'method':name,'reason':'no dimension benefit or expansion budget'});continue
            steps.append({'method':name,'before':current,'after':reduced,
                          'variables_removed':size(current)-size(reduced),'meaning':'existential equivalence'})
            current=reduced;changed=True;break
        if not changed:break
    current,necessary=_local_filters(current)
    # One free integer coordinate permits complete Boolean sign elimination,
    # even when no global integer-point theorem for the original curve exists.
    try:
        from .polynomial_domains import project_univariate_query
        reduced=project_univariate_query(current)['smt']
        if len(reduced)<=max(4096,4*len(current)):
            steps.append({'method':'univariate_domain','before':current,'after':reduced,
                          'variables_removed':0,'meaning':'pointwise integer equivalence'})
            current=reduced
    except ValueError:
        pass
    return {'schema':'pp-simplifier/1','original':script,'residual':current,'steps':steps,
            'necessary':necessary,'attempts':attempts,'budgets':{'rounds':rounds,'branch_limit':branch_limit},
            'status':'REDUCED' if steps or necessary else 'UNCHANGED','execution_verified':False}


def verify_simplification(result):
    try:
        rebuilt=simplify_query(result['original'],**result['budgets'])
        return json.dumps(rebuilt,sort_keys=True)==json.dumps(result,sort_keys=True)
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def verify_pullback(result, *, work_limit=100000):
    try:
        rebuilt=polynomial_pullback(result['outer'],result['inner'],result['degree'],work_limit=work_limit)
        return json.dumps(rebuilt,sort_keys=True)==json.dumps(result,sort_keys=True)
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def _eval(node,model):
    """Evaluate the supported SMT fragment using Euclidean integer division."""
    if isinstance(node,str):
        if node=='true':return True
        if node=='false':return False
        return int(node) if node.isascii() and node.isdecimal() else model[node]
    op,args=node[0],node[1:]
    if op=='ite':return _eval(args[1] if _eval(args[0],model) else args[2],model)
    values=[_eval(a,model) for a in args]
    if op=='+':return sum(values)
    if op=='-':return -values[0] if len(values)==1 else values[0]-sum(values[1:])
    if op=='*':
        out=1
        for n in values:out*=n
        return out
    if op in ('div','mod'):
        a,b=values
        if b==0:raise ValueError('division by zero has no canonical SMT model value')
        return (a//b if b>0 else -(a//(-b))) if op=='div' else a%abs(b)
    if op=='and':return all(values)
    if op=='or':return any(values)
    if op=='not':return not values[0]
    if op=='=>':
        out=values[-1]
        for n in reversed(values[:-1]):out=(not n) or out
        return out
    if op=='distinct':return len(set(values))==len(values)
    if op=='=':return all(a==b for a,b in zip(values,values[1:]))
    compare={'<':lambda a,b:a<b,'<=':lambda a,b:a<=b,'>':lambda a,b:a>b,'>=':lambda a,b:a>=b}
    if op in compare:return all(compare[op](a,b) for a,b in zip(values,values[1:]))
    raise ValueError('unsupported model expression')


def lift_model(result,model):
    """Recover and validate one ORIGINAL witness from a residual integer model.

    Reverse replay preserves compact parameterizations; finite alternatives
    are checked against the entire original context at their reduction step.
    This returns a sufficient witness, never a completeness claim.
    """
    import re
    from .integer_projection import _parse_integer_query,project_integer_query
    from .monomial_projection import project_monomial_query
    from .finite_projection import project_finite_query
    from .finite_formula import _poly
    from .smt_adapter import _padd
    if not verify_simplification(result):raise ValueError('invalid reduction chain')
    names=re.findall(r'\(declare-const ([A-Za-z_][A-Za-z0-9_]*) Int\)',result['residual'])
    if set(model)!=set(names) or any(type(v) is not int for v in model.values()):
        raise ValueError('exact integer values for all residual variables required')
    current=dict(model)
    for step in reversed(result['steps']):
        names,atoms=_parse_integer_query(step['before']);method=step['method']
        if method=='integer_lattice':
            current=project_integer_query(step['before']).lift(current)
        elif method=='univariate_domain':
            pass  # Same integer coordinate, now described by linear intervals.
        elif method in ('square_cube','coprime_power'):
            parameter=next(n for n in current if n not in names)
            selected=None
            for atom in atoms:
                if not isinstance(atom,list) or len(atom)!=3 or atom[0]!='=':continue
                try:p=_padd(_poly(atom[1],names),_poly(atom[2],names),-1)
                except ValueError:continue
                if len(p)!=2:continue
                (m,a),(n,b)=list(p.items())
                if len(m)==len(n)==1 and a==-b and a:
                    x,px=m[0];y,py=n[0]
                    from math import gcd
                    exact_shape=atom in (['=',['*']+[x]*px,['*']+[y]*py],['=',['*']+[y]*py,['*']+[x]*px])
                    shape_ok=method!='square_cube' or ({px,py}=={2,3} and exact_shape)
                    if x!=y and min(px,py)>=2 and gcd(px,py)==1 and shape_ok:
                        selected=(x,px,y,py);break
            if selected is None:raise ValueError('missing parameterized relation')
            x,px,y,py=selected;t=current.pop(parameter)
            current.update({x:t**py,y:t**px})
        elif method=='substitution':
            missing=next(n for n in names if n not in current)
            expression=None
            def contains(node):
                return node==missing if isinstance(node,str) else any(contains(a) for a in node[1:])
            for atom in atoms:
                if isinstance(atom,list) and len(atom)==3 and atom[0]=='=':
                    if atom[1]==missing and not contains(atom[2]):expression=atom[2];break
                    if atom[2]==missing and not contains(atom[1]):expression=atom[1];break
            current[missing]=_eval(expression,current)
        else:
            if method=='positive_monomial':
                projection=project_monomial_query(step['before'],point_limit=result['budgets']['branch_limit'])
                eliminated=projection.eliminated_symbols;points=projection.points
            elif method=='finite_relation':
                projection=project_finite_query(step['before'],branch_limit=result['budgets']['branch_limit'])
                eliminated=projection.emission.eliminated_symbols;points=projection.emission.points
            elif method=='polynomial_relation':
                from .polynomial_relations import project_polynomial_query
                projection=project_polynomial_query(step['before'],branch_limit=result['budgets']['branch_limit'])
                eliminated=projection.eliminated_symbols;points=projection.points
            else:raise ValueError('unknown reduction method')
            candidates=[dict(current,**dict(zip(eliminated,p))) for p in points]
            current=next((m for m in candidates if all(_eval(a,m) for a in atoms)),None)
            if current is None:raise ValueError('residual assignment is not a solution')
        if set(current)!=set(names) or not all(_eval(a,current) for a in atoms):
            raise ValueError('residual assignment does not lift to an original solution')
    names,atoms=_parse_integer_query(result['original'])
    if set(current)!=set(names) or not all(_eval(a,current) for a in atoms):
        raise ValueError('residual assignment is not a solution')
    return current
