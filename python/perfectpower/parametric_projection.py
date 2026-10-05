"""Whole two-coordinate power-curve queries to exact Presburger parameters."""
from dataclasses import dataclass
from .curve_queries import query_curve
from .semilinear_domains import render_domains
from .divisor_square import WorkLimit


def _curve_predicate(atoms,names):
    from .simplifier import _eval
    mapping=dict(zip(names,('x','y')));operations=0
    def term(node):
        nonlocal operations
        operations+=1
        if operations>10000:raise WorkLimit('curve SMT expression budget exceeded')
        if isinstance(node,str):
            if node in mapping:return mapping[node]
            if node.isascii() and node.isdecimal():return node
            raise ValueError('polynomial curve term required')
        if not isinstance(node,list) or not node or node[0] not in ('+','-','*'):raise ValueError('polynomial arithmetic required')
        op,args=node[0],node[1:]
        if op=='-' and len(args)==1:return '-('+term(args[0])+')'
        if len(args)<2:raise ValueError('arithmetic arity')
        return '('+op.join(term(a) for a in args)+')'
    def constant(node):
        if any(n in term(node) for n in ('x','y')):raise ValueError('integer constant required')
        value=_eval(node,{})
        if type(value) is not int:raise ValueError('integer constant required')
        return value
    def atom(left,right,relation):
        if any(isinstance(a,list) and a and a[0]=='mod' for a in (left,right)):
            if not (isinstance(left,list) and left and left[0]=='mod'):
                left,right=right,left;relation={'=':'=','!=':'!=','<':'>','<=':'>=','>':'<','>=':'<='}[relation]
            if len(left)!=3:raise ValueError('mod arity')
            return {'expr':term(left[1]),'modulus':constant(left[2]),'relation':relation,'value':constant(right)}
        return {'expr':term(left)+'-('+term(right)+')','relation':relation}
    def boolean(node,depth=0):
        if depth>64:raise WorkLimit('Boolean curve depth budget exceeded')
        if node=='true':return True
        if node=='false':return False
        if not isinstance(node,list) or not node:raise ValueError('Boolean curve condition required')
        op,args=node[0],node[1:]
        if op in ('and','or','not'):return {'op':op,'args':[boolean(a,depth+1) for a in args]}
        if op=='=>':
            if len(args)<2:raise ValueError('implication arity')
            out=boolean(args[-1],depth+1)
            for a in reversed(args[:-1]):out={'op':'or','args':[{'op':'not','args':[boolean(a,depth+1)]},out]}
            return out
        if op in ('=','<','<=','>','>=','distinct'):
            if len(args)<2:raise ValueError('comparison arity')
            pairs=[(a,b) for i,a in enumerate(args) for b in args[i+1:]] if op=='distinct' else list(zip(args,args[1:]))
            return {'op':'and','args':[atom(a,b,'!=' if op=='distinct' else op) for a,b in pairs]}
        raise ValueError('unsupported curve Boolean operation')
    return {'op':'and','args':[boolean(a) for a in atoms]}


@dataclass
class ParametricProjection:
    smt:str
    eliminated_symbols:tuple
    parameter:str
    query:dict


def project_parameterized_query(script,*,branch_limit=128):
    from .integer_projection import _parse_integer_query
    from .finite_formula import _poly
    from .smt_adapter import _padd
    names,atoms=_parse_integer_query(script)
    if len(names)!=2:raise ValueError('two original integer coordinates required')
    for relation in atoms:
        if not isinstance(relation,list) or len(relation)!=3 or relation[0]!='=':continue
        try:polynomial=_padd(_poly(relation[1],names),_poly(relation[2],names),-1)
        except ValueError:continue
        variables=sorted({v for m in polynomial for v,e in m})
        if len(variables)!=2 or any(len(m)>1 for m in polynomial):continue
        x,y=variables;dx=max(e for m in polynomial for v,e in m if v==x);dy=max(e for m in polynomial for v,e in m if v==y)
        if min(dx,dy)<2:continue
        left=[polynomial.get((),0)]+[polynomial.get(((x,i),),0) for i in range(1,dx+1)]
        right=[0]+[-polynomial.get(((y,i),),0) for i in range(1,dy+1)]
        predicate=_curve_predicate([a for a in atoms if a is not relation],(x,y))
        query=query_curve(left,right,predicate,point_limit=0)
        if query['status']!='COMPLETE' or query['schema']!='pp-polynomial-curve-query/1':continue
        parameter='_pp_curve'
        while parameter in names:parameter+='0'
        smt=render_domains([r['domain'] for r in query['charts']],parameter,branch_limit=branch_limit)
        return ParametricProjection(smt,(x,y),parameter,query)
    raise ValueError('no complete explicit power-curve parameterization')
