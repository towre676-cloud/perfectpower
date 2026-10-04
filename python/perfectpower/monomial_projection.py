"""Complete finite positive monomial relations inside existential SMT queries."""
from dataclasses import dataclass
from fractions import Fraction
from .integer_projection import _parse_integer_query
from .finite_projection import _number,_literal,_substitute,_simplify,_render
from .industrial_router import route_lia
from .monomial import solve_monomial,MonomialLimit


@dataclass
class MonomialProjection:
    smt:str
    eliminated_symbols:tuple
    remaining_symbols:tuple
    points:tuple
    solution:dict
    linear:bool


def project_monomial_query(script,*,point_limit=10000,**budgets):
    names,atoms=_parse_integer_query(script)
    def monomial(node):
        number=_number(node)
        if number is not None:return {},number
        if isinstance(node,str) and node in names:return {node:1},1
        if isinstance(node,list) and len(node)>=3 and node[0]=='*':
            out={};coefficient=1
            for child in node[1:]:
                powers,c=monomial(child);coefficient*=c
                for name,e in powers.items():out[name]=out.get(name,0)+e
            return out,coefficient
        raise ValueError('not a multiplicative monomial')
    equations=[];used=set()
    for atom in atoms:
        if isinstance(atom,list) and len(atom)==3 and atom[0]=='=':
            try:left,a=monomial(atom[1]);right,b=monomial(atom[2])
            except ValueError:continue
            if not a or not b or Fraction(b,a)<=0:continue
            row={name:left.get(name,0)-right.get(name,0) for name in set(left)|set(right)}
            # Variables cancelling on both sides still need positivity for
            # cancellation and must remain in the residual model.
            if not any(row.values()):continue
            equations.append((row,Fraction(b,a),set(left)|set(right)))
            used.update(left);used.update(right)
    if not equations:raise ValueError('no supported multiplicative equalities')
    positive=set()
    for atom in atoms:
        if isinstance(atom,list) and len(atom)==3:
            op,left,right=atom
            if isinstance(left,str) and left in used and ((op=='>=' and _number(right)==1) or (op=='>' and _number(right)==0)):
                positive.add(left)
            if isinstance(right,str) and right in used and ((op=='<=' and _number(left)==1) or (op=='<' and _number(left)==0)):
                positive.add(right)
    equations=[entry for entry in equations if entry[2]<=positive]
    if not equations:raise ValueError('every selected multiplicative variable needs an explicit positive-integer assertion')
    used=set().union(*(entry[2] for entry in equations))
    symbols=tuple(name for name in names if name in used)
    a=[[row.get(name,0) for name in symbols] for row,_,_ in equations]
    rhs=[value for _,value,_ in equations]
    solution=solve_monomial(a,rhs,point_limit=point_limit,**budgets)
    points=tuple(tuple(point) for point in solution['points'])
    if len(points)>point_limit:raise MonomialLimit('complete projection exceeds point budget')
    remaining=tuple(name for name in names if name not in used);branches=[]
    for point in points:
        bindings=dict(zip(symbols,point))
        branches.append(_simplify(['and']+[_substitute(atom,bindings) for atom in atoms]))
    assertion=_simplify(['or']+branches)
    out='\n'.join(['(set-logic QF_NIA)']+[f'(declare-const {name} Int)' for name in remaining]
                  +[f'(assert {_render(assertion)})','(check-sat)'])+'\n'
    routed,linear=route_lia(out)
    return MonomialProjection(routed,symbols,remaining,points,solution,linear)
