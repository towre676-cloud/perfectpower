"""Complete natural-index domains and optima for normalized Gamma polynomials.

Fixed expressions normalize to N(n)/D with D positive. Comparisons clear
only positive denominators; optimization scales values and keeps every tie.
Variable-width factorial ratios belong to the separate valuation backend.
"""
from fractions import Fraction as Q
import json
from .gamma_arithmetic import normalize, verify_normalization
from .polynomial_domains import (integer_domain, verify_domain,
                                optimize_polynomial, verify_optimization)
from .residue_cover import integer_polynomial


def _natural(predicate):
    return {'op':'and','args':[{'poly':[0,1],'relation':'>='},predicate]}


def _threshold(value):
    if type(value) is not int and not isinstance(value,(str,Q)):
        raise ValueError('exact integer, rational string or Fraction threshold required')
    if isinstance(value,str) and len(value)>16384:
        raise ValueError('threshold text budget exceeded')
    out=Q(value)
    if max(abs(out.numerator).bit_length(),out.denominator.bit_length())>16384:
        raise ValueError('threshold bit budget exceeded')
    return out


def _comparison(normal,relation,threshold):
    q=_threshold(threshold);f=[q.denominator*c for c in normal['numerator']]
    f[0]-=q.numerator*normal['denominator']
    return _natural({'poly':list(integer_polynomial(f)),'relation':relation})


def gamma_domain(spec,relation='>=',threshold=0,*,predicate=True,node_limit=100000):
    """Every natural index satisfying the fixed expression comparison."""
    normal=normalize(spec);q=_threshold(threshold)
    condition=_comparison(normal,relation,q)
    if predicate is True:domain=integer_domain(condition,node_limit=node_limit)
    else:
        from .semilinear_domains import semilinear_domain
        condition={'op':'and','args':[condition,predicate]}
        domain=semilinear_domain(condition,node_limit=node_limit)
    return {'schema':'pp-gamma-polynomial-domain/1','normalization':normal,
            'relation':relation,'threshold':str(q),'domain':domain,
            'complete':True,'execution_verified':False,**({'predicate':predicate} if predicate is not True else {})}


def optimize_gamma(spec,predicate=True,*,sense='min',node_limit=100000):
    """Global exact rational value and all natural-index optimizers."""
    normal=normalize(spec)
    pending=[predicate];modular=False;nodes=0
    while pending:
        node=pending.pop();nodes+=1
        if nodes>2048:raise ValueError('Gamma predicate node budget exceeded')
        if isinstance(node,dict):modular|='modulus' in node;pending.extend(node.get('args',[]))
    if modular:
        from .semilinear_domains import optimize_semilinear
        optimum=optimize_semilinear(_natural(predicate),normal['numerator'],sense=sense,node_limit=node_limit)
    else:optimum=optimize_polynomial(_natural(predicate),normal['numerator'],sense=sense,node_limit=node_limit)
    value=None if optimum['value'] is None else str(Q(optimum['value'],normal['denominator']))
    return {'schema':'pp-gamma-polynomial-optimum/1','normalization':normal,
            'predicate':predicate,'numerator_optimum':optimum,
            'status':optimum['status'],'value':value,'optimizers':_optimizers(optimum),
            'complete':True,'execution_verified':False}


def _same(a,b):return json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)


def _optimizers(optimum):
    if optimum['schema']=='pp-semilinear-optimum/1':
        return {'kind':'domain','domain':optimum['optimizer_domain']} if optimum['points'] is None else {'kind':'points','values':optimum['points']}
    return optimum['optimizers']


def verify_gamma_domain(result,*,node_limit=100000):
    try:
        normal=result['normalization'];domain=result['domain']
        condition=_comparison(normal,result['relation'],result['threshold']);predicate=result.get('predicate',True)
        if predicate is True:checker=verify_domain
        else:
            from .semilinear_domains import verify_domain as checker
            condition={'op':'and','args':[condition,predicate]}
        return (result['schema']=='pp-gamma-polynomial-domain/1'
                and result['complete'] is True and result['execution_verified'] is False
                and verify_normalization(normal)
                and _same(domain['predicate'],condition)
                and checker(domain,node_limit=node_limit))
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


def verify_gamma_optimum(result,*,node_limit=100000):
    try:
        normal=result['normalization'];optimum=result['numerator_optimum']
        checker=verify_optimization
        if optimum['schema']=='pp-semilinear-optimum/1':
            from .semilinear_domains import verify_optimization as checker
        value=None if optimum['value'] is None else str(Q(optimum['value'],normal['denominator']))
        return (result['schema']=='pp-gamma-polynomial-optimum/1'
                and result['complete'] is True and result['execution_verified'] is False
                and verify_normalization(normal)
                and _same(optimum['objective'],normal['numerator'])
                and _same(optimum['feasible_domain']['predicate'],_natural(result['predicate']))
                and result['status']==optimum['status'] and result['value']==value
                and _same(result['optimizers'],_optimizers(optimum))
                and checker(optimum,node_limit=node_limit))
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False
