"""Exact power identities and complete searches in declared positive boxes."""
from math import gcd
from functools import reduce
from .divisor_square import WorkLimit


def _integer(value, lo, hi, name):
    if type(value) is not int or not lo<=value<=hi:
        raise ValueError(f'{name} must be an integer in [{lo},{hi}]')


def power_sum_witness(terms, target, degree):
    _integer(degree,2,64,'degree'); terms=tuple(terms)
    if len(terms) not in (3,4) or any(type(t) is not int or t<=0 for t in terms) or type(target) is not int or target<=0:
        raise ValueError('three or four positive integer terms and positive target required')
    if sum(t**degree for t in terms)!=target**degree:
        raise ValueError('power identity is false')
    g=reduce(gcd,terms+(target,)); normalized=tuple(sorted(t//g for t in terms))
    return {'degree':degree,'terms':sorted(terms),'target':target,'gcd':g,
            'primitive':g==1,'normalized_terms':normalized,'normalized_target':target//g,
            'exact_replay':True,'execution_verified':False}


def search_power_sums(degree, terms, bound, *, work_limit=1_000_000, primitive_only=False):
    _integer(degree,2,64,'degree'); _integer(terms,3,4,'terms')
    _integer(bound,1,100_000,'bound'); _integer(work_limit,1,100_000_000,'work limit')
    if type(primitive_only) is not bool:raise ValueError('primitive_only must be boolean')
    estimate=bound*(bound+1)//2+(bound*(bound-1)//2 if terms==3 else bound*(bound-1)*(bound+1)//6)
    if estimate>work_limit:raise WorkLimit('complete pair/search loops exceed work limit; no partial list returned')
    powers=[n**degree for n in range(bound+1)]; pairs={}
    for b in range(1,bound+1):
        for a in range(1,b+1):pairs.setdefault(powers[a]+powers[b],[]).append((a,b))
    found=set(); loops=0
    for d in range(1,bound+1):
        for e in range(1,d):
            cs=(range(1,e+1) if terms==4 else (None,))
            for c in cs:
                loops+=1
                tail=(e,) if c is None else (c,e)
                remainder=powers[d]-sum(powers[t] for t in tail)
                for a,b in pairs.get(remainder,()):
                    if b<=tail[0]:
                        solution=(a,b)+tail+(d,)
                        if not primitive_only or reduce(gcd,solution)==1:found.add(solution)
    return {'degree':degree,'terms':terms,'bound':bound,'primitive_only':primitive_only,
            'solutions':sorted(found),'pair_entries':bound*(bound+1)//2,
            'search_loops':loops,'complete_in_domain':True,'globally_complete':False,
            'domain':f'1 <= a1 <= ... <= a{terms} < target <= {bound}',
            'execution_verified':False}
