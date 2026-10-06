"""Exact fermion covariant multiplicities through three scalar insertions.

The Molien projector factors over the three independent 3.A6 groups.
Symmetric scalar powers use cycle-index characters, not distinguishable
tensor copies. Both complex fields and their conjugates are counted.
"""
from collections import Counter
from functools import lru_cache
from fractions import Fraction as Q
from itertools import combinations_with_replacement, product as choices
from develop_valentiner_frames import generators,group_closure,mul,product,conjugate
from develop_valentiner_invariants import Z,O,add,sub,scale,exact_integer
from valentiner_canonical_operators import FERMIONS,SCALARS

FAMILIES={'u':0,'d':1,'H':2}
CYCLES={0:[(Q(1),())],1:[(Q(1),(1,))],
        2:[(Q(1,2),(1,1)),(Q(1,2),(2,))],
        3:[(Q(1,6),(1,1,1)),(Q(1,2),(1,2)),(Q(1,3),(3,))]}


def census(max_degree=3):
    if max_degree not in range(4):raise ValueError('Cycle index implemented through scalar degree three')
    group=group_closure(generators())[0]
    def trace(g):return tuple(sum(Q(g[1][3*i+i][j],g[0]) for i in range(3)) for j in range(4))
    signatures=Counter(tuple(trace(gk) for gk in (g,mul(g,g),mul(mul(g,g),g))) for g in group)
    classes=[]
    for traces,n in signatures.items():
        values=[]
        for t in traces:values.extend([t,conjugate(t),sub(product(t,conjugate(t)),O)])
        classes.append((values,n))
    @lru_cache(None)
    def moment(exponents):
        total=Z
        for values,n in classes:
            term=O
            for v,e in zip(values,exponents):
                for _ in range(e):term=product(term,v)
            total=add(total,scale(term,Q(n,len(group))))
        return total
    scalars=SCALARS+[(name+'-dagger',b,a,tuple(-q for q in c)) for name,a,b,c in SCALARS]
    rows=[]
    for degree in range(max_degree+1):
        for indexes in combinations_with_replacement(range(8),degree):
            counts=Counter(indexes);phase=tuple(sum(scalars[i][3][k]*n for i,n in counts.items())%6 for k in range(2))
            cycle_options=[CYCLES[counts[i]] for i in counts]
            polynomial=[]
            for option in choices(*cycle_options):
                coefficient=Q(1);exponents=[[0]*9 for _ in range(3)]
                for i,(factor,cycles) in zip(counts,option):
                    coefficient*=factor;name,to,fr,_=scalars[i]
                    for k in cycles:
                        if name.startswith('S'):exponents[2][3*(k-1)+2]+=1
                        else:
                            exponents[FAMILIES[to]][3*(k-1)]+=1
                            exponents[FAMILIES[fr]][3*(k-1)+1]+=1
                polynomial.append((coefficient,exponents))
            for left,(lf,lq) in FERMIONS.items():
                for right,(rf,rq) in FERMIONS.items():
                    if phase!=tuple((a-b)%6 for a,b in zip(lq,rq)):continue
                    total=Z
                    for coefficient,base in polynomial:
                        exponents=[e.copy() for e in base]
                        exponents[FAMILIES[lf]][1]+=1
                        exponents[FAMILIES[rf]][0]+=1
                        term=O
                        for e in exponents:term=product(term,moment(tuple(e)))
                        total=add(total,scale(term,coefficient))
                    multiplicity=exact_integer(total)
                    if multiplicity:
                        rows.append({'left':left,'right':right,'scalar_degree':degree,
                                     'fields':{scalars[i][0]:n for i,n in counts.items()},'multiplicity':multiplicity})
    def totals(lefts):
        return [sum(r['multiplicity'] for r in rows if r['left'] in lefts and r['scalar_degree']==d) for d in range(max_degree+1)]
    return {'group_order':len(group),'character_power_classes':len(classes),'maximum_scalar_degree':max_degree,
            'Higgs_covariant_counts_by_degree':totals(['bare']),
            'heavy_mass_covariant_counts_by_degree':totals(['D','H_A','H_B']),
            'covariants':rows,'scope':'Exact complex covariant dimensions; real CP couplings pair conjugate contractions. Scalar insertions only, no derivative operators.'}


def quality_bound(fields,kernels,certificate,cutoff,spurion=1.):
    """Worst-case determinant bound for unit-normalized invariant tensors.

    Each independent tensor has Frobenius norm one and real coefficient
    magnitude at most one. Tensor contraction is bounded by the product
    of the physical scalar norms. No cancellation between couplings is used.
    The certificate includes Higgs degrees one to three and mass degrees
    two and three, the nonrenormalizable terms in the enumerated space.
    """
    import numpy as np
    if cutoff<=0 or spurion<=0:raise ValueError('Positive cutoff and spurion required')
    norms={s[0]:np.linalg.norm(f) for s,f in zip(SCALARS,fields)}
    norms.update({s[0]+'-dagger':norms[s[0]] for s in SCALARS})
    rows=[]
    for k in kernels:
        # Factor the real Higgs VEV and the real spurion out of the rows.
        reduced=np.vstack([k['T'],k['F']]);size=0.
        for row in certificate['covariants']:
            degree=row['scalar_degree']
            if degree==0 or (degree<2 and row['left']!='bare'):continue
            product_norm=np.prod([norms[name]**power for name,power in row['fields'].items()])
            if row['left']=='bare':
                contribution=product_norm/cutoff**degree*(1 if row['right']=='bare' else spurion**2)
            else:contribution=product_norm/cutoff**(degree-1)
            size+=row['multiplicity']*contribution
        r=float(np.linalg.norm(np.linalg.inv(reduced),2)*size)
        if r>=1:bound=None
        else:bound=float(-12*np.log1p(-r))
        rows.append({'relative_operator_norm_bound':r,'absolute_phase_bound':bound})
    return {'cutoff':cutoff,'coefficient_absolute_bound':1.,'tensor_normalization':'unit Frobenius norm',
            'sectors':rows,'combined_absolute_phase_bound':None if any(r['absolute_phase_bound'] is None for r in rows) else sum(r['absolute_phase_bound'] for r in rows),
            'scope':'Uniform finite-EFT bound for all higher Higgs and heavy-mass/source terms through three scalar insertions; independent coefficients inside the stated norm domain. No assertion about operators beyond the stated order.'}
