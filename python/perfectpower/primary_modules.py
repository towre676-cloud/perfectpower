"""Exact cyclic subgroup phases in finite p-primary modules.

Recovered from Formation's cyclic normal forms. Cyclic subgroups are not all
lattice atoms: the word 'atom' in the old application meant a critical probe.
Enumeration has explicit finite budgets and no group-formation classification.
"""
from itertools import product
from .local_quartic import _prime
from .integral_lattice import local_torsion_profile


def primary_cyclic_counts(p,exponents):
    exponents=tuple(exponents)
    if not _prime(p) or not exponents or any(type(e) is not int or e<1 for e in exponents):
        raise ValueError('prime and positive invariant exponents required')
    rows=[]
    for e in range(1,max(exponents)+1):
        killed=p**sum(min(e,a) for a in exponents)
        previous=p**sum(min(e-1,a) for a in exponents)
        phi=(p-1)*p**(e-1)
        rows.append({'order':p**e,'elements_exact_order':killed-previous,
                     'cyclic_subgroups':(killed-previous)//phi,'generators_per_subgroup':phi})
    return {'prime':p,'exponents':list(exponents),'group_order':p**sum(exponents),
            'by_order':rows,'nontrivial_cyclic_subgroups':sum(r['cyclic_subgroups'] for r in rows),
            'execution_verified':False}


def presentation_cyclic_counts(matrix,p,**budgets):
    profile=local_torsion_profile(matrix,p,**budgets)
    if profile['free_rank']:raise ValueError('finite cokernel required')
    es=profile['torsion_lengths']
    return primary_cyclic_counts(p,es) if es else {
        'prime':p,'exponents':[],'group_order':1,'by_order':[],
        'nontrivial_cyclic_subgroups':0,'execution_verified':False}


def subgroup_census(p,exponents,*,element_limit=512,join_limit=1_000_000):
    """All subgroups, as generated closures of cyclic subgroups (small modules)."""
    exponents=tuple(exponents)
    counts=primary_cyclic_counts(p,exponents)
    if type(element_limit) is not int or element_limit<1 or type(join_limit) is not int or join_limit<1:
        raise ValueError('positive enumeration budgets required')
    if counts['group_order']>element_limit:raise ValueError('element budget exceeded')
    moduli=tuple(p**e for e in exponents);zero=tuple(0 for _ in moduli)
    elements=tuple(product(*(range(m) for m in moduli)))
    add=lambda x,y:tuple((a+b)%m for a,b,m in zip(x,y,moduli))
    def cyclic(g):
        xs={zero};x=g
        while x!=zero:xs.add(x);x=add(x,g)
        return frozenset(xs)
    cyclics={cyclic(g) for g in elements if g!=zero}
    if len(cyclics)!=counts['nontrivial_cyclic_subgroups']:
        raise AssertionError('cyclic formula and enumeration disagree')
    groups={frozenset((zero,))};queue=list(groups);joins=0
    # A representative for each cyclic subgroup suffices to generate all joins.
    for H in queue:
        for C in cyclics:
            if C<=H:continue
            joins+=1
            if joins>join_limit:raise ValueError('subgroup join budget exceeded; no census')
            K=frozenset(add(h,c) for h in H for c in C)
            if K not in groups:groups.add(K);queue.append(K)
    histogram={}
    for H in groups:histogram[len(H)]=histogram.get(len(H),0)+1
    return {**counts,'all_subgroups':len(groups),'subgroups_by_order':dict(sorted(histogram.items())),
            'join_trials':joins,'scope':'complete finite subgroup census within explicit budgets'}


def cyclic_phase(p,exponents,generator):
    """Canonical subgroup key retains relative unit phases, not just heights."""
    exponents=tuple(exponents)
    counts=primary_cyclic_counts(p,exponents);moduli=tuple(p**e for e in exponents)
    g=tuple(generator)
    if len(g)!=len(moduli) or any(type(x) is not int for x in g):raise ValueError('matching integer generator required')
    g=tuple(x%m for x,m in zip(g,moduli));zero=tuple(0 for _ in g)
    if g==zero:return {'order':1,'canonical_generator':zero,'coordinate_heights':[0]*len(g)}
    heights=[]
    for x,e in zip(g,exponents):
        v=e if x==0 else 0
        if x:
            while x%p==0:x//=p;v+=1
        heights.append(e-v)
    order=p**max(heights)
    # Normalize the earliest coordinate of maximal order to its primitive unit 1.
    i=heights.index(max(heights));unit=g[i]//(p**(exponents[i]-heights[i]))
    inverse=pow(unit,-1,order)
    canonical=tuple(inverse*x%m for x,m in zip(g,moduli))
    return {'order':order,'canonical_generator':canonical,'coordinate_heights':heights}
