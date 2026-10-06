"""Bounded repeated prime preimages with witnessed presentation compression.

Every prime step keeps all projective residue fibres. Bounded membership is
only a source of positive witnesses: a failed search never proves nonmembership.
"""
from itertools import product
from .elliptic_arithmetic import encode_point, root_budget
from .elliptic_subgroups import subgroup_preimage, linear_combination, parameters
from .elliptic_certificate_verifier import CheckBudget
from .divisor_square import WorkLimit


def controls(primes, max_steps, coefficient_bound, membership_limit):
    if type(primes) is not list or not primes or primes != sorted(set(primes)):
        raise ValueError('sorted distinct nonempty prime list required')
    for p in primes: parameters(p, [])
    for x, lo, hi in ((max_steps,1,16),(coefficient_bound,0,4),(membership_limit,1,1000000)):
        if type(x) is not int or not lo <= x <= hi: raise ValueError('saturation control out of range')


class MembershipSearch:
    def __init__(self, E, bound, limit): self.E, self.bound, self.remaining = E, bound, limit

    def witness(self, points, target):
        try:return self._witness(points,target)
        except WorkLimit:return None

    def _witness(self, points, target):
        if target is None: return [0]*len(points)
        for i, p in enumerate(points):
            for c in (1,-1):
                if abs(c)<=self.bound and self.E.mul(p,c)==target:
                    out=[0]*len(points);out[i]=c;return out
        # Refusal is an unresolved membership question, never an exclusion proof.
        count=(2*self.bound+1)**len(points)
        if count>self.remaining: return None
        self.remaining-=count
        multiples=[[self.E.mul(p,c) for c in range(-self.bound,self.bound+1)] for p in points]
        for cs in product(range(-self.bound,self.bound+1), repeat=len(points)):
            out=None
            for table,c in zip(multiples,cs):out=self.E.add(out,table[c+self.bound])
            if out==target:return list(cs)
        return None

    def reduce(self, points):
        current=list(points);removed=[];i=0
        while i<len(current):
            others=current[:i]+current[i+1:]
            cs=self.witness(others,current[i])
            if cs is None:i+=1;continue
            removed.append(dict(index=i,coefficients=cs));current=others
        return current,removed


def bounded_saturation(E, points, primes=None, max_steps=8, coefficient_bound=2,
                       membership_limit=100000, node_limit=100000):
    primes=[2,3] if primes is None else primes
    controls(primes,max_steps,coefficient_bound,membership_limit)
    parameters(primes[0],points);root_budget(node_limit)
    source=[E.checked(p) for p in points]
    search=MembershipSearch(E,coefficient_bound,membership_limit)
    current,initial_reductions=search.reduce(source)
    stages=[];closed=[];used=0
    while len(stages)<max_steps and len(current)<=4 and closed!=primes:
        if used>=node_limit:raise WorkLimit('shared saturation root budget exhausted')
        prime=next(p for p in primes if p not in closed)
        packet=subgroup_preimage(E,current,prime,node_limit-used);used+=packet['root_nodes']
        raw=[E.checked(p) for p in packet['generators']]
        witnesses=[search.witness(current,p) for p in raw]
        is_closed=all(cs is not None for cs in witnesses)
        reduced,removed=search.reduce(raw)
        stages.append(dict(preimage=packet,closure_witnesses=witnesses if is_closed else None,
                           reductions=removed,generators=[encode_point(p) for p in reduced]))
        # Previous closure transports only through a proven equality of groups.
        closed=sorted([*closed,prime]) if is_closed else []
        current=reduced
    status='closed' if closed==primes else 'width-limit' if len(current)>4 else 'step-limit'
    result=dict(schema='pp-bounded-elliptic-saturation/1',curve=E.specification,
        source_points=[encode_point(p) for p in source],primes=primes,max_steps=max_steps,
        coefficient_bound=coefficient_bound,membership_limit=membership_limit,
        initial_reductions=initial_reductions,stages=stages,
        generators=[encode_point(p) for p in current],closed_primes=closed,status=status,
        node_limit=node_limit,root_nodes=used,complete_mordell_weil_group=False,
        execution_verified=False)
    CheckBudget(2000000).packet(result)
    return result
