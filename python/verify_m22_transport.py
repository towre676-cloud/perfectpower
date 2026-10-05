"""Independent receipt verification using direct conjugated subgroup intersections.

Does not reuse the transport constructor, its cocycles, or its centralizer solver.
"""
from pathlib import Path
from itertools import permutations
from collections import Counter
import json
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions'


def compose(p,q):
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p):
    result=[0]*len(p)
    for i,x in enumerate(p):
        result[x]=i
    return tuple(result)


def conj(p,q):
    return compose(compose(p,q),inverse(p))


def sign(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))


def main():
    data=json.loads((OUT/'cap_transport.json').read_text())
    saved=np.load(OUT/'cap_permutations.npz')
    reps=[tuple(map(int,p)) for p in saved['representatives']]
    h=[tuple(map(int,p)) for p in saved['cap']]
    identity=tuple(range(22))
    twos=[p for p in h if p!=identity and compose(p,p)==identity]
    klein={frozenset([identity,p,q,compose(p,q)]) for p in twos for q in twos if p!=q and compose(p,q)==compose(q,p)}
    # Match the constructor's lexicographic subgroup convention exactly.
    ordered=sorted(tuple(sorted(k)) for k in klein)
    a4=[frozenset(p for p in h if {conj(p,q) for q in k}==set(k)) for k in ordered]
    localcaps={v:frozenset(conj(reps[v],p) for p in h) for v in data['component_vertices']}
    localletters={v:[frozenset(conj(reps[v],p) for p in a) for a in a4] for v in localcaps}
    edges={(r['source'],r['target']):tuple(r['permutation']) for r in data['transport_edges']}
    checked=0
    for (v,w),transport in edges.items():
        d5=localcaps[v]&localcaps[w]
        assert len(d5)==10
        source=[next(iter((a&d5)-{identity})) for a in localletters[v]]
        target=[next(iter((a&d5)-{identity})) for a in localletters[w]]
        assert all(len(a&d5)==2 for a in localletters[v]+localletters[w])
        actual=tuple(target.index(x) for x in source)
        assert actual==transport and sign(actual)==-1
        checked+=1
    # A depth-first spanning tree, independently of the construction's BFS.
    paths={0:tuple(range(5))};stack=[0];loops=[]
    while stack:
        v=stack.pop()
        for w in sorted((b for a,b in edges if a==v),reverse=True):
            candidate=compose(edges[v,w],paths[v])
            if w not in paths:
                paths[w]=candidate;stack.append(w)
            else:
                loops.append(compose(inverse(paths[w]),candidate))
    group={tuple(range(5))};pending=list(group)
    for p in pending:
        for g in loops:
            q=compose(g,p)
            if q not in group:
                group.add(q);pending.append(q)
    assert group==set(permutations(range(5)))
    def character(p):
        fixed=sum(i==p[i] for i in range(5))-1
        squarefixed=sum(i==p[p[i]] for i in range(5))-1
        return (fixed*fixed-squarefixed)//2
    assert sum(character(p)**2 for p in group)==120
    even=[p for p in group if sign(p)==1]
    assert sum(character(p)**2 for p in even)==120
    witness=data['orientation_cover']['base_odd_cycle_vertices'];p=tuple(range(5))
    for v,w in zip(witness,witness[1:]):
        p=compose(edges[v,w],p)
    assert p==tuple(data['orientation_cover']['base_odd_cycle_holonomy']) and sign(p)==-1
    result={'direct_intersection_transports_checked':checked,'independent_DFS_holonomy_order':len(group),
        'full_holonomy_character_inner_product':1,'even_holonomy_character_inner_product':2,
        'odd_cycle_length':len(witness)-1,'canonical_transport_verified_without_cocycles':True,
        'scope':'Independent exact verification of geometry and transport; not a CKM derivation.'}
    (OUT/'independent_transport_validation.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
