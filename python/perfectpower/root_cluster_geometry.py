"""Split-root p-adic cluster trees and geometric semistable double-cover graphs.

Odd residue characteristic; rational branch roots. The graph is geometric,
before stability contractions; component twists and Frobenius are not inferred.
"""
from fractions import Fraction as Q
from math import isqrt


def prime(p):return type(p) is int and p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def valuation(x,p):
    x=Q(x)
    if not x:raise ValueError('distinct roots required')
    def v(a):
        n=0
        while a%p==0:a//=p;n+=1
        return n
    return v(abs(x.numerator))-v(x.denominator)


def cluster_geometry(roots,p):
    if not prime(p) or p==2:raise ValueError('odd prime required')
    roots=list(map(Q,roots));m=len(roots)
    if not 3<=m<=9 or len(set(roots))!=m:raise ValueError('3 through 9 distinct rational roots required')
    nodes=[]
    def node(indices,parent=None):
        depth=min(valuation(roots[i]-roots[j],p) for k,i in enumerate(indices) for j in indices[k+1:]);idx=len(nodes)
        record=dict(id=idx,indices=indices,depth=depth,parent=parent,children=[],singletons=[]);nodes.append(record)
        remaining=set(indices)
        while remaining:
            i=min(remaining);group=sorted(j for j in remaining if j==i or valuation(roots[j]-roots[i],p)>depth);remaining.difference_update(group)
            if len(group)==1:record['singletons'].append(group[0])
            else:record['children'].append(node(group,idx))
        return idx
    node(list(range(m)));vertices=[];lifts={};edges=[]
    for r in nodes:
        odd=sum(len(nodes[k]['indices'])%2 for k in r['children'])+len(r['singletons'])
        odd+=(m%2 if r['parent'] is None else len(r['indices'])%2)
        if odd%2:raise AssertionError('odd number of branch flags')
        lifts[r['id']]=[]
        for sheet in range(1 if odd else 2):
            idx=len(vertices);lifts[r['id']].append(idx)
            vertices.append(dict(id=idx,cluster=r['id'],sheet=sheet,genus=max(0,(odd-2)//2),odd_branch_flags=odd))
    for r in nodes[1:]:
        parent=nodes[r['parent']];odd=len(r['indices'])%2;length=Q(r['depth']-parent['depth'],2 if odd else 1)
        for sheet in range(1 if odd else 2):
            a=lifts[parent['id']][sheet%len(lifts[parent['id']])];b=lifts[r['id']][sheet%len(lifts[r['id']])]
            edges.append(dict(source=a,target=b,length=str(length),ramified=bool(odd)))
    # Every branch-cover graph must be connected and recover the source genus.
    reached={0}
    while True:
        nxt=reached|{e['target'] for e in edges if e['source'] in reached}|{e['source'] for e in edges if e['target'] in reached}
        if nxt==reached:break
        reached=nxt
    b1=len(edges)-len(vertices)+1;genus=sum(v['genus'] for v in vertices)+b1
    if len(reached)!=len(vertices) or genus!=(m-1)//2:raise AssertionError('cluster double-cover genus replay failed')
    return dict(schema='pp-split-root-cluster-geometry/1',p=p,roots=list(map(str,roots)),clusters=nodes,vertices=vertices,edges=edges,
        graph_cycle_rank=b1,total_genus=genus,genus_identity_checked=True,
        scope='geometric semistable marked double-cover graph after sufficient tame base change; edge lengths may be half-integral; no component twist, minimal regular model or arithmetic Frobenius action claimed')


def simultaneous_quadratic_nodes(centres,order=4):
    """Exact root jets for product ((x-a)^2-t); t=r^2 resolves all nodes."""
    centres=list(map(Q,centres))
    if not 1<=len(centres)<=4 or len(set(centres))!=len(centres) or type(order) is not int or not 2<=order<=24:raise ValueError('1 through 4 distinct centres and order 2 through 24 required')
    jets=[[a,Q(sign)]+[Q(0)]*(order-1) for a in centres for sign in (1,-1)]
    contacts=[[None if i==j else next(k for k in range(order+1) if jets[i][k]!=jets[j][k]) for j in range(len(jets))] for i in range(len(jets))]
    return dict(schema='pp-simultaneous-quadratic-node-jets/1',parameter='t=r^2',centres=list(map(str,centres)),root_jets=[list(map(str,v)) for v in jets],contact_orders=contacts,
        exact_factor_identity='(x-a-r)(x-a+r)=(x-a)^2-t',branches_are_exact=True,scope='entire product-of-transverse-quadratics family; not arbitrary Puiseux factorization')
