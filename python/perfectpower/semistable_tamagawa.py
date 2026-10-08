"""Exact component groups from integral semistable metric graphs.

Frobenius must be supplied or derived by the rational-root odd-prime adapter.
A geometric component-group order alone is not the local Tamagawa number.
"""
from fractions import Fraction as Q
from collections import deque
from sympy import Matrix, ZZ, eye
from sympy.matrices.normalforms import smith_normal_form
from .cluster_stable_reduction import PadicDomain, cluster_picture, semistable_graph, analyse, vp, legendre


def component_group(vertices, edges, *, vertex_action=None, edge_action=None):
    """edges=(tail,head,length); edge_action entries=(image,orientation sign)."""
    n=vertices
    if type(n) is not int or n<1:raise ValueError('positive vertex count required')
    E=[(a,b,Q(L)) for a,b,L in edges];m=len(E)
    if any(type(a) is not int or type(b) is not int or not 0<=a<n or not 0<=b<n or L<=0 for a,b,L in E):
        raise ValueError('valid endpoints and positive lengths required')
    tree=[];chords=[];parent=list(range(n))
    def root(v):
        while parent[v]!=v:v=parent[v]
        return v
    adj=[[] for _ in range(n)]
    for j,(a,b,L) in enumerate(E):
        if root(a)==root(b):chords.append(j)
        else:
            parent[root(a)]=root(b);tree.append(j)
            adj[a].append((b,j,1));adj[b].append((a,j,-1))
    if len(tree)!=n-1:raise ValueError('connected graph required')
    cycles=[]
    for j in chords:
        a,b,_=E[j];v=[0]*m;v[j]=1
        q=deque([b]);paths={b:[]}
        while a not in paths:
            x=q.popleft()
            for y,k,sgn in adj[x]:
                if y not in paths:paths[y]=paths[x]+[(k,sgn)];q.append(y)
        for k,sgn in paths[a]:v[k]+=sgn
        cycles.append(v)
    r=len(cycles)
    if (vertex_action is None)!=(edge_action is None):raise ValueError('supply both graph actions or neither')
    supplied=vertex_action is not None
    va=list(range(n)) if vertex_action is None else list(vertex_action)
    ea=[(j,1) for j in range(m)] if edge_action is None else list(edge_action)
    if sorted(va)!=list(range(n)) or len(ea)!=m or sorted(j for j,s in ea)!=list(range(m)):
        raise ValueError('graph action must be bijective')
    for j,(k,sgn) in enumerate(ea):
        a,b,L=E[j];c,d,K=E[k]
        if sgn not in (-1,1) or L!=K or (va[a],va[b])!=((c,d) if sgn==1 else (d,c)):
            raise ValueError('action must preserve oriented incidence and lengths')
    if not r:
        return dict(schema='pp-semistable-component-group/1',cycle_rank=0,cycle_basis=[],monodromy_pairing=[],
                    invariant_factors=[],geometric_order=1,frobenius_cycle_action=[],tamagawa_number=1 if supplied else None,
                    frobenius_supplied=supplied,scope='Semistable metric graph; model and action are hypotheses')
    C=Matrix(cycles);G=C*Matrix.diag(*(L for a,b,L in E))*C.T
    if any(x.q!=1 for x in G):raise ValueError('integral monodromy pairing required over the declared base field')
    if G.det()<=0:raise ArithmeticError('cycle pairing must be positive definite')
    P=Matrix.zeros(m,m)
    for j,(k,sgn) in enumerate(ea):P[j,k]=sgn
    # Chord coordinates identify the integral cycle lattice without rational saturation.
    moved=C*P;F=moved[:,chords]
    if F*C!=moved or abs(F.det())!=1 or F*G*F.T!=G:raise ArithmeticError('invalid integral cycle action')
    # Columns on cycles act by F.T; the dual quotient acts by F^{-1}.
    T=F.inv()
    if any(x.q!=1 for x in T) or any(x.q!=1 for x in G.inv()*T*G):
        raise ArithmeticError('Frobenius does not descend to the discriminant group')
    S=smith_normal_form(G,domain=ZZ)
    factors=[abs(int(S[i,i])) for i in range(r) if abs(int(S[i,i]))>1]
    fixed=smith_normal_form(G.row_join(T-eye(r)),domain=ZZ)
    order=1
    for i in range(r):order*=abs(int(fixed[i,i]))
    return dict(schema='pp-semistable-component-group/1',cycle_rank=r,cycle_basis=cycles,
        monodromy_pairing=[[int(x) for x in row] for row in G.tolist()],invariant_factors=factors,
        geometric_order=int(G.det()),frobenius_cycle_action=[[int(x) for x in row] for row in F.T.tolist()],
        frobenius_dual_action=[[int(x) for x in row] for row in T.tolist()],
        tamagawa_number=order if supplied else None,frobenius_supplied=supplied,
        fixed_group_argument='ker(T-I) and coker(T-I) have equal order on the finite discriminant group; Smith form of [G,T-I]',
        scope='Semistable metric graph; model and action are hypotheses')


def rational_root_tamagawa(p,roots,leading=1):
    """Odd p, rational branch roots, semistable over Q_p; derive sheet signs.

    No extension-field, wild or p=2 inference is made by this adapter.
    """
    if any(isinstance(r,(list,tuple,dict,float)) for r in roots):raise ValueError('exact rational roots required')
    D=PadicDomain(p);result=analyse(D,roots,leading)
    if not result['ddmm_semistable_over_K']:raise ValueError('semistable reduction over the base field required')
    pic=cluster_picture(D,roots,leading);graph=semistable_graph(pic);cl=pic['clusters']
    roots=list(map(Q,roots));signs={};units={}
    for c in cl:
        if not c['even']:continue
        z=roots[c['roots'][0]];value=Q(leading)
        for i,r in enumerate(roots):
            if i not in c['roots']:value*=z-r
        v=vp(value,p)
        if v.denominator!=1 or int(v)%2:raise ValueError('ramified sheet character unsupported')
        unit=value/(Q(p)**int(v));res=unit.numerator*pow(unit.denominator,-1,p)%p
        signs[c['id']]=legendre(res,p);units[str(c['id'])]=dict(valuation=str(v),unit_mod_p=res,sign=signs[c['id']])
    va=[]
    for v in graph['vertices']:
        lifts=graph['lifts'][v['cluster']]
        va.append(lifts[v['sheet']^(signs[v['cluster']]<0)] if len(lifts)==2 else v['id'])
    by={(e['child'],e['lift']):i for i,e in enumerate(graph['edges'])}
    ea=[]
    for e in graph['edges']:
        j=e['lift'] if e['ramified'] else e['lift']^(signs[e['child']]<0)
        ea.append((by[e['child'],j],1))
    out=component_group(len(graph['vertices']),[(e['parent_vertex'],e['child_vertex'],e['length']) for e in graph['edges']],vertex_action=va,edge_action=ea)
    out.update(p=p,roots=list(map(str,roots)),leading=str(leading),sheet_characters=units,
               genus=pic['genus'],conductor_exponent=result['reduction_over_K']['conductor_exponent'],
               scope='Odd-prime semistable rational-root hyperelliptic curve; no wild or dyadic reduction')
    return out
