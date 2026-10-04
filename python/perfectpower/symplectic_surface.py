"""Integral tree/cotree homology and symplectic reduction on oriented surfaces.

Combinatorial certificates use exact integers; no analytic integration claim.
"""
from collections import deque
from .integer_lifting import smith_certificate,_multiply,_identity
from .exact_linear import inverse


def transpose(a):return [list(x) for x in zip(*a)]
def pairing(a,b):return _multiply(_multiply(transpose(b),a),b)


def symplectic_reduce(omega):
    n=len(omega)
    if n%2 or any(len(r)!=n for r in omega):raise ValueError('even square form required')
    if any(omega[i][j]!=-omega[j][i] for i in range(n) for j in range(n)):raise ValueError('alternating form required')
    transcripts=[]
    def reduce(a):
        m=len(a)
        if not m:return []
        # Smith of the first row constructs a vector with unit pairing.
        row=smith_certificate([a[0]]);transcripts.append(row)
        if row['smith_factors']!=[1]:raise ValueError('form is not unimodular')
        b=[r[0] for r in row['right']]
        # D=U A V, hence compensate the one-dimensional row sign.
        b=[x*row['left'][0][0] for x in b]
        e=[int(i==0) for i in range(m)]
        constraints=[a[0],[sum(b[i]*a[i][j] for i in range(m)) for j in range(m)]]
        cert=smith_certificate(constraints);transcripts.append(cert)
        if cert['smith_factors']!=[1,1]:raise ValueError('pair does not split integrally')
        k=[r[2:] for r in cert['right']]
        rest=reduce(pairing(a,k)) if m>2 else []
        tail=_multiply(k,rest) if m>2 else [[] for _ in range(m)]
        return [[e[i],b[i]]+tail[i] for i in range(m)]
    s=reduce(omega)
    order=list(range(0,n,2))+list(range(1,n,2));s=[[r[j] for j in order] for r in s]
    g=n//2;j=[[int(k==i+g)-int(i==k+g) for k in range(n)] for i in range(n)]
    if pairing(omega,s)!=j:raise AssertionError('symplectic equality failed')
    inv=inverse(s)
    if any(x.denominator!=1 for r in inv for x in r):raise AssertionError('nonintegral inverse')
    return {'basis_columns':s,'inverse_basis':[[int(x) for x in r] for r in inv],
            'standard_intersection':j,'smith_transcripts':transcripts}


def surface_basis(mesh):
    if len(mesh['triangles'])!=len(mesh['face_orientation_signs']) or any(s not in (-1,1) for s in mesh['face_orientation_signs']):raise ValueError('face orientations required')
    triangles=[]
    for t,sign in zip(mesh['triangles'],mesh['face_orientation_signs']):
        a,b,c=t;triangles.append((a,b,c) if sign==1 else (a,c,b))
    half={};edges={}
    for f,t in enumerate(triangles):
        for k in range(3):
            a,b=t[k],t[(k+1)%3]
            if (a,b) in half:raise ValueError('inconsistent oriented halfedges')
            half[a,b]=(f,k);edges.setdefault(tuple(sorted((a,b))),[]).append(f)
    if any(len(v)!=2 for v in edges.values()) or any((b,a) not in half for a,b in half):raise ValueError('closed oriented manifold required')
    # An edge-manifold can still have pinched vertices: check every link.
    links=[{} for _ in range(mesh['vertices'])]
    for t in triangles:
        if len(set(t))!=3 or any(type(v) is not int or not 0<=v<mesh['vertices'] for v in t):raise ValueError('invalid triangle vertices')
        for k,v in enumerate(t):
            a,b=t[(k+1)%3],t[(k+2)%3]
            links[v].setdefault(a,[]).append(b);links[v].setdefault(b,[]).append(a)
    for link in links:
        if not link or any(len(v)!=2 for v in link.values()):raise ValueError('nonmanifold vertex link')
        seen=set();todo=[next(iter(link))]
        while todo:
            v=todo.pop()
            if v not in seen:seen.add(v);todo.extend(link[v])
        if len(seen)!=len(link):raise ValueError('pinched vertex link')
    def spanning(count,adj):
        seen={0};tree=set();queue=deque([0])
        while queue:
            v=queue.popleft()
            for w,e in sorted(adj[v]):
                if w not in seen:seen.add(w);tree.add(e);queue.append(w)
        if len(seen)!=count:raise ValueError('disconnected tree graph')
        return tree
    adj=[[] for _ in range(mesh['vertices'])]
    for e in edges:
        a,b=e;adj[a].append((b,e));adj[b].append((a,e))
    primal=spanning(len(adj),adj)
    dualadj=[[] for _ in triangles]
    for e,(a,b) in edges.items():
        if e not in primal:dualadj[a].append((b,e));dualadj[b].append((a,e))
    dual=spanning(len(triangles),dualadj)
    handles=sorted(set(edges)-primal-dual)
    chi=mesh['vertices']-len(edges)+len(triangles);g=(2-chi)//2
    if len(handles)!=2*g:raise ValueError('tree/cotree genus mismatch')
    def successor(h):
        f,k=half[h];t=triangles[f];h=(t[(k+1)%3],t[(k+2)%3])
        budget=len(half)
        while tuple(sorted(h)) in dual:
            budget-=1
            if budget<0:raise ValueError('boundary traversal failed')
            f,k=half[h[1],h[0]];t=triangles[f];h=(t[(k+1)%3],t[(k+2)%3])
        return h
    boundary={h for h in half if tuple(sorted(h)) not in dual}
    start=min(boundary);h=start;walk=[]
    while True:
        walk.append(h);h=successor(h)
        if h==start:break
        if len(walk)>len(boundary):raise ValueError('nonclosing polygon')
    if set(walk)!=boundary:raise ValueError('multiple polygon boundaries')
    ids={e:i+1 for i,e in enumerate(handles)}
    word=[ids[tuple(sorted(h))]*(1 if h[0]<h[1] else -1) for h in walk if tuple(sorted(h)) in ids]
    n=len(handles);omega=[[0]*n for _ in range(n)]
    for i in range(n):
        p=word.index(i+1);q=word.index(-i-1)
        inside=lambda t:0<(t-p)%len(word)<(q-p)%len(word)
        for j in range(n):
            if i!=j:omega[i][j]=int(inside(word.index(j+1)))-int(inside(word.index(-j-1)))
    reduction=symplectic_reduce(omega) if n else {'basis_columns':[],'inverse_basis':[],'standard_intersection':[],'smith_transcripts':[]}
    # Explicit based dual loops crossing each handle from its right to left face.
    parent={0:(None,None)};queue=deque([0])
    while queue:
        f=queue.popleft()
        for v,e in dualadj[f]:
            if e in dual and v not in parent:parent[v]=(f,e);queue.append(v)
    def path(v):
        out=[]
        while v:
            p,e=parent[v];out.append([p,v,list(e)]);v=p
        return list(reversed(out))
    cycles=[]
    for a,b in handles:
        left=half[a,b][0];right=half[b,a][0]
        cycles.append(path(right)+[[right,left,[a,b]]]+[[v,u,e] for u,v,e in reversed(path(left))])
    return {'schema':'pp-integral-surface-symplectic-basis/1','genus':g,'euler':chi,
        'primal_tree':[list(e) for e in sorted(primal)],'dual_tree':[list(e) for e in sorted(dual)],
        'handle_edges':[list(e) for e in handles],'polygon_word':word,'dual_generator_cycles':cycles,
        'intersection_matrix':omega,**reduction,'analytic_periods_computed':False,
        'scope':'Exact integral combinatorics on the supplied oriented triangulation; no smooth metric or analytic quadrature certification.'}


def normalize_periods(generator_periods,basis):
    """Normalize supplied integrals in the certified dual-generator cycle order.

    This checks numerical Riemann conditions; it does not establish that caller
    supplied values actually are analytic integrals over the recorded cycles.
    """
    import numpy as np
    g=basis['genus']
    if g<1:raise ValueError('positive genus required')
    p=np.asarray(generator_periods,dtype=complex)
    if p.shape!=(g,2*g) or not np.isfinite(p).all():raise ValueError('finite g by 2g period array required')
    s=np.asarray(basis['basis_columns'],dtype=int)
    if pairing(basis['intersection_matrix'],basis['basis_columns'])!=basis['standard_intersection']:raise ValueError('invalid basis')
    normalized=p@s;a=normalized[:,:g];b=normalized[:,g:]
    tau=np.linalg.solve(a,b)
    symmetry=float(np.max(np.abs(tau-tau.T)))
    eig=np.linalg.eigvalsh((tau.imag+tau.imag.T)/2)
    encode=lambda x:[[[float(z.real),float(z.imag)] for z in row] for row in x]
    return {'A':encode(a),'B':encode(b),'tau':encode(tau),'symmetry_residual':symmetry,
            'imaginary_part_eigenvalues':list(map(float,eig)),
            'positive_imaginary_part':bool(np.all(eig>0)),
            'analytic_integrals_certified':False,'quadrature_error_certified':False,
            'input_contract':'Supplied periods must be integrals of the same ordered holomorphic forms over dual_generator_cycles.'}
