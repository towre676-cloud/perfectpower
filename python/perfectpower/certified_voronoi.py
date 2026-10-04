"""Exact distance brackets on rational polyhedral surfaces of any genus.

Heat fields are optional proposals only. Every accepted lower bound is checked
against the exact triangle metric. This does not certify the smooth curve metric.
"""
from fractions import Fraction as Q
from math import isqrt
from heapq import heappush, heappop


def sqrt_upper(q, bits=48):
    q=Q(q)
    if q<0: raise ValueError('negative squared length')
    scale=1<<bits
    n=(q.numerator*scale*scale+q.denominator-1)//q.denominator
    k=isqrt(n)
    if k*k<n:k+=1
    return Q(k,scale)


def prepare(mesh, fields):
    n=mesh['vertices']; edges={tuple(sorted((a,b))):Q(str(l)) for a,b,l in mesh['edge_lengths']}
    if any(l<=0 for l in edges.values()):raise ValueError('positive lengths required')
    grams=[]
    for a,b,c in mesh['triangles']:
        aa=edges[tuple(sorted((a,b)))]**2; bb=edges[tuple(sorted((a,c)))]**2
        cc=(aa+bb-edges[tuple(sorted((b,c)))]**2)/2
        if aa*bb-cc*cc<=0:raise ValueError('degenerate triangle metric')
        grams.append((aa,cc,bb))
    certified=[]; scales=[]
    for field in fields:
        if len(field)!=n:raise ValueError('field dimension')
        f=[Q(str(x)) for x in field]; largest=Q(0)
        for (a,b,c),(aa,cc,bb) in zip(mesh['triangles'],grams):
            u=f[b]-f[a];v=f[c]-f[a]
            largest=max(largest,(bb*u*u-2*cc*u*v+aa*v*v)/(aa*bb-cc*cc))
        scale=max(Q(1),sqrt_upper(largest));scales.append(str(scale));certified.append([x/scale for x in f])
    return edges,grams,certified,scales


def boundary_enclosure(mesh,sites,fields,depth=2):
    """Partition every face into proven cells and an enclosing unresolved band.

    The represented metric has EXACT rational edge lengths obtained from decimal
    input. It need not equal the analytic curve metric or its true geodesic edges.
    """
    if type(depth) is not int or not 0<=depth<=8:raise ValueError('depth must be 0..8')
    if len(set(sites))!=len(sites) or len(sites)<2:raise ValueError('distinct sites required')
    n=mesh['vertices']
    if any(type(s) is not int or not 0<=s<n for s in sites):raise ValueError('site index')
    edges,grams,fs,scales=prepare(mesh,fields)
    adj=[[] for _ in range(n)]
    for (a,b),l in edges.items():adj[a].append((b,l));adj[b].append((a,l))
    paths=[]
    for s in sites:
        dist=[None]*n;dist[s]=Q(0);heap=[(Q(0),s)]
        while heap:
            d,a=heappop(heap)
            if d!=dist[a]:continue
            for b,l in adj[a]:
                t=d+l
                if dist[b] is None or t<dist[b]:dist[b]=t;heappush(heap,(t,b))
        if any(d is None for d in dist):raise ValueError('disconnected surface')
        paths.append(dist)
    pieces=[];proven=Q(0);uncertain=Q(0)
    for fi,(tri,gram) in enumerate(zip(mesh['triangles'],grams)):
        aa,cc,bb=gram
        def length(p,q):
            u=p[1]-q[1];v=p[2]-q[2]
            return sqrt_upper(aa*u*u+2*cc*u*v+bb*v*v)
        def visit(vertices,level,fraction):
            nonlocal proven,uncertain
            p=tuple(sum(v[k] for v in vertices)/3 for k in range(3))
            radius=max(length(p,v) for v in vertices)
            upper=[min(ds[tri[k]]+length(p,tuple(Q(int(j==k)) for j in range(3))) for k in range(3)) for ds in paths]
            values=[sum(p[k]*f[tri[k]] for k in range(3)) for f in fs]
            lower=[max([Q(0)]+[abs(v-f[s]) for v,f in zip(values,fs)]) for s in sites]
            winner=next((i for i in range(len(sites)) if all(i==j or upper[i]+2*radius<lower[j] for j in range(len(sites)))),None)
            if winner is None and level<depth:
                a,b,c=vertices;ab=tuple((x+y)/2 for x,y in zip(a,b));bc=tuple((x+y)/2 for x,y in zip(b,c));ca=tuple((x+y)/2 for x,y in zip(c,a))
                for vs in ((a,ab,ca),(ab,b,bc),(ca,bc,c),(ab,bc,ca)):visit(vs,level+1,fraction/4)
            else:
                pieces.append({'face':fi,'barycentric_triangle':[[str(x) for x in v] for v in vertices],
                    'site':None if winner is None else sites[winner],'face_area_fraction':str(fraction),
                    'center_upper':[str(x) for x in upper],'center_lower':[str(x) for x in lower],'radius_upper':str(radius)})
                if winner is None:uncertain+=fraction
                else:proven+=fraction
        visit(tuple(tuple(Q(int(j==k)) for j in range(3)) for k in range(3)),0,Q(1))
    assert proven+uncertain==len(mesh['triangles'])
    return {'schema':'pp-certified-polyhedral-voronoi/1','sites':sites,'depth':depth,'field_scales':scales,
        'pieces':pieces,'proven_face_fraction_sum':str(proven),'unresolved_face_fraction_sum':str(uncertain),
        'rational_metric_certified':True,'smooth_curve_metric_certified':False,
        'boundary_claim':'Every true Voronoi boundary of the specified rational polyhedral metric lies in the unresolved triangles.',
        'metric_claim':'Exact decimal-rational edge lengths; no claim of a certified comparison with the smooth conformal metric.'}


def verify_enclosure(mesh,fields,certificate):
    """Replay all rational checks and the exact deterministic face partition."""
    try:
        return boundary_enclosure(mesh,certificate['sites'],fields,certificate['depth'])==certificate
    except (KeyError,ValueError,TypeError,ZeroDivisionError):
        return False
