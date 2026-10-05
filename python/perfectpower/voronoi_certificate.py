"""Producer-independent rational checker for adaptive polyhedral Voronoi packets.

The checker validates finite metric data, explicit paths, affine lower fields and
an exact subdivision tree. Smooth comparison parameters are assumptions, never
inferred from a floating mesh. Python acceptance is not a Lean proof term.
"""
from fractions import Fraction as Q
from heapq import heappush, heappop
from math import isqrt

UNIT = tuple(tuple(Q(int(j == k)) for j in range(3)) for k in range(3))


def children(v):
    a,b,c=v
    ab=tuple((x+y)/2 for x,y in zip(a,b))
    bc=tuple((x+y)/2 for x,y in zip(b,c))
    ca=tuple((x+y)/2 for x,y in zip(c,a))
    return ((a,ab,ca),(ab,b,bc),(ca,bc,c),(ab,bc,ca))


def _ceil_root(q):
    assert q >= 0
    scale=1 << 48
    n=(q.numerator*scale*scale+q.denominator-1)//q.denominator
    k=isqrt(n)
    return Q(k+(k*k < n),scale)


def _round_bound(value, upward, bits=32):
    scale=1 << bits
    value=Q(value)*scale
    integer=-((-value.numerator)//value.denominator) if upward else value.numerator//value.denominator
    return str(Q(integer,scale))


def _metric(mesh):
    n=mesh['vertices']
    if type(n) is not int or n < 3: raise ValueError('vertex count')
    edges={}
    for a,b,length in mesh['edge_lengths']:
        if any(type(v) is not int or not 0 <= v < n for v in (a,b)) or a == b:
            raise ValueError('edge indices')
        key=tuple(sorted((a,b)))
        length=Q(str(length))
        if key in edges or length <= 0: raise ValueError('edge lengths')
        edges[key]=length
    grams=[]; incidence={}; links=[{} for _ in range(n)]
    seen=set()
    signs=mesh.get('face_orientation_signs',[1]*len(mesh['triangles']))
    if len(signs)!=len(mesh['triangles']) or any(type(s) is not int or s not in (-1,1) for s in signs):
        raise ValueError('orientation signs')
    for tri,sign in zip(mesh['triangles'],signs):
        if len(tri)!=3 or any(type(v) is not int or not 0 <= v < n for v in tri):
            raise ValueError('face indices')
        a,b,c=tri
        if len(set(tri))!=3 or tuple(sorted(tri)) in seen: raise ValueError('face duplicate')
        seen.add(tuple(sorted(tri)))
        for u,v in ((a,b),(b,c),(c,a)):
            key=tuple(sorted((u,v))); incidence.setdefault(key,[]).append((u,v) if sign==1 else (v,u))
        for center,u,v in ((a,b,c),(b,c,a),(c,a,b)):
            links[center].setdefault(u,set()).add(v); links[center].setdefault(v,set()).add(u)
        A=edges[tuple(sorted((a,b)))]**2; B=edges[tuple(sorted((a,c)))]**2
        C=(A+B-edges[tuple(sorted((b,c)))]**2)/2
        if A*B-C*C <= 0: raise ValueError('Gram determinant')
        grams.append((A,C,B))
    if set(incidence)!=set(edges): raise ValueError('unused/missing edges')
    if any(len(v)!=2 or v[0]!=v[1][::-1] for v in incidence.values()):
        raise ValueError('closed oriented edge gluing')
    for link in links:
        if not link or any(len(v)!=2 for v in link.values()): raise ValueError('vertex link')
        todo=[next(iter(link))]; reached=set()
        while todo:
            v=todo.pop()
            if v not in reached: reached.add(v); todo.extend(link[v]-reached)
        if reached != set(link): raise ValueError('disconnected vertex link')
    adj=[[] for _ in range(n)]
    for (a,b),length in edges.items(): adj[a].append((b,length));adj[b].append((a,length))
    reached={0};todo=[0]
    while todo:
        for b,_ in adj[todo.pop()]:
            if b not in reached: reached.add(b);todo.append(b)
    if len(reached)!=n: raise ValueError('disconnected surface')
    return edges,grams,adj


def produce(mesh, sites, fields, depth=2):
    """Use numerical proposals; retain exact fields and actual edge-path witnesses."""
    from .certified_voronoi import boundary_enclosure, prepare
    edges,grams,adj=_metric(mesh)
    old=boundary_enclosure(mesh,sites,fields,depth)
    _,_,normalized,_=prepare(mesh,fields)
    paths=[]
    for site in sites:
        distances=[None]*mesh['vertices']; prev=[None]*mesh['vertices']
        distances[site]=Q(0); heap=[(Q(0),site)]
        while heap:
            distance,a=heappop(heap)
            if distance!=distances[a]: continue
            for b,length in adj[a]:
                candidate=distance+length
                if distances[b] is None or candidate < distances[b]:
                    distances[b]=candidate;prev[b]=a;heappush(heap,(candidate,b))
        rows=[]
        for v in range(mesh['vertices']):
            path=[v]
            while path[-1]!=site: path.append(prev[path[-1]])
            rows.append(path[::-1])
        paths.append(rows)
    # Recover the producer's traversal as explicit prefix-free leaf addresses.
    pieces=iter(old['pieces']); current=next(pieces,None); addressed=[]
    def visit(face,verts,address):
        nonlocal current
        if current is not None and current['face']==face and tuple(tuple(Q(x) for x in v) for v in current['barycentric_triangle'])==verts:
            addressed.append(dict(current,address=address));current=next(pieces,None)
        else:
            if len(address)>=depth: raise ValueError('producer partition')
            for j,child in enumerate(children(verts)): visit(face,child,address+[j])
    for face in range(len(mesh['triangles'])): visit(face,UNIT,[])
    if current is not None: raise ValueError('extra producer pieces')
    # Compact outward bounds reduce packet size without changing semantics.
    for piece in addressed:
        piece['center_upper']=[_round_bound(x,True) for x in piece['center_upper']]
        piece['center_lower']=[_round_bound(x,False) for x in piece['center_lower']]
        piece['radius_upper']=_round_bound(piece['radius_upper'],True)
        if piece['site'] is not None:
            i=sites.index(piece['site']); upper=list(map(Q,piece['center_upper'])); lower=list(map(Q,piece['center_lower']))
            if not all(i==j or upper[i]+2*Q(piece['radius_upper'])<lower[j] for j in range(len(sites))):
                piece['site']=None
    packet={'schema':'pp-voronoi-witness/1','sites':list(sites),'depth':depth,
            'fields':[[str(x) for x in f] for f in normalized], 'paths':paths,
            'pieces':addressed,'smooth_curve_metric_certified':False,
            'scope':'Closed connected oriented rational polyhedral surface; unresolved leaves enclose all distance ties.'}
    if not verify(mesh,packet): raise ValueError('certificate construction failed')
    return packet


def _check(mesh,packet):
    if packet['schema']!='pp-voronoi-witness/1' or packet['smooth_curve_metric_certified'] is not False:
        raise ValueError('scope')
    edges,grams,_=_metric(mesh); n=mesh['vertices']
    sites=packet['sites']; depth=packet['depth']
    if type(depth) is not int or not 0<=depth<=8: raise ValueError('depth')
    if len(sites)<2 or any(type(s) is not int or not 0<=s<n for s in sites) or len(set(sites))!=len(sites):
        raise ValueError('sites')
    fields=[[Q(x) for x in row] for row in packet['fields']]
    for f in fields:
        if len(f)!=n: raise ValueError('field dimension')
        for (a,b,c),(A,C,B) in zip(mesh['triangles'],grams):
            u=f[b]-f[a];v=f[c]-f[a]
            if B*u*u-2*C*u*v+A*v*v > A*B-C*C: raise ValueError('gradient')
    if len(packet['paths'])!=len(sites): raise ValueError('path rows')
    costs=[]
    for site,rows in zip(sites,packet['paths']):
        if len(rows)!=n: raise ValueError('path columns')
        rowcost=[]
        for target,path in enumerate(rows):
            if not path or path[0]!=site or path[-1]!=target or len(path)>n:
                raise ValueError('path endpoints/budget')
            if any(type(v) is not int or not 0<=v<n for v in path): raise ValueError('path vertex')
            rowcost.append(sum((edges[tuple(sorted((a,b)))] for a,b in zip(path,path[1:])),Q(0)))
        costs.append(rowcost)
    leaves={}
    for piece in packet['pieces']:
        face=piece['face'];address=piece['address']
        if type(face) is not int or not 0<=face<len(grams): raise ValueError('face')
        if len(address)>depth or any(type(j) is not int or not 0<=j<4 for j in address): raise ValueError('address')
        key=(face,tuple(address))
        if key in leaves: raise ValueError('duplicate leaf')
        verts=UNIT
        for j in address: verts=children(verts)[j]
        if tuple(tuple(Q(x) for x in row) for row in piece['barycentric_triangle'])!=verts:
            raise ValueError('patch vertices')
        if Q(piece['face_area_fraction'])!=Q(1,4**len(address)): raise ValueError('area')
        A,C,B=grams[face]; tri=mesh['triangles'][face]
        def length(p,q):
            u=p[1]-q[1];v=p[2]-q[2]
            return _ceil_root(A*u*u+2*C*u*v+B*v*v)
        center=tuple(sum(v[k] for v in verts)/3 for k in range(3))
        radius=Q(piece['radius_upper'])
        if radius < max(length(center,v) for v in verts): raise ValueError('radius')
        upper=[Q(x) for x in piece['center_upper']];lower=[Q(x) for x in piece['center_lower']]
        if len(upper)!=len(sites) or len(lower)!=len(sites): raise ValueError('bounds dimension')
        values=[sum(center[k]*f[tri[k]] for k in range(3)) for f in fields]
        for i,site in enumerate(sites):
            pathbound=min(costs[i][tri[k]]+length(center,UNIT[k]) for k in range(3))
            fieldbound=max([Q(0)]+[abs(v-f[site]) for v,f in zip(values,fields)])
            if upper[i]<pathbound or lower[i]<0 or lower[i]>fieldbound: raise ValueError('distance bounds')
        winner=piece['site']
        if winner is not None:
            if type(winner) is not int or winner not in sites: raise ValueError('winner')
            i=sites.index(winner)
            if not all(i==j or upper[i]+2*radius<lower[j] for j in range(len(sites))):
                raise ValueError('separation')
        leaves[key]=piece
    # A trie establishes exact coverage, not merely a matching total area.
    def cover(face,address):
        if (face,address) in leaves: return 1
        if len(address)>=depth: raise ValueError('coverage hole')
        return sum(cover(face,address+(j,)) for j in range(4))
    consumed=sum(cover(face,()) for face in range(len(grams)))
    if consumed!=len(leaves): raise ValueError('overlapping descendants')
    return True


def verify(mesh,packet):
    """Check witnesses without invoking producer, heat solver or Dijkstra."""
    try: return _check(mesh,packet)
    except (KeyError,ValueError,TypeError,ZeroDivisionError,IndexError,AssertionError,OverflowError): return False


def transfer_piece(piece, lower_scale, upper_scale):
    """Conditional transfer: l*d_mesh <= d_smooth <= u*d_mesh globally.

    Returned classifications have that explicit hypothesis. Nothing here proves
    a particular analytic curve satisfies it, even if l=u=1 is supplied.
    """
    l,u=Q(lower_scale),Q(upper_scale)
    if not 0<l<=u: raise ValueError('positive ordered global comparison factors')
    upper=[u*Q(x) for x in piece['center_upper']]
    lower=[l*Q(x) for x in piece['center_lower']]
    radius=u*Q(piece['radius_upper'])
    winner=next((i for i in range(len(upper)) if all(i==j or upper[i]+2*radius<lower[j] for j in range(len(upper)))),None)
    return {'schema':'pp-conditional-metric-transfer/1','winner_index':winner,
            'lower_scale':str(l),'upper_scale':str(u),'radius_upper':str(radius),
            'center_upper':list(map(str,upper)),'center_lower':list(map(str,lower)),
            'comparison_proved':False,'claim':'Valid only under the stated global distance comparison.'}


class SurfaceSpace:
    """Validate once, then reuse exact distance witnesses at arbitrary face points.

    This represents the supplied polyhedral surface, not the original smooth
    curve. Returned dictionaries cannot mutate the retained compiled witnesses.
    """
    def __init__(self,mesh,packet):
        if not verify(mesh,packet): raise ValueError('invalid Voronoi witness packet')
        edges,grams,_=_metric(mesh)
        self._triangles=tuple(tuple(t) for t in mesh['triangles'])
        self._grams=tuple(grams)
        self._sites=tuple(packet['sites'])
        self._fields=tuple(tuple(Q(x) for x in row) for row in packet['fields'])
        self._costs=tuple(tuple(sum((edges[tuple(sorted((a,b)))] for a,b in zip(path,path[1:])),Q(0))
                                for path in rows) for rows in packet['paths'])
        self._queries=0

    def point(self,face,barycentric):
        if type(face) is not int or not 0<=face<len(self._grams): raise ValueError('face index')
        p=tuple(Q(x) for x in barycentric)
        if len(p)!=3 or any(x<0 for x in p) or sum(p)!=1: raise ValueError('barycentric point')
        A,C,B=self._grams[face];tri=self._triangles[face]
        def length(q):
            u=p[1]-q[1];v=p[2]-q[2]
            return _ceil_root(A*u*u+2*C*u*v+B*v*v)
        upper=[min(cost[tri[k]]+length(UNIT[k]) for k in range(3)) for cost in self._costs]
        values=[sum(p[k]*f[tri[k]] for k in range(3)) for f in self._fields]
        lower=[max([Q(0)]+[abs(v-f[s]) for v,f in zip(values,self._fields)]) for s in self._sites]
        winner=next((self._sites[i] for i in range(len(self._sites))
                     if all(i==j or upper[i]<lower[j] for j in range(len(self._sites)))),None)
        candidates=[s for s,L in zip(self._sites,lower) if L<=min(upper)]
        self._queries+=1
        return {'schema':'pp-polyhedral-distance-query/1','face':face,'barycentric':list(map(str,p)),
                'sites':list(self._sites),'lower':list(map(str,lower)),'upper':list(map(str,upper)),
                'unique_winner':winner,'possible_nearest_sites':candidates,
                'smooth_curve_metric_certified':False,'kernel_checked':False}

    def statistics(self):
        return {'certificate_checks':1,'point_queries':self._queries,'sites':len(self._sites),'faces':len(self._grams)}
