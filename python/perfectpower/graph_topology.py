"""Exact graph cycles, rational cellular homology, and planar string winding.

Betti representatives are over Q; integral H1 torsion uses replayable Smith reduction.
Smooth analytic periods are outside this interface.
"""
from fractions import Fraction as Q
from collections import deque
from .exact_linear import rref
from .divisor_square import WorkLimit


def cycle_basis(n, edges):
    """Integral fundamental cycles for a multigraph, including loops."""
    if type(n) is not int or n < 0: raise ValueError('nonnegative vertex count required')
    edges = [list(e) for e in edges]; parent = list(range(n)); adj = [[] for _ in range(n)]; chords = []; tree = []
    def root(v):
        while parent[v]!=v: v=parent[v]
        return v
    for i,e in enumerate(edges):
        if len(e)!=2 or any(type(v) is not int or not 0<=v<n for v in e): raise ValueError('invalid edge')
        a,b=e
        if root(a)!=root(b):
            parent[root(a)]=root(b); tree.append(i); adj[a].append((b,i,1)); adj[b].append((a,i,-1))
        else: chords.append(i)
    cycles=[]
    for i in chords:
        a,b=edges[i]; previous={b:None}; todo=deque([b])
        while todo and a not in previous:
            v=todo.popleft()
            for w,j,sign in adj[v]:
                if w not in previous: previous[w]=(v,j,sign); todo.append(w)
        z=[0]*len(edges); z[i]=1; v=a
        while v!=b:
            u,j,sign=previous[v]; z[j]=sign; v=u
        cycles.append(z)
    boundary=[[0]*len(edges) for _ in range(n)]
    for j,(a,b) in enumerate(edges): boundary[a][j]-=1; boundary[b][j]+=1
    if any(sum(x*y for x,y in zip(row,z)) for row in boundary for z in cycles): raise AssertionError('nonzero cycle boundary')
    return {'edges':edges,'boundary_1':boundary,'tree_edges':tree,'chord_edges':chords,
            'cycles':cycles,'components':len({root(v) for v in range(n)}), 'cycle_rank':len(cycles)}


def cellular_homology(n, edges, face_boundaries, *, matrix_cell_limit=1_000_000):
    """Faces are signed edge-chain rows. Require ∂1∂2=0; compute H1 over Q."""
    edges = list(edges); faces = [list(f) for f in face_boundaries]; m=len(edges)
    if (n+m+len(faces))*(m+len(faces)) > matrix_cell_limit: raise WorkLimit('cellular matrix budget exceeded')
    if any(len(f)!=m or any(type(x) is not int for x in f) for f in faces): raise ValueError('integer edge-chain face boundaries required')
    base=cycle_basis(n,edges); d1=base['boundary_1']
    if any(sum(x*y for x,y in zip(row,f)) for row in d1 for f in faces): raise ValueError('face boundary is not a cycle')
    independent=[]; rank=0
    for f in faces:
        new=len(rref(independent+[f],columns=m)[1])
        if new>rank: independent.append(f); rank=new
    face_rank=rank; representatives=[]
    for z in base['cycles']:
        new=len(rref(independent+[z],columns=m)[1])
        if new>rank: independent.append(z); representatives.append(z); rank=new
    from .integer_lifting import smith_certificate
    coordinates = [[f[chord] for f in faces] for chord in base['chord_edges']]
    for f in faces:
        reconstructed = [sum(f[chord]*z[j] for chord,z in zip(base['chord_edges'],base['cycles'])) for j in range(m)]
        if reconstructed != f: raise AssertionError('integral cycle coordinates do not reconstruct face')
    smith = smith_certificate(coordinates) if coordinates and faces else None
    torsion = [d for d in smith['smith_factors'] if d > 1] if smith else []
    integral = {'free_rank':len(representatives),'torsion_invariant_factors':torsion,
                'face_cycle_coordinates':coordinates,'smith_certificate':smith}
    return {'schema':'pp-cellular-homology/1' ,**base,'face_boundaries':faces,
            'boundary_2':[[f[j] for f in faces] for j in range(m)],
            'betti':[base['components'],len(representatives),len(faces)-face_rank],
            'homology_representatives':representatives,'coefficient_field':'Q',
            'integral_h1':integral,'torsion_computed':True,'analytic_periods_computed':False}


def mesh_homology(mesh, **options):
    """Adapt the repo's triangular mesh; vertex IDs must be contiguous."""
    triangles=mesh['triangles']; vertices=sorted({v for t in triangles for v in t})
    n=max(vertices,default=-1)+1
    if vertices!=list(range(n)) or any(len(t)!=3 or len(set(t))!=3 for t in triangles): raise ValueError('contiguous nondegenerate triangular mesh required')
    edges=sorted({tuple(sorted((t[i],t[(i+1)%3]))) for t in triangles for i in range(3)})
    ix={e:j for j,e in enumerate(edges)}; faces=[]
    signs=mesh.get('face_orientation_signs',[1]*len(triangles))
    if len(signs)!=len(triangles) or any(type(s) is not int or s not in (-1,1) for s in signs): raise ValueError('invalid orientations')
    for t,sign in zip(triangles,signs):
        f=[0]*len(edges)
        for i in range(3):
            a,b=t[i],t[(i+1)%3]; f[ix[tuple(sorted((a,b)))]]+=sign*(1 if a<b else -1)
        faces.append(f)
    return cellular_homology(n,edges,faces,**options)


def winding_number(path, point):
    """Exact closed polygon winding about a point, with contact rejection.

    A nonzero winding is topological enclosure, not a physical grasp certificate.
    """
    def coordinate(x):
        if type(x) not in (int,Q,str): raise ValueError('exact rational coordinates required')
        return Q(x)
    def xy(p):
        if len(p)!=2: raise ValueError('two coordinates required')
        return tuple(map(coordinate,p))
    path=list(map(xy,path)); p=xy(point)
    if len(path)<4 or path[0]!=path[-1]: raise ValueError('closed polygon with at least three segments required')
    winding=0
    for a,b in zip(path,path[1:]):
        cross=(b[0]-a[0])*(p[1]-a[1])-(b[1]-a[1])*(p[0]-a[0])
        if cross==0 and min(a[0],b[0])<=p[0]<=max(a[0],b[0]) and min(a[1],b[1])<=p[1]<=max(a[1],b[1]):
            raise ValueError('point contacts string segment; winding undefined')
        if a[1]<=p[1]<b[1] and cross>0: winding+=1
        if b[1]<=p[1]<a[1] and cross<0: winding-=1
    return winding


def string_enclosures(path, objects):
    return {'schema':'pp-string-enclosures/1','windings':{name:winding_number(path,p) for name,p in objects.items()},
            'scope':'closed planar rational polygon around supplied point objects; physical contact and grasp not inferred'}
