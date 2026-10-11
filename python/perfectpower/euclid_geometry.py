"""Rational planar contact predicates and bounded Euclidean Voronoi cells."""
from fractions import Fraction as Q
from .divisor_square import WorkLimit


def rational(x):
    if type(x) not in (int,str,Q):raise ValueError('exact integer, Fraction or rational string required')
    return Q(x)


def point(p):
    if len(p)!=2:raise ValueError('two-dimensional point required')
    return tuple(map(rational,p))


def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def orientation(a,b,c):return cross(sub(point(b),point(a)),sub(point(c),point(a)))
def encode(p):return [str(x) for x in p]


def on_segment(p,a,b):
    p,a,b=map(point,(p,a,b))
    return cross(sub(b,a),sub(p,a))==0 and all(min(x,y)<=z<=max(x,y) for z,x,y in zip(p,a,b))


def segment_intersection(a,b,c,d):
    a,b,c,d=map(point,(a,b,c,d));r=sub(b,a);s=sub(d,c);den=cross(r,s)
    if den:
        t=cross(sub(c,a),s)/den;u=cross(sub(c,a),r)/den
        if not 0<=t<=1 or not 0<=u<=1:return {'kind':'DISJOINT','points':[]}
        p=tuple(x+t*y for x,y in zip(a,r))
        return {'kind':'PROPER' if 0<t<1 and 0<u<1 else 'TOUCH','points':[encode(p)]}
    common=sorted({p for p in (a,b,c,d) if on_segment(p,a,b) and on_segment(p,c,d)})
    return {'kind':'OVERLAP' if len(common)>1 else 'TOUCH' if common else 'DISJOINT',
            'points':[encode(p) for p in (common if len(common)<2 else [common[0],common[-1]])]}


def point_segment_distance_squared(p,a,b):
    p,a,b=map(point,(p,a,b));v=sub(b,a);norm=dot(v,v)
    t=max(Q(0),min(Q(1),dot(sub(p,a),v)/norm)) if norm else Q(0)
    nearest=tuple(x+t*y for x,y in zip(a,v));delta=sub(p,nearest)
    return {'squared_distance':str(dot(delta,delta)),'nearest':encode(nearest),'parameter':str(t)}


def string_disk_contacts(path,objects,*,pair_limit=100000):
    path=list(map(point,path))
    if len(path)<2:raise ValueError('at least one string segment required')
    if (len(path)-1)*len(objects)>pair_limit:raise WorkLimit('string contact pair budget exceeded')
    contacts=[]
    for name,obj in sorted(objects.items()):
        center=point(obj['center']);radius=rational(obj['radius'])
        if radius<0:raise ValueError('nonnegative disk radius required')
        for i,(a,b) in enumerate(zip(path,path[1:])):
            receipt=point_segment_distance_squared(center,a,b);dist=Q(receipt['squared_distance'])
            if dist<=radius*radius:
                contacts.append({'object':name,'segment':i,'tangent':dist==radius*radius,**receipt})
    return {'schema':'pp-string-disk-contacts/1','contacts':contacts,
            'scope':'intersection of supplied straight string segments with closed rational disks; dynamics and grasp not inferred'}


def bisector(a,b):
    a,b=map(point,(a,b));normal=tuple(2*x for x in sub(b,a));bound=dot(b,b)-dot(a,a)
    return {'normal':encode(normal),'bound':str(bound),'coincident_sites':a==b}


def _clip(polygon,normal,bound):
    out=[]
    if not polygon:return out
    for a,b in zip(polygon,polygon[1:]+polygon[:1]):
        ha=bound-dot(normal,a);hb=bound-dot(normal,b)
        if ha>=0:out.append(a)
        if (ha<0 and hb>0) or (ha>0 and hb<0):
            t=ha/(ha-hb);out.append(tuple(x+t*(y-x) for x,y in zip(a,b)))
    clean=[]
    for p in out:
        if not clean or p!=clean[-1]:clean.append(p)
    if len(clean)>1 and clean[0]==clean[-1]:clean.pop()
    return clean


def voronoi_cells(sites,box,*,pair_limit=10000):
    if not sites or any(type(name) is not str for name in sites):raise ValueError('named sites required')
    if len(sites)**2>pair_limit:raise WorkLimit('Voronoi site pair budget exceeded')
    sites={name:point(p) for name,p in sorted(sites.items())}
    if len(box)!=2:raise ValueError('box needs lower and upper points')
    lo,hi=map(point,box)
    if any(a>=b for a,b in zip(lo,hi)):raise ValueError('positive rectangular box required')
    corners=[lo,(hi[0],lo[1]),hi,(lo[0],hi[1])];cells={}
    for name,a in sites.items():
        polygon=list(corners);inequalities=[];ties=[]
        for other,b in sites.items():
            if other==name:continue
            h=bisector(a,b);inequalities.append({'other':other,**h})
            if a==b:ties.append(other)
            polygon=_clip(polygon,point(h['normal']),Q(h['bound']))
        if any(dot(point(h['normal']),p)>Q(h['bound']) for h in inequalities for p in polygon):raise AssertionError('clipped vertex violates halfplane')
        cells[name]={'vertices':[encode(p) for p in polygon],'inequalities':inequalities,'coincident_ties':ties}
    return {'schema':'pp-rational-voronoi/1','sites':{k:encode(v) for k,v in sites.items()},
            'box':[encode(lo),encode(hi)],'cells':cells,'scope':'closed Euclidean nearest-site cells clipped to the declared rectangle; all ties retained'}


def nearest_sites(sites,p):
    p=point(p)
    if not sites:raise ValueError('nonempty site set required')
    distances={name:dot(sub(p,point(a)),sub(p,point(a))) for name,a in sites.items()};best=min(distances.values())
    return {'sites':sorted(k for k,v in distances.items() if v==best),'squared_distance':str(best)}


def string_geometry(path,objects,**options):
    """Combine exact contact and winding while retaining the open-string distinction."""
    from .graph_topology import winding_number
    path=list(map(point,path));contacts=string_disk_contacts(path,objects,**options)
    closed=path[0]==path[-1] and len(path)>=4;summary={}
    touching={r['object'] for r in contacts['contacts']}
    for name,obj in sorted(objects.items()):
        center=point(obj['center']);winding=None
        if closed and not any(on_segment(center,a,b) for a,b in zip(path,path[1:])):
            winding=winding_number(path,center)
        summary[name]={'winding':winding,'contacts_disk':name in touching,
                       'whole_disk_topologically_enclosed':closed and winding is not None and winding!=0 and name not in touching}
    return {'schema':'pp-exact-string-geometry/1','closed':closed,'objects':summary,
            'segment_contacts':contacts['contacts'],'scope':'exact supplied polygon and closed disks; physical grasp and dynamics not inferred'}
