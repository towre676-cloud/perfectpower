"""Rational incidence, polygon structure and congruence inspired by Belyaev.

This is a Euclidean rational-coordinate implementation, not a model of every
Hilbert continuity axiom. Floats are rejected. No hyperbolic metric is inferred.
"""
from fractions import Fraction as Q
from math import gcd,lcm
from .euclid_geometry import point,rational,encode,sub,dot,cross,orientation,on_segment,segment_intersection
from .divisor_square import Budget,WorkLimit


def between(a,b,c,*,strict=True):
    a,b,c=map(point,(a,b,c))
    if type(strict) is not bool:raise ValueError('boolean strict required')
    return on_segment(b,a,c) and (not strict or (a!=c and b not in (a,c)))


def line_through(a,b):
    a,b=map(point,(a,b))
    if a==b:raise ValueError('distinct points determine a line')
    values=[a[1]-b[1],b[0]-a[0],cross(a,b)]
    denominator=lcm(*(q.denominator for q in values))
    integers=[int(v*denominator) for v in values];factor=gcd(*integers)
    integers=[v//factor for v in integers]
    if next(v for v in integers if v)<0:integers=[-v for v in integers]
    return integers


def meet_lines(first,second):
    def checked(line):
        if len(line)!=3:raise ValueError('three line coefficients required')
        a,b,c=map(rational,line)
        if not a and not b:raise ValueError('nonzero line normal required')
        return a,b,c
    a,b,c=checked(first);d,e,f=checked(second);den=a*e-b*d
    if den:return {'kind':'POINT','point':encode(((b*f-c*e)/den,(c*d-a*f)/den))}
    return {'kind':'COINCIDENT' if a*f==c*d and b*f==c*e else 'PARALLEL','point':None}


def polygon_vertices(vertices):
    vertices=list(map(point,vertices))
    if len(vertices)>1 and vertices[0]==vertices[-1]:vertices.pop()
    if len(vertices)<3:raise ValueError('at least three polygon vertices required')
    return vertices


def signed_area2(vertices):
    return sum((cross(a,b) for a,b in zip(vertices,vertices[1:]+vertices[:1])),Q(0))


def polygon_structure(vertices,*,work_limit=100000):
    p=polygon_vertices(vertices);budget=Budget(work_limit);issues=[];n=len(p)
    if len(set(p))!=n:issues.append({'kind':'REPEATED_VERTEX'})
    edges=list(zip(p,p[1:]+p[:1]))
    for i,(a,b) in enumerate(edges):
        if a==b:issues.append({'kind':'ZERO_EDGE','edge':i})
        for j in range(i+1,n):
            budget.spend();hit=segment_intersection(a,b,*edges[j])
            if hit['kind']=='DISJOINT':continue
            adjacent=j==i+1 or (i==0 and j==n-1)
            common=p[j] if j==i+1 else p[0]
            if adjacent and hit=={'kind':'TOUCH','points':[encode(common)]}:continue
            issues.append({'kind':'SIDE_INTERSECTION','edges':[i,j],'intersection':hit})
    area2=signed_area2(p)
    if area2==0:issues.append({'kind':'ZERO_AREA'})
    return {'schema':'pp-rational-polygon-structure/1','vertices':[encode(v) for v in p],
            'simple':not issues,'issues':issues,'signed_area':str(area2/2),
            'orientation':'CCW' if area2>0 else 'CW' if area2<0 else 'DEGENERATE',
            'work_used':budget.used,'scope':'simple closed rational Euclidean polygon; adjacent endpoint contact allowed'}


def _simple(vertices,budget):
    p=polygon_vertices(vertices)
    # Charge the exact number of side-pair tests to a shared caller budget.
    for _ in range(len(p)*(len(p)-1)//2):budget.spend()
    packet=polygon_structure(p,work_limit=max(1,len(p)*(len(p)-1)//2))
    if not packet['simple']:raise ValueError('simple nonzero-area polygon required')
    return p


def locate_point(vertices,p,*,work_limit=100000):
    polygon=_simple(vertices,Budget(work_limit));p=point(p)
    return _locate(polygon,p)


def _locate(polygon,p):
    if any(on_segment(p,a,b) for a,b in zip(polygon,polygon[1:]+polygon[:1])):return 'BOUNDARY'
    winding=0
    for a,b in zip(polygon,polygon[1:]+polygon[:1]):
        if a[1]<=p[1]<b[1] and cross(sub(b,a),sub(p,a))>0:winding+=1
        elif b[1]<=p[1]<a[1] and cross(sub(b,a),sub(p,a))<0:winding-=1
    return 'INSIDE' if winding else 'OUTSIDE'


def triangle_contains(a,b,c,p,*,boundary=True):
    a,b,c,p=map(point,(a,b,c,p))
    turn=orientation(a,b,c)
    if not turn:raise ValueError('nondegenerate triangle required')
    signs=[orientation(a,b,p),orientation(b,c,p),orientation(c,a,p)]
    return all(s*turn>=0 if boundary else s*turn>0 for s in signs)


def triangulate(vertices,*,work_limit=100000):
    budget=Budget(work_limit);original=_simple(vertices,budget);p=list(original)
    if signed_area2(p)<0:p.reverse()
    removed=[]
    # Strip only redundant collinear points between their neighbours.
    changed=True
    while changed and len(p)>3:
        changed=False
        for i,b in enumerate(p):
            budget.spend();a,c=p[i-1],p[(i+1)%len(p)]
            if between(a,b,c):removed.append(encode(b));p.pop(i);changed=True;break
    normalized=list(p);triangles=[]
    while len(p)>3:
        for i,b in enumerate(p):
            budget.spend();a,c=p[i-1],p[(i+1)%len(p)]
            if orientation(a,b,c)<=0:continue
            blocked=False
            for j,v in enumerate(p):
                if j in (i,(i-1)%len(p),(i+1)%len(p)):continue
                budget.spend()
                if triangle_contains(a,b,c,v):blocked=True;break
            if blocked:continue
            triangles.append([a,b,c]);p.pop(i);break
        else:raise AssertionError('no ear found in a validated simple polygon')
    triangles.append(p)
    areas=[orientation(*t)/2 for t in triangles]
    if any(a<=0 for a in areas) or sum(areas)!=abs(signed_area2(original))/2:
        raise AssertionError('triangulation area replay failed')
    return {'schema':'pp-rational-triangulation/1','vertices':[encode(v) for v in original],
            'normalized_vertices':[encode(v) for v in normalized],
            'removed_collinear_vertices':removed,'triangles':[[encode(v) for v in t] for t in triangles],
            'triangle_areas':[str(a) for a in areas],'area':str(sum(areas)),
            'complete':True,'kernel_checked':False,'work_used':budget.used,
            'scope':'ear decomposition of a simple rational polygon without holes; Python execution tested'}


def polygon_centroid(vertices,*,work_limit=100000):
    p=_simple(vertices,Budget(work_limit));area2=signed_area2(p)
    accum=[Q(0),Q(0)]
    for a,b in zip(p,p[1:]+p[:1]):
        weight=cross(a,b)
        for i in range(2):accum[i]+=(a[i]+b[i])*weight
    return {'area':str(abs(area2)/2),'centroid':encode(tuple(v/(3*area2) for v in accum)),
            'scope':'uniform filled polygon centroid; may lie outside a concave polygon'}


def circumcircle(a,b,c):
    a,b,c=map(point,(a,b,c));u,v=sub(b,a),sub(c,a);den=2*cross(u,v)
    if not den:raise ValueError('three noncollinear points required')
    nu,nv=dot(u,u),dot(v,v)
    offset=((nu*v[1]-nv*u[1])/den,(u[0]*nv-v[0]*nu)/den)
    center=tuple(x+y for x,y in zip(a,offset))
    return {'center':encode(center),'radius_squared':str(dot(offset,offset))}


def incircle(a,b,c,p):
    a,b,c,p=map(point,(a,b,c,p));turn=orientation(a,b,c)
    if not turn:raise ValueError('noncollinear circle sites required')
    u,v,w=sub(a,p),sub(b,p),sub(c,p)
    determinant=dot(u,u)*cross(v,w)-dot(v,v)*cross(u,w)+dot(w,w)*cross(u,v)
    signed=determinant if turn>0 else -determinant
    return {'kind':'INSIDE' if signed>0 else 'OUTSIDE' if signed<0 else 'ON',
            'oriented_determinant':str(determinant),'orientation':str(turn)}


def apply_isometry(transform,p):
    p=point(p);matrix=[[rational(v) for v in row] for row in transform['matrix']];offset=point(transform['translation'])
    if len(matrix)!=2 or any(len(row)!=2 for row in matrix):raise ValueError('2 by 2 matrix required')
    if any(sum(matrix[k][i]*matrix[k][j] for k in range(2))!=(1 if i==j else 0) for i in range(2) for j in range(2)):
        raise ValueError('orthogonal rational matrix required')
    expected='PRESERVING' if matrix[0][0]*matrix[1][1]-matrix[0][1]*matrix[1][0]>0 else 'REVERSING'
    if transform.get('orientation',expected)!=expected:raise ValueError('matrix orientation label mismatch')
    return tuple(dot(row,p)+t for row,t in zip(matrix,offset))


def fit_isometries(source,target):
    source,target=list(map(point,source)),list(map(point,target))
    if len(source)!=len(target) or not source:raise ValueError('equal nonempty labelled point lists required')
    index=next((i for i in range(1,len(source)) if source[i]!=source[0]),None)
    if index is None:
        if any(p!=target[0] for p in target):return {'status':'NOT_CONGRUENT','transforms':[]}
        shift=sub(target[0],source[0])
        return {'status':'UNDERDETERMINED','transforms':[],
                'translation_example':{'matrix':[['1','0'],['0','1']],'translation':encode(shift)},
                'scope':'one distinct source point; infinitely many Euclidean rigid maps remain'}
    u,v=sub(source[index],source[0]),sub(target[index],target[0]);norm=dot(u,u)
    if dot(v,v)!=norm:return {'status':'NOT_CONGRUENT','transforms':[]}
    transforms=[]
    for reflected in (False,True):
        ux,uy=u;vx,vy=v
        if not reflected:
            a,b=dot(u,v)/norm,cross(u,v)/norm;matrix=((a,-b),(b,a))
        else:
            a,b=(ux*vx-uy*vy)/norm,(uy*vx+ux*vy)/norm;matrix=((a,b),(b,-a))
        translation=tuple(v0-dot(row,source[0]) for row,v0 in zip(matrix,target[0]))
        transform={'matrix':[encode(row) for row in matrix],'translation':encode(translation),
                   'orientation':'REVERSING' if reflected else 'PRESERVING'}
        if all(apply_isometry(transform,a)==b for a,b in zip(source,target)):transforms.append(transform)
    return {'status':'CONGRUENT' if transforms else 'NOT_CONGRUENT','transforms':transforms,
            'scope':'all rational Euclidean rigid maps for the supplied labelled points when at least two source points differ'}


def check_triangulation(packet,*,work_limit=100000):
    if packet!=triangulate(packet['vertices'],work_limit=work_limit):raise ValueError('triangulation packet does not replay')
    return True


def voronoi_mesh(sites,box,*,work_limit=1000000,site_pair_limit=10000):
    """Attach exact areas, centroids and triangles to the existing planar cells."""
    from .euclid_geometry import voronoi_cells
    budget=Budget(work_limit);base=voronoi_cells(sites,box,pair_limit=site_pair_limit)
    cells={};seen=set();total=Q(0)
    for name,cell in base['cells'].items():
        budget.spend();p=list(map(point,cell['vertices']))
        if len(p)<3 or signed_area2(p)==0:
            cells[name]={'dimension':-1 if not p else 0 if len(set(p))==1 else 1,
                         'area':'0','centroid':None,'triangles':[]};continue
        remaining=budget.limit-budget.used
        if remaining<1:raise WorkLimit('Voronoi mesh budget exceeded')
        triangles=triangulate(p,work_limit=remaining)
        for _ in range(triangles['work_used']):budget.spend()
        areas=list(map(Q,triangles['triangle_areas']));area=sum(areas)
        centroid=tuple(sum(weight*sum(Q(v[i]) for v in tri)/3 for weight,tri in zip(areas,triangles['triangles']))/area for i in range(2))
        cells[name]={'dimension':2,'area':str(area),'centroid':encode(centroid),'triangles':triangles['triangles']}
        key=tuple(base['sites'][name])
        if key not in seen:total+=area;seen.add(key)
    lo,hi=map(point,box);box_area=(hi[0]-lo[0])*(hi[1]-lo[1])
    if total!=box_area:raise AssertionError('unique-site Voronoi area partition failed')
    return {'schema':'pp-rational-voronoi-mesh/1','voronoi':base,'mesh':cells,
            'unique_cell_area':str(total),'box_area':str(box_area),'work_used':budget.used,
            'kernel_checked':False,'scope':'bounded planar Euclidean cells, including coincident ties and lower-dimensional cells; triangulation execution tested'}


def transport_voronoi(packet,transform):
    """Reuse a canonical cell diagram under a rigid map, including its domain."""
    from .euclid_geometry import voronoi_cells
    if packet!=voronoi_cells(packet['sites'],packet['box']):raise ValueError('source Voronoi packet does not replay')
    apply_isometry(transform,[0,0]);matrix=[[rational(v) for v in row] for row in transform['matrix']]
    translation=point(transform['translation']);lo,hi=map(point,packet['box'])
    corners=[lo,(hi[0],lo[1]),hi,(lo[0],hi[1])];cells={}
    for name,cell in packet['cells'].items():
        inequalities=[]
        for h in cell['inequalities']:
            normal=point(h['normal']);image_normal=tuple(dot(row,normal) for row in matrix)
            inequalities.append({'other':h['other'],'normal':encode(image_normal),
                                 'bound':str(Q(h['bound'])+dot(image_normal,translation)),
                                 'coincident_sites':h['coincident_sites']})
        cells[name]={'vertices':[encode(apply_isometry(transform,p)) for p in cell['vertices']],
                     'inequalities':inequalities,'coincident_ties':cell['coincident_ties']}
    return {'schema':'pp-isometric-voronoi-transport/1','transform':transform,
            'sites':{k:encode(apply_isometry(transform,p)) for k,p in packet['sites'].items()},
            'domain_boundary':[encode(apply_isometry(transform,p)) for p in corners],
            'cells':cells,'kernel_checked':False,
            'scope':'Euclidean cell transport over the transformed original rectangle; resulting domain may be a rotated quadrilateral'}
