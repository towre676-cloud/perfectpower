"""Continuous intrinsic Voronoi cells on a rectangular conformal flat torus.

The Legendre curve supplies the lattice through rigorously enclosed periods.
Floating polygon predicates operate on the midpoint lattice, not on a mesh graph.
"""
import math
from fractions import Fraction as Q
from .legendre_period_bounds import legendre_period_packet,rational_value


def clip(poly,normal,bound,tol=1e-12):
    out=[]
    for a,b in zip(poly,poly[1:]+poly[:1]):
        va=sum(x*y for x,y in zip(a,normal))-bound;vb=sum(x*y for x,y in zip(b,normal))-bound
        if va<=tol:out.append(a)
        if (va<-tol and vb>tol) or (va>tol and vb<-tol):
            t=va/(va-vb);out.append([a[k]+t*(b[k]-a[k]) for k in range(2)])
    clean=[]
    for p in out:
        if not clean or math.dist(p,clean[-1])>1e-10:clean.append(p)
    if len(clean)>1 and math.dist(clean[0],clean[-1])<1e-10:clean.pop()
    return clean

def area(poly):return abs(sum(a[0]*b[1]-b[0]*a[1] for a,b in zip(poly,poly[1:]+poly[:1])))/2

def distance(a,b,height):
    dx=abs((a[0]-b[0]+.5)%1-.5)
    dy=abs((a[1]-b[1]+height/2)%height-height/2)
    return math.hypot(dx,dy)


def voronoi(height,sites):
    height=float(height)
    if not math.isfinite(height) or height<=0:raise ValueError('positive finite lattice height required')
    sites=[[float(s[0])%1,float(s[1])%height] for s in sites]
    if not sites or len(sites)>100:raise ValueError('one through one hundred sites required')
    if any(not all(map(math.isfinite,s)) for s in sites):raise ValueError('finite sites required')
    if any(distance(a,b,height)<1e-8 for i,a in enumerate(sites) for b in sites[i+1:]):raise ValueError('duplicate quotient sites')
    cells=[]
    for index,s in enumerate(sites):
        # Same-site lattice translates restrict the lifted cell to this box.
        poly=[[s[0]-.5,s[1]-height/2],[s[0]+.5,s[1]-height/2],
              [s[0]+.5,s[1]+height/2],[s[0]-.5,s[1]+height/2]]
        images=[]
        for j,t in enumerate(sites):
            for u in (-1,0,1):
                for v in (-1,0,1):
                    if (j,u,v)==(index,0,0):continue
                    q=[t[0]+u,t[1]+height*v];normal=[q[k]-s[k] for k in range(2)]
                    bound=(sum(x*x for x in q)-sum(x*x for x in s))/2
                    images.append((j,u,v,normal,bound))
                    poly=clip(poly,normal,bound)
        neighbors=[]
        for a,b in zip(poly,poly[1:]+poly[:1]):
            mid=[(a[k]+b[k])/2 for k in range(2)]
            choices=[(abs(sum(x*y for x,y in zip(mid,n))-z),j,u,v) for j,u,v,n,z in images]
            residual,j,u,v=min(choices)
            neighbors.append({'site':j,'lattice_shift':[u,v],'bisector_residual':residual})
        cells.append({'site':index,'lifted_polygon':poly,'area':area(poly),'sides':len(poly),'edge_neighbors':neighbors})
    # Quotient the universal-cover vertices/edges; numerical topology diagnostics
    # reject degenerate inputs rather than claiming every diagram is trivalent.
    scale=1e8
    def key(p):return (round((p[0]%1)*scale)%round(scale),round((p[1]%height)/height*scale)%round(scale))
    vertices=set();edges={}
    for cell in cells:
        poly=cell['lifted_polygon']
        for a,b,nb in zip(poly,poly[1:]+poly[:1],cell['edge_neighbors']):
            ka,kb=key(a),key(b);vertices.update((ka,kb))
            edge=tuple(sorted((ka,kb)))+tuple(sorted((cell['site'],nb['site'])))
            edges.setdefault(edge,[]).append(cell['site'])
    v,e,f=len(vertices),len(edges),len(cells)
    degrees={k:0 for k in vertices}
    for edge in edges:
        degrees[edge[0]]+=1;degrees[edge[1]]+=1
    topology={'vertices':v,'edges':e,'faces':f,'euler':v-e+f,
              'two_face_edge_incidence':all(len(a)==2 for a in edges.values()),
              'trivalent':all(d==3 for d in degrees.values()),'face_charge':sum(6-c['sides'] for c in cells),
              'quantization_relative':1e-8,'certified':False,
              'disk_cell_condition':all(nb['site']!=c['site'] for c in cells for nb in c['edge_neighbors'])}
    return {'height':height,'sites':sites,'cells':cells,'total_cell_area':sum(c['area'] for c in cells),
            'surface_area':height,'area_partition_residual':sum(c['area'] for c in cells)-height,
            'topology_diagnostics':topology,'curvature':0,'metric':'|du|^2 on C/(Z+i*height Z)',
            'distance':'minimum Euclidean distance over lattice translates; continuous geodesic distance',
            'mesh_graph_approximation':False,'floating_predicates':True,
            'scope':'intrinsic cells for rectangular flat torus; arbitrary higher-genus geodesic Voronoi not implemented'}


def legendre_torus(lam,sites=None,terms=256):
    p=legendre_period_packet(lam,terms)
    low,high=map(rational_value,p['tau_imaginary_interval']);height=float((low+high)/2)
    if float(high-low)>1e-8*height:raise ValueError('period enclosure too wide; increase terms')
    if sites is None:
        # Deliberately asymmetric generic points in fractional lattice coordinates.
        sites=[[x,height*y] for x,y in ((.08,.11),(.34,.07),(.72,.16),(.91,.39),(.57,.43),(.21,.36),(.07,.71),(.39,.78),(.76,.72),(.93,.94),(.58,.96),(.24,.96))]
    packet=voronoi(height,sites)
    packet.update(schema='pp-intrinsic-legendre-torus/1',lambda_parameter=p['lambda'],period_enclosure=p,
                  height_interval=p['tau_imaginary_interval'],
                  conformal_metric='|dx/y|^2 / |A|^2, where A=2*pi*F(lambda)',
                  uniformization='u=(integral dx/y)/A modulo Z+tau Z',
                  conformal_to_original_curve=True,
                  rigorous_lattice_enclosure=True,voronoi_topology_certified=False)
    return packet


def legendre_point(lam,u,height,theta_terms=24):
    """Jacobi theta inversion of the actual elliptic-curve uniformization.

u is normalized Abel-Jacobi coordinate relative to x=0. Floating Fourier
summation; residual against the original curve is returned, not certified.
"""
    import cmath
    lam=float(lam);u=complex(u);height=float(height)
    if not 0<lam<1 or height<=0:raise ValueError('smooth floating Legendre parameter and positive height required')
    u=complex(u.real%1,u.imag%height);q=math.exp(-math.pi*height)
    def theta(k,v):
        if k in (1,2):
            return 2*sum(((-1)**n if k==1 else 1)*q**((n+.5)**2)*
                         (cmath.sin((2*n+1)*v) if k==1 else cmath.cos((2*n+1)*v)) for n in range(theta_terms))
        return 1+2*sum(((-1)**n if k==4 else 1)*q**(n*n)*cmath.cos(2*n*v) for n in range(1,theta_terms))
    t2,t3,t4=(theta(k,0) for k in (2,3,4));v=math.pi*u;den=theta(4,v)
    if abs(den)<1e-12:return {'abel_jacobi':[u.real,u.imag],'point_at_infinity':True}
    sn=t3/t2*theta(1,v)/den;cn=t4/t2*theta(2,v)/den;dn=t4/t3*theta(3,v)/den
    x=lam*sn*sn;y=lam*sn*cn*dn;rhs=x*(x-1)*(x-lam)
    return {'abel_jacobi':[u.real,u.imag],'x':[x.real,x.imag],'y':[y.real,y.imag],
            'relative_equation_residual':abs(y*y-rhs)/max(1.,abs(rhs)),
            'theta_terms':theta_terms,'certified':False}
