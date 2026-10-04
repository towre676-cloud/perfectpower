"""Curve-derived closed hyperelliptic meshes and intrinsic heat Voronoi cells.

The metric is integrated along chart edges. Piecewise-flat lengths approximate
that smooth metric. Heat distances and linear face clipping are numerical
geodesic approximations, not exact Voronoi boundaries or graph distances.
"""
import math,cmath
from .analytic_surface import AnalyticSurface,evaluate,derivative,pair


def hyperelliptic_mesh(coefficients,resolution=5,ring_count=16):
    import numpy as np
    from scipy.spatial import Delaunay
    from scipy.integrate import quad
    if type(resolution) is not int or not 3<=resolution<=16:raise ValueError('resolution must be 3..16')
    s=AnalyticSurface(coefficients,2);g=s.packet['dimension_per_component']
    if not g or s.packet['geometry']['components']!=1 or any(e!=1 for a,e in s.roots):
        raise ValueError('connected positive-genus squarefree hyperelliptic curve required')
    roots=[a for a,e in s.roots];m=len(roots);radius=3*max(1.,max(map(abs,roots)))
    coords=list(roots);branch=set(range(m))
    for x in np.linspace(-.85*radius,.85*radius,resolution):
        for y in np.linspace(-.85*radius,.85*radius,resolution):
            z=complex(x,y)
            if abs(z)<.88*radius and min(abs(z-a) for a in coords)>1e-6:coords.append(z)
    ring=[]
    for k in range(ring_count):ring.append(len(coords));coords.append(radius*cmath.exp(2j*math.pi*k/ring_count))
    plane_faces=[tuple(map(int,t)) for t in Delaunay([[z.real,z.imag] for z in coords]).simplices]
    infinity=len(coords);coords.append(None)
    if m%2:branch.add(infinity)
    base_faces=[(f,False) for f in plane_faces]+[((infinity,ring[k],ring[(k+1)%ring_count]),True) for k in range(ring_count)]
    mids={};faces=[];face_caps=[];edge_chart={}
    def chart_coord(v,cap):
        z=coords[v];return (0j if z is None else 1/z) if cap else z
    def midpoint(a,b,cap):
        key=tuple(sorted((a,b)))
        if key not in mids:
            if cap and infinity in key:
                w=(chart_coord(a,True)+chart_coord(b,True))/2;z=1/w
            else:z=(coords[a]+coords[b])/2
            mids[key]=len(coords);coords.append(z)
        return mids[key]
    for (a,b,c),cap in base_faces:
        ab,bc,ca=midpoint(a,b,cap),midpoint(b,c,cap),midpoint(c,a,cap)
        if cap:wc=sum(chart_coord(v,True) for v in (a,b,c))/3;center=1/wc
        else:center=(coords[a]+coords[b]+coords[c])/3
        center_id=len(coords);coords.append(center)
        for tri in ((a,ab,center_id),(ab,b,center_id),(b,bc,center_id),(bc,c,center_id),(c,ca,center_id),(ca,a,center_id)):
            faces.append(tri);face_caps.append(cap)
            for u,v in zip(tri,tri[1:]+tri[:1]):edge_chart[tuple(sorted((u,v)))]=edge_chart.get(tuple(sorted((u,v))),False) or cap
    def parity(a,b,cap):
        if a in branch or b in branch:raise AssertionError('branch edges have no regular transition')
        if infinity in (a,b):
            finite=b if a==infinity else a;w=1/coords[finite];x=coords[finite]
            principal=cmath.exp(.5*cmath.log(evaluate(s.r,x)))
            analytic=cmath.exp(.5*sum(cmath.log(1-r*w) for r in roots))
            ratio=principal*w**(m//2)/analytic
            return 0 if ratio.real>0 else 1
        x,y=coords[a],coords[b]
        if cap:
            wa,wb=1/x,1/y
            increment=sum(cmath.log((1-r*wb)/(1-r*wa))-cmath.log(wb/wa) for r in roots)
        else:increment=sum(cmath.log((y-r)/(x-r)) for r in roots)
        delta=cmath.log(evaluate(s.r,x))+increment-cmath.log(evaluate(s.r,y))
        k=round(delta.imag/(2*math.pi))
        if abs(delta-2j*math.pi*k)>1e-6:raise AssertionError('inconsistent chart continuation')
        return k%2
    node={};labels=[]
    for v in range(len(coords)):
        for sheet in range(1 if v in branch else 2):node[(v,sheet)]=len(labels);labels.append((v,sheet))
    triangles=[]
    for face in faces:
        regular=[v for v in face if v not in branch]
        seed=regular[0]
        shifts={seed:0}
        for v in regular[1:]:shifts[v]=parity(seed,v,edge_chart[tuple(sorted((seed,v)))])
        if len(regular)==3:
            a,b,c=regular
            if (shifts[b]+parity(b,c,edge_chart[tuple(sorted((b,c)))])-shifts[c])%2:
                raise AssertionError('face continuation cocycle failed')
        for sheet in range(2):triangles.append([node[(v,0 if v in branch else (sheet+shifts[v])%2)] for v in face])
    lengths={};errors=[]
    def edge_length(a,b,cap):
        ca,cb=chart_coord(a,cap),chart_coord(b,cap)
        # Sin-squared endpoints remove simple branch/infinity square-root poles.
        def fn(theta):
            t=math.sin(theta)**2;z=ca+(cb-ca)*t;dz=(cb-ca)*2*math.sin(theta)*math.cos(theta)
            if cap:x=1/z;factor=abs(dz)/abs(z)**2
            else:x=z;factor=abs(dz)
            r=abs(evaluate(s.r,x));numerator=sum(abs(evaluate(f['numerator'],x))**2/r for f in s.forms)
            return math.sqrt(numerator)*factor
        value,error=quad(fn,0,math.pi/2,epsabs=2e-8,epsrel=2e-8,limit=200)
        errors.append(error);return value
    for edge,cap in edge_chart.items():lengths[edge]=edge_length(*edge,cap)
    lifted_edges={};incidences={}
    for fi,tri in enumerate(triangles):
        for a,b in zip(tri,tri[1:]+tri[:1]):
            key=tuple(sorted((a,b)));ba,bb=labels[a][0],labels[b][0]
            lifted_edges[key]=lengths[tuple(sorted((ba,bb)))];incidences.setdefault(key,[]).append(fi)
    chi=len(labels)-len(lifted_edges)+len(triangles)
    if chi!=2-2*g or any(len(v)!=2 for v in incidences.values()):raise AssertionError('lifted mesh is not the expected closed surface')
    links=[{} for _ in labels]
    directed={}
    for fi,tri in enumerate(triangles):
        for i,a in enumerate(tri):
            b,c=tri[(i+1)%3],tri[(i+2)%3]
            links[a].setdefault(b,[]).append(c);links[a].setdefault(c,[]).append(b)
            directed.setdefault(tuple(sorted((a,b))),[]).append((fi,1 if a<b else -1))
    for link in links:
        if any(len(v)!=2 for v in link.values()):raise AssertionError('nonmanifold vertex link')
        start=next(iter(link));seen={start};stack=[start]
        while stack:
            for v in link[stack.pop()]:
                if v not in seen:seen.add(v);stack.append(v)
        if len(seen)!=len(link):raise AssertionError('disconnected vertex link')
    adj=[[] for _ in triangles]
    for entry in directed.values():
        (a,da),(b,db)=entry;relation=-da*db;adj[a].append((b,relation));adj[b].append((a,relation))
    signs={0:1};stack=[0]
    while stack:
        a=stack.pop()
        for b,r in adj[a]:
            sign=signs[a]*r
            if b in signs:
                if signs[b]!=sign:raise AssertionError('nonorientable lifted surface')
            else:signs[b]=sign;stack.append(b)
    if len(signs)!=len(triangles):raise AssertionError('disconnected lifted surface')
    angles=np.zeros(len(labels));areas=[];local=[]
    for tri in triangles:
        a,b,c=tri;ab=lifted_edges[tuple(sorted((a,b)))];bc=lifted_edges[tuple(sorted((b,c)))];ca=lifted_edges[tuple(sorted((c,a)))]
        if min(ab+bc-ca,bc+ca-ab,ca+ab-bc)<=0:raise ValueError('metric triangle inequality failed; increase mesh resolution')
        xx=(ab*ab+ca*ca-bc*bc)/(2*ab);yy=math.sqrt(max(0.,ca*ca-xx*xx));local.append([[0.,0.],[ab,0.],[xx,yy]]);areas.append(ab*yy/2)
        for v,u,w in ((a,ab,ca),(b,ab,bc),(c,ca,bc)):
            opposite=bc if v==a else ca if v==b else ab
            angles[v]+=math.acos(max(-1.,min(1.,(u*u+w*w-opposite*opposite)/(2*u*w))))
    defects=2*math.pi-angles
    return {'schema':'pp-conformal-hyperelliptic-mesh/1','coefficients':list(coefficients),'genus':g,
            'resolution':resolution,'ring_count':ring_count,'vertices':len(labels),'edges':len(lifted_edges),'faces':len(triangles),
            'euler':chi,'connected':True,'closed_manifold_vertex_links':True,'orientable':True,'face_orientation_signs':[signs[i] for i in range(len(triangles))],'triangles':triangles,'triangle_local_coordinates':local,'triangle_areas':areas,
            'face_inverse_chart':[cap for cap in face_caps for _ in range(2)],
            'base_edge_inverse_chart':[[a,b,cap] for (a,b),cap in sorted(edge_chart.items())],
            'vertex_chart_labels':[[v,sh] for v,sh in labels],
            'base_coordinates':[None if z is None else pair(z) for z in coords],
            'edge_lengths':[[a,b,l] for (a,b),l in lifted_edges.items()],
            'angular_defects':list(map(float,defects)),'total_defect':float(sum(defects)),
            'gauss_bonnet_residual':float(sum(defects)-2*math.pi*chi),'area':float(sum(areas)),
            'maximum_edge_quadrature_error_estimate':max(errors),'root_diagnostics':s.root_diagnostics,
            'metric_source':'integrated sum |omega_i|^2 on the original normalized curve',
            'exact_conformal_mesh':False,'scope':'closed piecewise-flat approximation to smooth conformal curve metric; sheet gluing and Euler count checked'}


def heat_voronoi(mesh,n_sites=8):
    import numpy as np
    from scipy.sparse import coo_matrix,diags
    from scipy.sparse.linalg import factorized
    n=mesh['vertices']
    if type(n_sites) is not int or not 2<=n_sites<=min(n,30):raise ValueError('two through thirty sites required')
    rows=[];cols=[];data=[];mass=np.zeros(n);gradients=[]
    for tri,xy,area in zip(mesh['triangles'],mesh['triangle_local_coordinates'],mesh['triangle_areas']):
        inv=np.linalg.inv(np.array([[1.,p[0],p[1]] for p in xy]));grad=inv[1:,:];gradients.append(grad)
        block=area*grad.T@grad
        for i,a in enumerate(tri):
            mass[a]+=area/3
            for j,b in enumerate(tri):rows.append(a);cols.append(b);data.append(block[i,j])
    stiffness=coo_matrix((data,(rows,cols)),shape=(n,n)).tocsc();mean=sum(e[2] for e in mesh['edge_lengths'])/mesh['edges'];time=mean*mean
    heat_solve=factorized(diags(mass)+time*stiffness);poisson=factorized(stiffness[1:,1:]);distances=[];sites=[0];minraw=0.
    def solve(site):
        rhs=np.zeros(n);rhs[site]=1.;u=heat_solve(rhs);div=np.zeros(n)
        for tri,g,area in zip(mesh['triangles'],gradients,mesh['triangle_areas']):
            v=g@u[tri];norm=np.linalg.norm(v);x=-v/norm if norm>1e-30 else np.zeros(2);div[tri]+=area*g.T@x
        phi=np.zeros(n);phi[1:]=poisson(div[1:]);phi-=phi[site]
        return phi
    for k in range(n_sites):
        raw=solve(sites[-1]);minraw=min(minraw,float(raw.min()));distances.append(np.maximum(raw,0))
        if k+1<n_sites:sites.append(int(np.argmax(np.min(distances,axis=0))))
    fields=np.array(distances);pieces=[];cellarea=np.zeros(n_sites)
    def cut(poly,values):
        out=[]
        for a,b in zip(poly,poly[1:]+poly[:1]):
            va=float(np.dot(a,values));vb=float(np.dot(b,values))
            if va<=1e-12:out.append(a)
            if (va<-1e-12 and vb>1e-12) or (va>1e-12 and vb<-1e-12):out.append(a+(b-a)*va/(va-vb))
        return out
    for fi,(tri,area) in enumerate(zip(mesh['triangles'],mesh['triangle_areas'])):
        active=np.argmin(fields[:,tri],axis=0)
        # Keep all competing sites: three corner winners alone can miss cells.
        for site in range(n_sites):
            poly=[np.array([1.,0,0]),np.array([0.,1,0]),np.array([0.,0,1])]
            for other in range(n_sites):
                if other!=site:poly=cut(poly,fields[site,tri]-fields[other,tri])
                if not poly:break
            if len(poly)<3:continue
            fraction=abs(sum(a[1]*b[2]-b[1]*a[2] for a,b in zip(poly,poly[1:]+poly[:1])))
            if fraction<1e-14:continue
            cellarea[site]+=area*fraction;pieces.append({'face':fi,'site':site,'barycentric_polygon':[list(map(float,p)) for p in poly],'area':float(area*fraction)})
    return {'schema':'pp-intrinsic-heat-voronoi/1','mesh_genus':mesh['genus'],'sites':sites,
            'cell_areas':list(map(float,cellarea)),'pieces':pieces,'heat_time':time,
            'area_partition_residual':float(sum(cellarea)-mesh['area']),'minimum_unclipped_distance':minraw,
            'distance_fields':[list(map(float,d)) for d in fields],
            'method':'finite-element heat geodesic distances followed by intrinsic linear face bisector clipping',
            'graph_shortest_path':False,'exact_geodesic_voronoi':False,'certified':False,
            'scope':'numerical intrinsic Voronoi approximation on a curve-derived conformal polyhedral surface'}
