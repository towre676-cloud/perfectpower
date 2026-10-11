"""Source-bound rational segment admission certificates for Lean.

The producer proposes affine-sign cells or a blocked rational parameter for
EVERY ordered source vertex pair. Lean checks their exhaustive coverage and
reconstructs graph weights and vertices; no shortest-path search is used here.
"""
from fractions import Fraction as Q
from math import lcm
from .euclid_geometry import point, orientation
from .belyaev_geometry import _locate
from .geometry_certificates import check_route_certificate, compile_route_certificate, _proof_packet, digest
from .divisor_square import Budget, WorkLimit


def _lines(polygons, a, b):
    """All affine atoms in GeometryAdmission.obstaclesFormula, including boundary."""
    out=[]
    def coord(axis,c,sign=1):
        return sign*(b[axis]-a[axis]),sign*(a[axis]-c)
    for polygon in polygons:
        for c,d in zip(polygon,polygon[1:]+polygon[:1]):
            side=(orientation(c,d,b)-orientation(c,d,a),orientation(c,d,a))
            out.extend([side,coord(0,min(c[0],d[0])),coord(0,max(c[0],d[0]),-1),
                        coord(1,min(c[1],d[1])),coord(1,max(c[1],d[1]),-1)])
            if c[1]<d[1]:out.extend([coord(1,c[1]),coord(1,d[1]),tuple(-x for x in side)])
            elif d[1]<c[1]:out.extend([coord(1,d[1]),coord(1,c[1]),side])
            else:out.extend([(Q(0),Q(0))]*3)
    return out


def segment_evidence(obstacles, a, b, *, work_limit=1000000):
    """Cover the entire parameter interval; a proposal, independently checked in Lean."""
    budget=Budget(work_limit)
    polygons=[list(map(point,p)) for p in obstacles];a,b=map(point,(a,b))
    lines=_lines(polygons,a,b);cuts={Q(0),Q(1)}
    for slope,offset in lines:
        budget.spend()
        if slope:
            root=-offset/slope
            if 0<root<1:cuts.add(root)
    cuts=sorted(cuts);cells=list(zip(cuts,cuts[1:]))
    # Endpoints matter: a crossing or tangent must not evade open-cell checks.
    for t in sorted(set(cuts+[(lo+hi)/2 for lo,hi in cells])):
        p=tuple(x+t*(y-x) for x,y in zip(a,b))
        for polygon in polygons:
            budget.spend()
            if _locate(polygon,p)=='INSIDE':
                return {'status':'BLOCKED','parameter':str(t),'work_used':budget.used}
    for lo,hi in cells:
        for slope,offset in lines:
            budget.spend();left=slope*lo+offset;right=slope*hi+offset
            if left*right<0:raise AssertionError('affine root missing from partition')
    return {'status':'FREE','cells':[[str(lo),str(hi)] for lo,hi in cells],'work_used':budget.used}


def compile_geometric_route_certificate(packet, certificate, **limits):
    """Extend the old all-walk proof with independently checked geometric admission.

    Both directed orientations are certified. Omitted pairs carry a parameter
    inside an obstacle, proving completeness relative to rational winding
    geometry on the supplied source vertex set. Coordinates/weights are cleared
    with the same positive denominator; this is still Manhattan graph routing.
    """
    check_route_certificate(packet,certificate,**limits)
    nodes=list(map(point,packet['vertices']));polys=[list(map(point,p)) for p in packet['obstacles']]
    denominator=lcm(*(v.denominator for p in nodes for v in p),
                    *(Q(w).denominator for _,_,w in packet['edges']),
                    *(Q(v).denominator for v in certificate['potentials']),
                    Q(packet['cost']).denominator if packet['cost'] is not None else 1)
    scaled=lambda p:tuple(int(v*denominator) for v in p)
    ns=list(map(scaled,nodes));ps=[[scaled(p) for p in poly] for poly in polys]
    def ip(p):return f'(({p[0]} : Int),({p[1]} : Int))'
    def ilist(points):return '['+', '.join(map(ip,points))+']'
    def rat(q):
        q=Q(q);return f'(({q.numerator} : ℚ)/({q.denominator} : ℚ))'
    def qp(p):return f'({rat(p[0])},{rat(p[1])})'
    def qlist(points):return '['+', '.join(map(qp,points))+']'
    directed={(u,v) for u,v,_ in packet['edges']}|{(v,u) for u,v,_ in packet['edges']}
    pairs=sorted(directed)
    # Use the older compiler only for the retained walk/cut and dual witnesses.
    # It chooses a potentially smaller scale; replace its complete proof at the
    # desired scale by using integer-scaled input and zero-denominator potentials.
    from copy import deepcopy
    scaled_packet=deepcopy(packet)
    scaled_packet['start']=list(map(str,scaled(point(packet['start']))))
    scaled_packet['end']=list(map(str,scaled(point(packet['end']))))
    scaled_packet['vertices']=[list(map(str,p)) for p in ns]
    scaled_packet['obstacles']=[[list(map(str,p)) for p in poly] for poly in ps]
    scaled_packet['edges']=[[u,v,str(Q(w)*denominator)] for u,v,w in packet['edges']]
    scaled_packet['path']=[scaled_packet['vertices'][i] for i in packet.get('path_indices',[])]
    scaled_packet['cost']=str(Q(packet['cost'])*denominator) if packet['cost'] is not None else None
    scaled_cert=deepcopy(certificate);scaled_cert['source_sha256']=digest(scaled_packet)
    scaled_cert['potentials']=[str(Q(v)*denominator) for v in certificate['potentials']]
    old=compile_route_certificate(scaled_packet,scaled_cert,**limits)
    source=old['source'].replace('import PerfectPower.GeometryCertificates','import PerfectPower.GeometrySourceTransport',1)
    source=source.replace('theorem denominator_positive : (0 : Int)<(1)',f'theorem denominator_positive : (0 : Int)<({denominator})',1)
    pos=source.index('def edges')
    source=source[:pos]+f'''open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
-- Source coordinates, not producer-selected vertex indices.
def sourceObstacles : List (List Point) := [{', '.join(ilist(p) for p in ps)}]
def sourceStart : Point := {ip(scaled(point(packet['start'])))}
def sourceEnd : Point := {ip(scaled(point(packet['end'])))}
def nodes : List Point := ([sourceStart,sourceEnd] ++ sourceObstacles.flatten).eraseDups
def obstacles : List (List QPoint) := sourceObstacles.map (List.map qpoint)
theorem source_nodes : nodes = {ilist(ns)} := by decide
def originalObstacles : List (List QPoint) := [{', '.join(qlist(p) for p in polys)}]
def originalNodes : List QPoint := {qlist(nodes)}
theorem original_source_nodes : originalNodes = ([{qp(point(packet['start']))},{qp(point(packet['end']))}] ++ originalObstacles.flatten).eraseDups := by decide +kernel
theorem source_obstacle_scaling : obstacles = originalObstacles.map (List.map (scalePoint {rat(denominator)})) := by decide +kernel
theorem source_node_scaling : ∀ u ∈ List.range {len(ns)},
    qpoint (vertex nodes u) = scalePoint {rat(denominator)} (originalNodes[u]?.getD (0,0)) := by decide +kernel
def admitted : List (Nat × Nat) := [{', '.join(f'({u},{v})' for u,v in pairs)}]
'''+source[pos:]
    import re
    source=re.sub(r'def edges : List Edge := (\[[^\n]*\])',
                  r'def edges : List Edge := graph nodes admitted\ntheorem source_edges : edges.Perm \1 := by decide',source,count=1)
    tail=source.rindex('\nend ')
    geometry='''\ntheorem reconstructed_edges : edges = graph nodes admitted := rfl
'''
    evidence={};budget=Budget(limits.get('work_limit',1000000))
    for u in range(len(ns)):
        for v in range(len(ns)):
            if u==v:continue
            remaining=budget.limit-budget.used
            if remaining<1:raise WorkLimit('geometric certificate budget exceeded')
            e=segment_evidence(ps,ns[u],ns[v],work_limit=remaining);budget.used+=e['work_used'];evidence[f'{u},{v}']=e
            free=f'FreeSegment obstacles (qpoint (vertex nodes {u})) (qpoint (vertex nodes {v}))'
            f=f'obstaclesFormula obstacles (qpoint (vertex nodes {u})) (qpoint (vertex nodes {v}))'
            if e['status']=='FREE':
                if (u,v) not in directed:raise ValueError('Python visibility omitted a geometrically free pair')
                cells='['+', '.join(f'({rat(lo)},{rat(hi)})' for lo,hi in e['cells'])+']'
                geometry+=f'''def cells_{u}_{v} : List (ℚ × ℚ) := {cells}
theorem admission_{u}_{v} : accepted ({f}) cells_{u}_{v} := by decide +kernel
theorem pair_{u}_{v} : (({u},{v}) ∈ admitted) ↔ {free} :=
  iff_of_true (by decide) (segment_admission _ _ _ _ admission_{u}_{v})
'''
            else:
                if (u,v) in directed:raise ValueError('Python visibility admitted a blocked pair')
                t=rat(e['parameter'])
                geometry+=f'''theorem blockage_{u}_{v} : ({f}).eval {t} = true := by decide +kernel
theorem pair_{u}_{v} : (({u},{v}) ∈ admitted) ↔ {free} :=
  iff_of_false (by decide) (blocked_segment _ _ _ {t} (by norm_num) (by norm_num) blockage_{u}_{v})
'''
    geometry+='''theorem geometric_complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
    ((u,v) ∈ admitted ↔ FreeSegment obstacles (qpoint (vertex nodes u)) (qpoint (vertex nodes v))) := by
  intro u v hu hv hne
  rw [source_nodes] at hu hv
  simp only [List.length_cons, List.length_nil] at hu hv
  interval_cases u <;> interval_cases v
'''
    for u in range(len(ns)):
        for v in range(len(ns)):
            geometry+=('  · omega\n' if u==v else f'  · exact pair_{u}_{v}\n')
    geometry+=f'''theorem original_geometric_complete : ∀ u v, u < nodes.length → v < nodes.length → u ≠ v →
    ((u,v) ∈ admitted ↔ FreeSegment originalObstacles (originalNodes[u]?.getD (0,0)) (originalNodes[v]?.getD (0,0))) := by
  intro u v hu hv hne
  have hu' : u < {len(ns)} := by simpa only [source_nodes,List.length_cons,List.length_nil] using hu
  have hv' : v < {len(ns)} := by simpa only [source_nodes,List.length_cons,List.length_nil] using hv
  rw [geometric_complete u v hu hv hne,source_obstacle_scaling,
    source_node_scaling u (List.mem_range.mpr hu'),source_node_scaling v (List.mem_range.mpr hv')]
  exact free_segment_scale {rat(denominator)} (by norm_num) _ _ _
theorem original_nodes_length : nodes.length = originalNodes.length := by decide
theorem vertex_scaling : ∀ u, u < originalNodes.length →
    qpoint (vertex nodes u) = scalePoint {rat(denominator)} (rationalVertex originalNodes u) := by
  intro u hu
  have hn : u < {len(ns)} := by simpa only [originalNodes,List.length_cons,List.length_nil] using hu
  exact source_node_scaling u (List.mem_range.mpr hn)
#print axioms original_geometric_complete
'''
    if packet['status']=='ROUTE':
        cost=int(Q(packet['cost'])*denominator)
        s=packet['vertices'].index(packet['start']);t=packet['vertices'].index(packet['end'])
        geometry+=f'''theorem no_cheaper_geometric_walk {{other : Int}}
    (walk : GeometricWalk obstacles nodes {s} {t} other) : ({cost} : Int) ≤ other := by
  apply geometric_optimal_walk obstacles nodes admitted geometric_complete potential
  · rw [← reconstructed_edges]; exact edge_bounds
  · exact dual_equality
  · exact walk
theorem no_cheaper_original_walk {{other : ℚ}}
    (walk : RationalGeometricWalk originalObstacles originalNodes {s} {t} other) : {rat(packet['cost'])} ≤ other := by
  apply rational_optimal_walk {rat(denominator)} (by norm_num) originalObstacles originalNodes nodes
    original_nodes_length vertex_scaling (best := ({cost} : Int))
  · norm_num
  · intro c walk
    rw [← source_obstacle_scaling] at walk
    exact no_cheaper_geometric_walk walk
  · exact walk
def sourcePath : List Nat := [{', '.join(map(str,packet['path_indices']))}]
theorem source_path_admitted : ∀ e ∈ sourcePath.zip sourcePath.tail,
    e.1 < nodes.length ∧ e.2 < nodes.length ∧ e.1 ≠ e.2 ∧ e ∈ admitted := by decide
theorem source_path_visible : ∀ e ∈ sourcePath.zip sourcePath.tail,
    FreeSegment originalObstacles (rationalVertex originalNodes e.1) (rationalVertex originalNodes e.2) := by
  intro e he
  have h := source_path_admitted e he
  exact (original_geometric_complete e.1 e.2 h.1 h.2.1 h.2.2.1).mp h.2.2.2
theorem source_path_cost : ((sourcePath.zip sourcePath.tail).map
    (fun e => qweight (rationalVertex originalNodes e.1) (rationalVertex originalNodes e.2))).sum = {rat(packet['cost'])} := by decide +kernel
#print axioms no_cheaper_geometric_walk
#print axioms no_cheaper_original_walk
#print axioms source_path_visible
'''
    else:
        s=packet['vertices'].index(packet['start']);t=packet['vertices'].index(packet['end'])
        geometry+=f'''theorem no_geometric_route (c : Int) : ¬GeometricWalk obstacles nodes {s} {t} c := by
  intro walk
  have hw := geometric_walk_to_graph obstacles nodes admitted geometric_complete walk
  rw [← reconstructed_edges] at hw
  exact no_route c hw
theorem no_original_route (c : ℚ) : ¬RationalGeometricWalk originalObstacles originalNodes {s} {t} c := by
  intro walk
  obtain ⟨scaled,hw,_⟩ := rational_walk_scaled {rat(denominator)} (by norm_num) originalObstacles originalNodes nodes original_nodes_length vertex_scaling walk
  rw [← source_obstacle_scaling] at hw
  exact no_geometric_route scaled hw
#print axioms no_geometric_route
#print axioms no_original_route
'''
    geometry+='#print axioms geometric_complete\n'
    source=source[:tail]+geometry+source[tail:]
    return _proof_packet(source,{'packet':packet,'certificate':certificate},
        'complete source-derived finite graph for universal rational segment avoidance under exact nonzero-winding interior semantics; scaled Manhattan all-walk optimality or unreachability; no arbitrary-bend/global path, topology, clearance or rope dynamics claim',
        schema='pp-lean-geometric-route/1',denominator=denominator,pair_evidence=evidence,work_used=budget.used)


def compile_refinement_mesh_certificate(packet, trace, **limits):
    """Pointwise coverage of triangular source domains under finite edge splits.

    Each step replaces one CCW triangle (a,b,c) by (a,b,m),(a,m,c),
    m=(1-t)b+t*c, 0<t<1. This independent acceptance does not infer a trace
    from arbitrary admitted meshes, nor claim the general polygon chain theorem.
    """
    from .geometry_certificates import check_mesh_certificate
    check_mesh_certificate(packet,**limits)
    polygon=list(map(point,packet['vertices']))
    if len(polygon)!=3:raise ValueError('refinement coverage currently needs a triangular source domain')
    mesh=[polygon];steps=[];budget=Budget(limits.get('work_limit',1000000))
    cap=limits.get('triangle_limit',200)
    for step in trace:
        budget.spend()
        if len(mesh)>=cap:raise WorkLimit('refinement triangle limit exceeded')
        from .euclid_geometry import rational
        i=step['triangle'];t=rational(step['parameter'])
        if type(i) is not int or not 0<=i<len(mesh) or not 0<t<1:raise ValueError('invalid edge refinement step')
        before=mesh[:i];after=mesh[i+1:];a,b,c=mesh[i]
        m=tuple(x+t*(y-x) for x,y in zip(b,c))
        result=before+[[a,b,m],[a,m,c]]+after
        steps.append((before,after,a,b,c,t,result));mesh=result
    if mesh!=[list(map(point,t)) for t in packet['triangles']]:raise ValueError('trace does not reconstruct the supplied mesh')
    def rat(q):
        q=Q(q);return f'(({q.numerator} : ℚ)/({q.denominator} : ℚ))'
    def qp(p):return f'({rat(p[0])},{rat(p[1])})'
    def triangle(t):return '('+', '.join(map(qp,t))+')'
    def ml(ts):return '['+', '.join(map(triangle,ts))+']'
    namespace='R'+digest({'packet':packet,'trace':trace})
    source=f'''import PerfectPower.GeometryAdmission
namespace PerfectPower.CheckedMesh.{namespace}
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
def mesh_0 : List Triangle := {ml([polygon])}
theorem source_positive : (0 : ℚ) < qside {qp(polygon[0])} {qp(polygon[1])} {qp(polygon[2])} := by decide +kernel
theorem refinement_0 : Refines mesh_0 mesh_0 := Refines.refl _
'''
    for j,(before,after,a,b,c,t,result) in enumerate(steps,1):
        source+=f'''def mesh_{j} : List Triangle := {ml(result)}
theorem step_{j} : Refines mesh_{j-1} mesh_{j} := by
  have h := Refines.split {ml(before)} {ml(after)} {qp(a)} {qp(b)} {qp(c)} {rat(t)} (by norm_num) (by norm_num)
  have left : mesh_{j-1} = {ml(before)} ++ {triangle([a,b,c])} :: {ml(after)} := by decide +kernel
  have right : mesh_{j} = {ml(before)} ++ {triangle([a,b,tuple(x+t*(y-x) for x,y in zip(b,c))])} :: {triangle([a,tuple(x+t*(y-x) for x,y in zip(b,c)),c])} :: {ml(after)} := by decide +kernel
  rw [left,right]
  convert h using 1; norm_num [interpolate]
theorem refinement_{j} : Refines mesh_0 mesh_{j} := Refines.trans refinement_{j-1} step_{j}
'''
    source+=f'''theorem final_triangles_positive : ∀ tri ∈ mesh_{len(steps)}, (0 : ℚ) < qside tri.1 tri.2.1 tri.2.2 := by decide +kernel
theorem source_coverage (p : QPoint) : meshCovers mesh_0 p ↔ meshCovers mesh_{len(steps)} p :=
  refinement_coverage refinement_{len(steps)} p
#print axioms source_coverage
end PerfectPower.CheckedMesh.{namespace}
'''
    return _proof_packet(source,{'packet':packet,'trace':trace},
        'pointwise equality of closed rational triangle-source region and supplied mesh, including all edges and vertices; finite edge refinement trace independently checked; arbitrary polygon meshes require a further coverage bridge',
        schema='pp-lean-refinement-mesh/1',refinement_steps=len(steps),work_used=budget.used)


def compile_boundary_contact_certificate(polygon, a, b, *, work_limit=1000000):
    """Exact polygon-boundary contact or universal disjointness, including overlaps.

    This concerns the boundary chain itself and does not assume polygon simplicity.
    """
    from .euclid_geometry import segment_intersection
    polygon=list(map(point,polygon));a,b=map(point,(a,b));budget=Budget(work_limit)
    if len(polygon)<2:raise ValueError('at least two boundary vertices required')
    def rat(q):
        q=Q(q);return f'(({q.numerator} : ℚ)/({q.denominator} : ℚ))'
    def qp(p):return f'({rat(p[0])},{rat(p[1])})'
    name='C'+digest({'polygon':[[str(v) for v in p] for p in polygon],'a':list(map(str,a)),'b':list(map(str,b))})
    source=f'''import PerfectPower.GeometryContact
namespace PerfectPower.CheckedContact.{name}
open PerfectPower.GeometryAdmission
set_option maxRecDepth 10000
def polygon : List QPoint := [{', '.join(map(qp,polygon))}]
def start : QPoint := {qp(a)}
def finish : QPoint := {qp(b)}
'''
    witness=None
    for c,d in zip(polygon,polygon[1:]+polygon[:1]):
        budget.spend();hit=segment_intersection(a,b,c,d)
        if hit['points']:
            witness=(c,d,point(hit['points'][0]));break
    if witness:
        c,d,p=witness
        source+=f'''theorem contact : BoundaryContact polygon start finish :=
  boundary_contact_witness polygon start finish {qp(c)} {qp(d)} {qp(p)} (by decide +kernel) (by decide +kernel) (by decide +kernel)
#print axioms contact
'''
        status='CONTACT'
    else:
        # _lines contains every boundary atom; extra winding atoms are harmless.
        cuts={Q(0),Q(1)}
        for slope,offset in _lines([polygon],a,b):
            budget.spend()
            if slope and 0 < -offset/slope < 1:cuts.add(-offset/slope)
        cuts=sorted(cuts);cells='['+', '.join(f'({rat(lo)},{rat(hi)})' for lo,hi in zip(cuts,cuts[1:]))+']'
        source+=f'''def cells : List (ℚ × ℚ) := {cells}
theorem admission : accepted (boundaryFormula polygon start finish) cells := by decide +kernel
theorem disjoint : ¬BoundaryContact polygon start finish := no_boundary_contact _ _ _ _ admission
#print axioms disjoint
'''
        status='DISJOINT'
    source+=f'end PerfectPower.CheckedContact.{name}\n'
    spec={'polygon':[[str(v) for v in p] for p in polygon],'start':list(map(str,a)),'end':list(map(str,b))}
    return _proof_packet(source,spec,'exact contact/disjointness with supplied finite rational polygon boundary, including tangencies and overlapping segments; no interior/topology inference',
                         schema='pp-lean-boundary-contact/1',status=status,work_used=budget.used)
