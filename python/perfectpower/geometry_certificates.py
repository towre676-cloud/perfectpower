"""Independent exact mesh and finite visibility-graph optimality certificates.

No ear clipping or shortest-path search is used by either acceptance function.
Geometric predicates remain Python; emitted Lean proofs certify source-bound
integer separation/boundary data and all-walk graph optimality, not topology.
"""
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from heapq import heappop, heappush
from math import lcm
import json
from .euclid_geometry import point, encode, rational, orientation, on_segment
from .belyaev_geometry import _simple, _locate, signed_area2
from .polygon_routing import _visible, _charge
from .divisor_square import Budget, WorkLimit


def digest(packet):
    return sha256(json.dumps(packet, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _cap(value, name):
    if type(value) is not int or value < 1:
        raise ValueError(name+' must be a positive integer')


def _separation(first, second, budget):
    """Separating-axis witness for closed triangles with disjoint interiors."""
    for triangle in (first, second):
        for a, b in zip(triangle, triangle[1:]+triangle[:1]):
            values=[]
            for group in (first, second):
                row=[]
                for p in group:
                    budget.spend();row.append(orientation(a,b,p))
                values.append(row)
            for sign in (1,-1):
                if all(sign*v>=0 for v in values[0]) and all(sign*v<=0 for v in values[1]):
                    return {'line':[encode(a),encode(b)],'first_side':sign}
    raise ValueError('triangle interiors overlap')


def _chain(edges, points, budget):
    """Split every edge at all admitted collinear vertices, including T-junctions."""
    out=Counter()
    for a,b in edges:
        cuts=[]
        for p in points:
            budget.spend()
            if on_segment(p,a,b):cuts.append(p)
        cuts.sort(reverse=a>b)
        for u,v in zip(cuts,cuts[1:]):
            key=(min(u,v),max(u,v));out[key]+=1 if u<v else -1
    return out


def certify_mesh(vertices, triangles, *, work_limit=1000000, triangle_limit=200, vertex_limit=500):
    """Validate arbitrary positive rational triangle meshes, including Steiner points.

    Pairwise separating halfplanes prohibit overlap; the oriented atomized
    boundary equals the source polygon and positive area equals source area.
    This check is independent of triangulate() and does not require its output.
    """
    _cap(triangle_limit,'triangle limit');_cap(vertex_limit,'vertex limit')
    budget=Budget(work_limit)
    vertices=list(vertices);triangles=list(triangles)
    if len(vertices)>vertex_limit or len(triangles)>triangle_limit:
        raise WorkLimit('mesh size limit exceeded')
    polygon=_simple(vertices,budget)
    if signed_area2(polygon)<0:polygon.reverse()
    mesh=[]
    for triangle in triangles:
        if len(triangle)!=3:raise ValueError('exactly three vertices per triangle required')
        t=list(map(point,triangle));budget.spend()
        if orientation(*t)<=0:raise ValueError('strictly positive CCW triangles required')
        mesh.append(t)
    if not mesh:raise ValueError('nonempty triangle mesh required')
    points=sorted(set(polygon+[p for t in mesh for p in t]))
    if len(points)>vertex_limit:raise WorkLimit('mesh vertex limit exceeded')
    separators=[]
    for i,first in enumerate(mesh):
        for j in range(i+1,len(mesh)):
            separators.append({'triangles':[i,j],**_separation(first,mesh[j],budget)})
    source_edges=list(zip(polygon,polygon[1:]+polygon[:1]))
    mesh_edges=[edge for t in mesh for edge in zip(t,t[1:]+t[:1])]
    source_chain=_chain(source_edges,points,budget);mesh_chain=_chain(mesh_edges,points,budget)
    atoms=sorted(set(source_chain)|set(mesh_chain))
    if any(source_chain[a]!=mesh_chain[a] for a in atoms):
        raise ValueError('oriented mesh boundary differs from source polygon')
    areas=[orientation(*t)/2 for t in mesh];source_area=signed_area2(polygon)/2
    if sum(areas)!=source_area:raise ValueError('mesh area differs from source polygon')
    return {'schema':'pp-independent-rational-mesh/1','vertices':[encode(p) for p in polygon],
            'triangles':[[encode(p) for p in t] for t in mesh],
            'triangle_areas':[str(a) for a in areas],'area':str(source_area),
            'separators':separators,
            'boundary_atoms':[{'edge':[encode(p) for p in edge],
                               'source_coefficient':source_chain[edge],
                               'mesh_coefficient':mesh_chain[edge]} for edge in atoms],
            'work_used':budget.used,'kernel_checked':False,
            'scope':'exact pairwise separating halfplanes, atomized oriented boundary equality and positive area; geometric coverage uses the simple-polygon topology, not a Lean coverage theorem'}


def check_mesh_certificate(packet, **limits):
    expected=certify_mesh(packet['vertices'],packet['triangles'],**limits)
    if expected!=packet:raise ValueError('mesh certificate data differs from independent checks')
    return True


def _graph(packet,budget,vertex_limit):
    """Rebuild admissible vertices/edges, without optimizing or selecting a route."""
    _cap(vertex_limit,'vertex limit')
    if packet.get('schema')!='pp-polygon-visibility-route/1' or packet.get('complete') is not True:
        raise ValueError('complete visibility route packet required')
    if len(packet['vertices'])>vertex_limit:raise WorkLimit('route vertex limit exceeded')
    polygons=[_simple(p,budget) for p in packet['obstacles']]
    start,end=map(point,(packet['start'],packet['end']))
    for polygon in polygons:
        _charge(budget,4*len(polygon))
        if _locate(polygon,start)=='INSIDE' or _locate(polygon,end)=='INSIDE':
            raise ValueError('route endpoint inside obstacle')
    nodes=list(dict.fromkeys([start,end]+[v for p in polygons for v in p]))
    if len(nodes)>vertex_limit:raise WorkLimit('route vertex limit exceeded')
    if packet['vertices']!=[encode(p) for p in nodes]:raise ValueError('source vertex list mismatch')
    edges=[]
    for i,a in enumerate(nodes):
        for j in range(i+1,len(nodes)):
            budget.spend();b=nodes[j]
            if _visible(polygons,a,b,budget):
                edges.append([i,j,str(sum((abs(x-y) for x,y in zip(a,b)),Q(0)))])
    if edges!=packet['edges']:raise ValueError('full geometric visibility edge list mismatch')
    return nodes,edges,nodes.index(start),nodes.index(end)


def certify_route(packet, *, work_limit=1000000, vertex_limit=200):
    """Producer: full graph distances supply feasible dual potentials or a cut."""
    budget=Budget(work_limit);nodes,edges,s,t=_graph(packet,budget,vertex_limit)
    adj=[[] for _ in nodes]
    for u,v,w in edges:
        w=Q(w);adj[u].append((v,w));adj[v].append((u,w))
    distances={s:Q(0)};heap=[(Q(0),s)]
    while heap:
        cost,u=heappop(heap)
        if distances[u]!=cost:continue
        for v,w in adj[u]:
            budget.spend();candidate=cost+w
            if v not in distances or candidate<distances[v]:
                distances[v]=candidate;heappush(heap,(candidate,v))
    # Disconnected components have no edge to the source component: zero is a
    # valid feasible potential on each such component, regardless of reachability.
    proof={'schema':'pp-visibility-dual-certificate/1','source_sha256':digest(packet),
           'status':packet['status'],'potentials':[str(distances.get(i,Q(0))) for i in range(len(nodes))],
           'reachable':sorted(distances),'kernel_checked':False,
           'scope':'cost optimality for every finite walk in the complete source-bound visibility graph; route tie-breaking is not certified'}
    check_route_certificate(packet,proof,work_limit=work_limit,vertex_limit=vertex_limit)
    return proof


def check_route_certificate(packet, certificate, *, work_limit=1000000, vertex_limit=200):
    """Acceptance: geometry replay + edge inequalities + witness; no search."""
    budget=Budget(work_limit);nodes,edges,s,t=_graph(packet,budget,vertex_limit)
    if certificate.get('schema')!='pp-visibility-dual-certificate/1' or certificate.get('source_sha256')!=digest(packet):
        raise ValueError('route certificate source mismatch')
    if certificate.get('status')!=packet['status']:raise ValueError('status mismatch')
    if len(certificate['potentials'])!=len(nodes):raise ValueError('one potential per vertex required')
    potentials=list(map(rational,certificate['potentials']))
    reached=certificate['reachable']
    if any(type(i) is not int or not 0<=i<len(nodes) for i in reached) or reached!=sorted(set(reached)):
        raise ValueError('canonical in-range reachability set required')
    reached=set(reached)
    if s not in reached:raise ValueError('source absent from reachability set')
    weights={}
    for u,v,w in edges:
        budget.spend();w=Q(w);weights[u,v]=weights[v,u]=w
        if (u in reached)!=(v in reached):raise ValueError('claimed component is not edge-closed')
        if abs(potentials[v]-potentials[u])>w:raise ValueError('infeasible edge potential')
    if packet['status']=='UNREACHABLE':
        if t in reached or packet['path']!=[] or packet['cost'] is not None:
            raise ValueError('unreachable cut does not separate endpoints')
    elif packet['status']=='ROUTE':
        indices=packet['path_indices']
        if not indices or any(type(i) is not int or not 0<=i<len(nodes) for i in indices):
            raise ValueError('invalid path indices')
        if indices[0]!=s or indices[-1]!=t:raise ValueError('path endpoint mismatch')
        if packet['path']!=[encode(nodes[i]) for i in indices]:raise ValueError('path coordinates mismatch')
        cost=Q(0)
        for u,v in zip(indices,indices[1:]):
            budget.spend()
            if (u,v) not in weights:raise ValueError('path edge absent')
            cost+=weights[u,v]
        if rational(packet['cost'])!=cost or cost!=potentials[t]-potentials[s]:
            raise ValueError('path cost fails dual equality')
        if t not in reached:raise ValueError('target absent from route component')
    else:raise ValueError('unknown route status')
    return True


def _proof_packet(source, specification, scope, **fields):
    return {'source':source,'source_sha256':sha256(source.encode()).hexdigest(),
            'specification_sha256':digest(specification),'kernel_checked':False,'scope':scope,**fields}


def compile_route_certificate(packet, certificate, **limits):
    check_route_certificate(packet,certificate,**limits)
    values=[Q(w) for _,_,w in packet['edges']]+list(map(Q,certificate['potentials']))
    if packet['cost'] is not None:values.append(Q(packet['cost']))
    denominator=lcm(*(v.denominator for v in values))
    edges=[(u,v,int(Q(w)*denominator)) for u,v,w in packet['edges']]
    directed=edges+[(v,u,w) for u,v,w in edges]
    potentials=[int(Q(v)*denominator) for v in certificate['potentials']]
    s=packet['vertices'].index(packet['start']);t=packet['vertices'].index(packet['end'])
    namespace='P'+digest({'packet':packet,'certificate':certificate})
    edge_text=', '.join(f'({u},{v},({w} : Int))' for u,v,w in directed)
    potentials_text=', '.join(f'({v} : Int)' for v in potentials)
    source=f'''import PerfectPower.GeometryCertificates
namespace PerfectPower.CheckedGraph.{namespace}
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<({denominator}) := by decide
def edges : List Edge := [{edge_text}]
def potentials : List Int := [{potentials_text}]
def potential (u : Nat) : Int := potentials[u]?.getD 0
theorem edge_bounds : ∀ e ∈ edges, potential e.2.1 ≤ potential e.1 + e.2.2 := by decide
'''
    if packet['status']=='ROUTE':
        indices=packet['path_indices'];cost=int(Q(packet['cost'])*denominator)
        weights={(u,v):w for u,v,w in directed}
        steps=[weights[u,v] for u,v in zip(indices,indices[1:])]
        proof='Walk.nil '+str(t)
        for i in range(len(steps)-1,-1,-1):
            proof=f'Walk.cons (edges := edges) (u := {indices[i]}) (v := {indices[i+1]}) (t := {t}) (w := ({steps[i]})) (c := ({sum(steps[i+1:])})) (by decide) ({proof})'
        source+=f'''theorem retained_path : Walk edges {s} {t} ({cost}) := by
  show Walk edges {s} {t} ({'+'.join(str(w) for w in steps)+('+0' if steps else '0')})
  exact {proof}
theorem dual_equality : ({cost} : Int) = potential {t} - potential {s} := by decide
theorem no_cheaper_walk {{other : Int}} (walk : Walk edges {s} {t} other) : ({cost} : Int) ≤ other :=
  optimal_walk edges potential edge_bounds dual_equality walk
#print axioms retained_path
#print axioms no_cheaper_walk
'''
    else:
        reached=', '.join(map(str,certificate['reachable']))
        source+=f'''def reachable (u : Nat) : Prop := u ∈ ([{reached}] : List Nat)
instance (u : Nat) : Decidable (reachable u) := by unfold reachable; infer_instance
theorem closed : ∀ e ∈ edges, reachable e.1 → reachable e.2.1 := by decide
theorem source_inside : reachable {s} := by decide
theorem target_outside : ¬reachable {t} := by decide
theorem no_route : ∀ c, ¬Walk edges {s} {t} c :=
  no_walk_outside edges reachable closed source_inside target_outside
#print axioms no_route
'''
    source+=f'end PerfectPower.CheckedGraph.{namespace}\n'
    return _proof_packet(source,{'packet':packet,'certificate':certificate},
        'every finite graph walk has at least the retained scaled cost, or no graph walk exists; source geometry and Manhattan edge weights checked by Python',
        schema='pp-lean-visibility-dual/1',denominator=denominator)


def compile_mesh_certificate(packet, **limits):
    check_mesh_certificate(packet,**limits)
    polygon=list(map(point,packet['vertices']));mesh=[list(map(point,t)) for t in packet['triangles']]
    points=sorted(set(polygon+[p for t in mesh for p in t]))
    denominator=lcm(*(v.denominator for p in points for v in p))
    scaled=lambda p:tuple(int(v*denominator) for v in p)
    def lit(p):
        x,y=scaled(p);return f'(({x} : Int),({y} : Int))'
    def group(t):return '['+', '.join(map(lit,t))+']'
    source_edges=list(zip(polygon,polygon[1:]+polygon[:1]))
    mesh_edges=[edge for t in mesh for edge in zip(t,t[1:]+t[:1])]
    # Segment-membership claims are separate from the atom counts: Lean
    # computes those counts directly from the actual coordinate lists.
    clauses=[]
    for a,b in source_edges+mesh_edges:
        for p in points:
            if on_segment(p,a,b):clauses.append(f'onSegment {lit(p)} {lit(a)} {lit(b)}')
    namespace='M'+digest(packet)
    source=f'''import PerfectPower.GeometryCertificates
namespace PerfectPower.CheckedMesh.{namespace}
open PerfectPower.GeometryCertificates
theorem denominator_positive : (0 : Int)<({denominator}) := by decide
def vertices : List Point := {group(points)}
def polygon : List Point := {group(polygon)}
def triangles : List (List Point) := [{', '.join(group(t) for t in mesh)}]
theorem vertices_ordered : ∀ e ∈ vertices.zip vertices.tail,
    e.1.1 < e.2.1 ∨ (e.1.1 = e.2.1 ∧ e.1.2 < e.2.2) := by decide
'''
    for i,t in enumerate(mesh):
        source+=f'theorem triangle_{i}_positive : (0 : Int) < side {lit(t[0])} {lit(t[1])} {lit(t[2])} := by decide\n'
    for witness in packet['separators']:
        i,j=witness['triangles'];a,b=map(point,witness['line']);sign=witness['first_side']
        source+=f'theorem separation_{i}_{j} : separated {group(mesh[i])} {group(mesh[j])} {lit(a)} {lit(b)} ({sign}) := by decide\n'
    side_terms='+'.join(f'(side {lit(t[0])} {lit(t[1])} {lit(t[2])})' for t in mesh)
    area2=int(Q(packet['area'])*2*denominator*denominator)
    polygon_terms='+'.join(f'(side {lit(a)} {lit(b)} ((0 : Int),(0 : Int)))' for a,b in source_edges)
    source+=f'theorem polygon_area : {polygon_terms}=({area2} : Int) := by decide\n'
    source+=f'theorem area_total : {side_terms}=({area2} : Int) := by decide\n'
    source+=f'theorem subdivision_membership : {" ∧ ".join(clauses)} := by decide\n'
    edge_lit=lambda edges:'['+', '.join(f'({lit(a)},{lit(b)})' for a,b in edges)+']'
    source+=f'''def sourceEdges : List (Point × Point) := {edge_lit(source_edges)}
def meshEdges : List (Point × Point) := {edge_lit(mesh_edges)}
theorem edge_endpoints_admitted : ∀ e ∈ sourceEdges ++ meshEdges, e.1 ∈ vertices ∧ e.2 ∈ vertices := by decide
def sourceAtoms : List (Nat × Nat) := sourceEdges.flatMap (fun e => atomicLine vertices e.1 e.2)
def meshAtoms : List (Nat × Nat) := meshEdges.flatMap (fun e => atomicLine vertices e.1 e.2)
def atomicEdges : List (Nat × Nat) := (List.range {len(points)}).flatMap (fun u => (List.range {len(points)}).map (fun v => (u,v)))
theorem boundary_counts : ∀ e ∈ atomicEdges,
    signedMultiplicity meshAtoms e.1 e.2 = signedMultiplicity sourceAtoms e.1 e.2 := by decide
#print axioms boundary_counts
#print axioms area_total
'''
    for witness in packet['separators']:
        i,j=witness['triangles'];source+=f'#print axioms separation_{i}_{j}\n'
    source+=f'end PerfectPower.CheckedMesh.{namespace}\n'
    return _proof_packet(source,packet,
        'actual integer triangle positivity, pairwise separating halfplanes, subdivision segment membership and oriented atomic boundary counts; atomic subdivisions computed from actual coordinates in Lean; full topology/coverage theorem remains outside Lean',
        schema='pp-lean-rational-mesh/1',denominator=denominator)


def certify_voronoi_mesh(packet, *, work_limit=1000000, triangle_limit=200, vertex_limit=500, site_pair_limit=10000):
    """Independently accept the supplied cell meshes without running ear clipping."""
    from .euclid_geometry import voronoi_cells
    base=packet['voronoi']
    if base!=voronoi_cells(base['sites'],base['box'],pair_limit=site_pair_limit):
        raise ValueError('source Voronoi diagram does not replay')
    if packet.get('schema')!='pp-rational-voronoi-mesh/1' or set(packet['mesh'])!=set(base['cells']):
        raise ValueError('Voronoi mesh labels mismatch')
    budget=Budget(work_limit);certificates={};references={};seen={};total=Q(0)
    for name,cell in base['cells'].items():
        budget.spend();vertices=list(map(point,cell['vertices']));supplied=packet['mesh'][name]
        if len(vertices)<3 or signed_area2(vertices)==0:
            expected={'dimension':-1 if not vertices else 0 if len(set(vertices))==1 else 1,
                      'area':'0','centroid':None,'triangles':[]}
            if supplied!=expected:raise ValueError('degenerate Voronoi cell mesh mismatch')
            references[name]=None;continue
        remaining=budget.limit-budget.used
        if remaining<1:raise WorkLimit('Voronoi certificate budget exceeded')
        certificate=certify_mesh(vertices,supplied['triangles'],work_limit=remaining,
                                 triangle_limit=triangle_limit,vertex_limit=vertex_limit)
        _charge(budget,certificate['work_used'])
        area=Q(certificate['area']);triangles=certificate['triangles'];weights=list(map(Q,certificate['triangle_areas']))
        centroid=tuple(sum(weight*sum(Q(v[i]) for v in tri)/3 for weight,tri in zip(weights,triangles))/area for i in range(2))
        if supplied['dimension']!=2 or supplied['area']!=str(area) or supplied['centroid']!=encode(centroid):
            raise ValueError('Voronoi cell moments mismatch')
        # Coincident labels share the same geometric cell. Accept an alternate
        # triangulation for a duplicate label, but count its area only once.
        key=tuple(base['sites'][name])
        if key not in seen:
            seen[key]=name;total+=area
        certificates[name]=certificate;references[name]=seen[key]
    lo,hi=map(point,base['box']);box_area=(hi[0]-lo[0])*(hi[1]-lo[1])
    if total!=box_area or packet['unique_cell_area']!=str(total) or packet['box_area']!=str(box_area):
        raise ValueError('Voronoi unique-cell area mismatch')
    return {'schema':'pp-independent-voronoi-mesh/1','source_sha256':digest(packet),
            'cells':certificates,'unique_cell_references':references,'unique_cell_area':str(total),
            'work_used':budget.used,'kernel_checked':False,
            'scope':'source-bound planar cell mesh separation, oriented boundary and moments; coincident-site areas counted once, Voronoi clipping remains Python'}
