"""JSON command interface for exact polygon structure, rigid maps and routing."""
import json
from .belyaev_geometry import between,line_through,meet_lines,polygon_structure,locate_point,triangulate,polygon_centroid,circumcircle,incircle,fit_isometries,voronoi_mesh,transport_voronoi
from .polygon_routing import route,segment_visibility

OPERATIONS=('real-contact-proof','real-mesh-proof','real-segment-proof','real-route-proof','metric-energy-proof','incidence','polygon','locate','triangulate','centroid','circumcircle','incircle','congruence','visibility','route','voronoi-mesh','transport-voronoi','mesh-certificate','route-certificate','mesh-proof','route-proof','geometric-route-proof','boundary-contact-proof','refinement-mesh-proof','voronoi-mesh-certificate')


def dispatch(operation,spec):
    limit=spec.get('work_limit',1000000)
    if operation=='real-contact-proof':
        from .planar_certificates import compile_real_contact
        certificate,source=compile_real_contact(spec['a'],spec['b'],spec['c'],spec['d'],work_limit=limit,atom_limit=spec.get('atom_limit',64))
        return {'certificate':certificate,'lean_source':source}
    if operation in ('real-mesh-proof','real-segment-proof','real-route-proof'):
        from .planar_certificates import compile_mesh_coverage,compile_real_segment,compile_real_route
        options={'work_limit':limit,'atom_limit':spec.get('atom_limit',64)}
        if operation=='real-mesh-proof':
            certificate,source=compile_mesh_coverage(spec['vertices'],spec['triangles'],**options)
        elif operation=='real-segment-proof':
            certificate,source=compile_real_segment(spec['obstacles'],spec['start'],spec['end'],**options)
        else:
            from .geometry_certificates import certify_route
            packet=route(spec['obstacles'],spec['start'],spec['end'],work_limit=limit,vertex_limit=spec.get('vertex_limit',200))
            certificate,source=compile_real_route(packet,certify_route(packet,work_limit=limit),**options)
        return {'certificate':certificate,'lean_source':source}
    if operation=='metric-energy-proof':
        from .riemannian_energy import compile_energy_certificate
        certificate,source=compile_energy_certificate(spec,step_limit=spec.get('step_limit',256))
        return {'certificate':certificate,'lean_source':source}
    if operation=='boundary-contact-proof':
        from .geometry_admission import compile_boundary_contact_certificate
        return compile_boundary_contact_certificate(spec['vertices'],spec['start'],spec['end'],work_limit=limit)
    if operation=='refinement-mesh-proof':
        from .geometry_admission import compile_refinement_mesh_certificate
        from .geometry_certificates import certify_mesh
        limits={'work_limit':limit,'triangle_limit':spec.get('triangle_limit',200),'vertex_limit':spec.get('vertex_limit',500)}
        packet=certify_mesh(spec['vertices'],spec['triangles'],**limits)
        return compile_refinement_mesh_certificate(packet,spec['trace'],**limits)
    if operation in ('mesh-certificate','mesh-proof'):
        from .geometry_certificates import certify_mesh,compile_mesh_certificate
        packet=certify_mesh(spec['vertices'],spec['triangles'],work_limit=limit,triangle_limit=spec.get('triangle_limit',200),vertex_limit=spec.get('vertex_limit',500))
        return compile_mesh_certificate(packet,work_limit=limit,triangle_limit=spec.get('triangle_limit',200),vertex_limit=spec.get('vertex_limit',500)) if operation=='mesh-proof' else packet
    if operation in ('route-certificate','route-proof','geometric-route-proof'):
        from .geometry_certificates import certify_route,compile_route_certificate
        packet=route(spec['obstacles'],spec['start'],spec['end'],work_limit=limit,vertex_limit=spec.get('vertex_limit',200))
        certificate=certify_route(packet,work_limit=limit,vertex_limit=spec.get('vertex_limit',200))
        result={'route':packet,'certificate':certificate}
        if operation=='route-proof':result['proof']=compile_route_certificate(packet,certificate,work_limit=limit,vertex_limit=spec.get('vertex_limit',200))
        if operation=='geometric-route-proof':
            from .geometry_admission import compile_geometric_route_certificate
            result['proof']=compile_geometric_route_certificate(packet,certificate,work_limit=limit,vertex_limit=spec.get('vertex_limit',200))
        return result
    if operation=='incidence':
        result={'line':line_through(spec['a'],spec['c'])}
        if 'b' in spec:result['between']=between(spec['a'],spec['b'],spec['c'],strict=spec.get('strict',True))
        if 'other_line' in spec:result['intersection']=meet_lines(result['line'],spec['other_line'])
        return result
    if operation=='polygon':return polygon_structure(spec['vertices'],work_limit=limit)
    if operation=='locate':return {'location':locate_point(spec['vertices'],spec['point'],work_limit=limit)}
    if operation=='triangulate':return triangulate(spec['vertices'],work_limit=limit)
    if operation=='centroid':return polygon_centroid(spec['vertices'],work_limit=limit)
    if operation=='circumcircle':return circumcircle(*spec['triangle'])
    if operation=='incircle':return incircle(*spec['triangle'],spec['point'])
    if operation=='congruence':return fit_isometries(spec['source'],spec['target'])
    if operation=='visibility':return segment_visibility(spec['obstacles'],spec['start'],spec['end'],work_limit=limit)
    if operation=='route':return route(spec['obstacles'],spec['start'],spec['end'],work_limit=limit,vertex_limit=spec.get('vertex_limit',200))
    if operation=='voronoi-mesh-certificate':
        from .geometry_certificates import certify_voronoi_mesh
        packet=voronoi_mesh(spec['sites'],spec['box'],work_limit=limit,site_pair_limit=spec.get('site_pair_limit',10000))
        return {'mesh':packet,'certificate':certify_voronoi_mesh(packet,work_limit=limit,site_pair_limit=spec.get('site_pair_limit',10000))}
    if operation=='voronoi-mesh':return voronoi_mesh(spec['sites'],spec['box'],work_limit=limit,site_pair_limit=spec.get('site_pair_limit',10000))
    if operation=='transport-voronoi':
        from .euclid_geometry import voronoi_cells
        return transport_voronoi(voronoi_cells(spec['sites'],spec['box']),spec['transform'])
    raise ValueError('unknown geometry foundation operation')


def add_commands(sub):
    p=sub.add_parser('geometry-foundations',help='exact incidence, polygon, congruence and obstacle routing')
    p.add_argument('operation',choices=OPERATIONS);p.add_argument('input',help='JSON specification file')


def cli(args):
    if args.command!='geometry-foundations':return False
    with open(args.input) as f:result=dispatch(args.operation,json.load(f))
    print(json.dumps(result,indent=2,sort_keys=True));return True
