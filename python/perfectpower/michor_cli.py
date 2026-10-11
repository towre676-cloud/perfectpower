"""JSON interface for conformal dynamics and smooth chart-domain comparisons."""
import json
from . import michor_geometry as M
OPERATIONS=('compile','point','dynamics','bridge','distance','winner','pullback','tube','trace','plane')
def metric(spec):
    if 'coefficients' in spec:return M.hyperelliptic_metric(spec['coefficients'],spec.get('chart','finite'),spec.get('branch'))
    return M.compile_metric(spec['numerator'],spec['denominator_squared'])
def dispatch(operation,spec):
    if operation=='plane':
        p,b=M.bounded_plane_bridge();result={'metric':p,'bridge':b}
        if 'start' in spec:result['distance']=M.bridge_distances(p,b,spec['start'],spec['end'])
        if 'sites' in spec:result['winner']=M.bridge_winner(p,b,spec['center'],spec['sites'],spec['site'],spec['radius'])
        return result
    p=metric(spec)
    if operation=='compile':return p
    if operation=='point':return M.evaluate_metric(p,spec['point'],bits=spec.get('bits',64))
    if operation=='dynamics':return M.dynamics(p,spec['point'],spec['velocity'],transport=spec.get('transport'),variation=spec.get('variation'),momentum=spec.get('momentum'),bits=spec.get('bits',64))
    if operation in ('bridge','distance','winner'):
        b=M.certify_domain(p,spec['box'],spec['lower_scale'],spec['upper_scale'],depth=spec.get('depth',4),node_limit=spec.get('node_limit',10000))
        result={'metric':p,'bridge':b}
        if operation=='distance':result['distance']=M.bridge_distances(p,b,spec['start'],spec['end'],bits=spec.get('bits',64))
        if operation=='winner':result['winner']=M.bridge_winner(p,b,spec['center'],spec['sites'],spec['site'],spec['radius'],bits=spec.get('bits',64))
        return result
    if operation=='pullback':return M.pullback_metric(p,spec['coordinate_map'])
    if operation=='tube':return M.certify_flow_tube(p,spec['initial_box'],spec['tube_box'],spec['time'],iterations=spec.get('iterations',4))
    if operation=='trace':return M.trace_geodesic(p,spec['initial'],spec['time'],spec['steps'],transport=spec.get('transport',(1,0)),variation=spec.get('variation',(0,0,0,1)))
    raise ValueError('unknown conformal geometry operation')
def add_commands(sub):
    p=sub.add_parser('differential-geometry',help='exact conformal metrics, chart transport, dynamics and smooth-distance bridges')
    p.add_argument('operation',choices=OPERATIONS);p.add_argument('input',help='JSON input path')
def cli(args):
    if args.command!='differential-geometry':return False
    with open(args.input) as f:print(json.dumps(dispatch(args.operation,json.load(f)),indent=2,sort_keys=True))
    return True
