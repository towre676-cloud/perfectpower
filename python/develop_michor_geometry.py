"""Build Michor-inspired metric, dynamics, bridge and chart examples."""
from pathlib import Path
import json,math
from fractions import Fraction as Q
from perfectpower import michor_geometry as M,bernstein_boxes as B
from perfectpower.michor_lean import compile_dynamics,compile_bridge
OUT=Path('receipts/michor_geometry')
def save(name,value):(OUT/(name+'.json')).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
def proof(name,value):
    (OUT/(name+'.lean')).write_text(value.pop('source'));save(name+'-proof',value)

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    sphere=M.compile_metric([[0,0,4]],B.power({(0,0):Q(1),(2,0):Q(1),(0,2):Q(1)},4))
    hyper=M.compile_metric([[0,0,1]],[[0,4,1]])
    flat=M.compile_metric([[0,0,1]],[[0,0,1]])
    coeff=[0,-1,0,0,0,1]
    finite=M.hyperelliptic_metric(coeff);branch=M.hyperelliptic_metric(coeff,'branch',branch=0);infinity=M.hyperelliptic_metric(coeff,'infinity')
    plane,global_bridge=M.bounded_plane_bridge()
    for name,p in [('Sphere',sphere),('Hyperbolic',hyper),('FiniteCurve',finite),('BranchCurve',branch),('InfinityCurve',infinity),('BoundedPlane',plane)]:
        save(name,p)
        if name in ['Sphere','Hyperbolic']:proof(name+'Dynamics',compile_dynamics(p))
        if name=='FiniteCurve':proof('FiniteCurvePoint',compile_dynamics(p,point=[2,0]))
    for name,p,box,l,u in [('FiniteBridge',finite,[2,'9/4',0,'1/4'],'1/4',1),
                           ('BranchBridge',branch,['-1/4','1/4','-1/4','1/4'],1,3),
                           ('InfinityBridge',infinity,['-1/4','1/4','-1/4','1/4'],1,3)]:
        b=M.certify_domain(p,box,l,u,depth=2);save(name,b);proof(name,compile_bridge(p,b))
    save('GlobalPlaneBridge',global_bridge);proof('GlobalPlaneBridge',compile_bridge(plane,global_bridge))
    save('GlobalPlaneQueries',{'distance':M.bridge_distances(plane,global_bridge,[0,0],[3,4]),
        'winner':M.bridge_winner(plane,global_bridge,[0,0],{'near':[0,0],'far':[3,4]},'near',1)})
    save('FiniteCurveQuery',M.dynamics(finite,[2,0],[1,1],transport=[1,0],variation=[0,0,1,0],momentum=[1,1]))
    invert=[{'numerator':[[1,0,1]],'denominator':[[2,0,1],[0,2,1]]},{'numerator':[[0,1,1]],'denominator':[[2,0,1],[0,2,1]]}]
    square=[{'numerator':[[2,0,1],[0,2,-1]],'denominator':[[0,0,1]]},{'numerator':[[1,1,2]],'denominator':[[0,0,1]]}]
    transport=M.pullback_metric(sphere,invert);save('SphereChartTransport',transport)
    overlap=M.pullback_metric(finite,square)
    check={'points':[],'scope':'branch overlap x=t^2 only at nonzero t; regular branch point supplied independently by BranchCurve'}
    for p in [['1/3','1/5'],['1/4',0]]:
        a=M._eval(overlap['metric']['density_squared'],*map(Q,p));b=M._eval(branch['density_squared'],*map(Q,p));assert a==b
        check['points'].append({'point':list(map(str,p)),'squared_density':str(a)})
    save('BranchChartTransport',overlap);save('BranchOverlapChecks',check)
    tube=M.certify_flow_tube(sphere,[[1,1],[0,0],[0,0],[1,1]],[['9/10','11/10'],['-1/10','1/10'],['-1/5','1/5'],['9/10','11/10']],'1/100')
    save('SphereTube',tube)
    save('FlatTube',M.certify_flow_tube(flat,[[0,0],[0,0],[1,1],[2,2]],[[-1,1],[-1,1],[1,1],[2,2]],'1/10'))
    traces={'sphere':M.trace_geodesic(sphere,[1,0,0,1],str(2*math.pi),300,transport=[1,0],variation=[0,0,1,0]),
            'hyperbolic':M.trace_geodesic(hyper,[0,1,1,0],2,100),
            'curve':M.trace_geodesic(finite,[2,'1/10','1/5','1/10'],'1/2',80)}
    for name,t in traces.items():save(name+'-trace',t)
    Path('web/michor_geometry/data.js').write_text('window.MICHOR_DATA='+json.dumps({'traces':traces,'sphere_tube':tube,'global_plane':global_bridge,'curve_query':M.evaluate_metric(finite,[2,0])},separators=(',',':'))+';\n')
    specs={'sphere':{'numerator':[[0,0,4]],'denominator_squared':B.encode(B.power({(0,0):Q(1),(2,0):Q(1),(0,2):Q(1)},4)),'point':[1,0],'velocity':[0,1],'transport':[1,0],'variation':[0,0,1,0],'momentum':[0,1]},
           'curve':{'coefficients':coeff,'box':[2,'9/4',0,'1/4'],'lower_scale':'1/4','upper_scale':1,'start':[2,0],'end':['9/4','1/4']},
           'plane':{'start':[0,0],'end':[3,4],'center':[0,0],'sites':{'near':[0,0],'far':[3,4]},'site':'near','radius':1}}
    for name,spec in specs.items():Path('examples/michor_geometry/'+name+'.json').write_text(json.dumps(spec,indent=2)+'\n')
    save('summary',{'curve':'y^2=x^5-x','sphere_curvature':'1','hyperbolic_curvature':'-1','curve_curvature_at_2':'-12/25',
        'continuous_rectangle_bridges':3,'global_plane_bridge':True,'source_bound_lean_examples':7,'flow_tubes':2,
        'trace_diagnostics':{k:{'maximum_energy_drift':v['maximum_energy_drift'],'maximum_transport_norm_drift':v['maximum_transport_norm_drift']} for k,v in traces.items()},
        'scope':'actual continuous chart domains and explicit smooth plane; compact higher-genus global distance remains open'})
if __name__=='__main__':main()
