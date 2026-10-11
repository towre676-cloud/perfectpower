"""Rebuild all-real source geometry certificates; kernel acceptance is separate."""
from pathlib import Path
import json
from perfectpower.planar_certificates import compile_mesh_coverage,compile_real_segment,compile_real_route,compile_real_contact
from perfectpower.belyaev_geometry import triangulate
from perfectpower.polygon_routing import route
from perfectpower.geometry_certificates import certify_route
out=Path('receipts/planar_closure');out.mkdir(parents=True,exist_ok=True);summary={}
def save(name,receipt,source):
    (out/(name+'.lean')).write_text(source)
    (out/(name+'.json')).write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    summary[name]={'schema':receipt['schema'],'source_sha256':receipt['proof']['source_sha256'],'bytes':len(source.encode())}
square=[[0,0],[2,0],[2,2],[0,2]]
concave=[[0,0],[4,0],[4,1],[1,1],[1,4],[0,4]]
meshes={
 'Square':(square,[[[0,0],[2,0],[2,2]],[[0,0],[2,2],[0,2]]]),
 'Steiner':(square,[[square[i],square[(i+1)%4],[1,1]] for i in range(4)]),
 'Concave':(concave,triangulate(concave)['triangles']),
}
for name,(v,t) in meshes.items():
    r,s=compile_mesh_coverage(v,t,namespace=name,work_limit=4000000);save(name,r,s)
    print(name,r['tree_statistics'],len(s),flush=True)
segments={
 'Boundary':([square],[-1,0],[3,0]),
 'Tangent':([square],[-1,1],[1,-1]),
 'Crossing':([square],[-1,1],[3,1]),
 'Notch':([concave],[2,2],[3,3]),
 'Overlap':([square,square],[-1,0],[3,0]),
 'Rational':([square],['-1/3','-1/7'],['7/3','-1/7']),
}
for name,(p,a,b) in segments.items():
    r,s=compile_real_segment(p,a,b,namespace=name);save(name,r,s);print(name,len(s),flush=True)
for name,p,a,b in [('ZeroRoute',[],[0,0],[0,0]),('RealRoute',[],['1/3','2/7'],['4/3','9/7']),
                   ('ObstacleRoute',[square],[0,0],[2,2])]:
    packet=route(p,a,b);certificate=certify_route(packet)
    r,s=compile_real_route(packet,certificate,work_limit=4000000);save(name,r,s);print(name,len(s),flush=True)
for name,args in {'RealContactCrossing':([0,0],[2,2],[0,2],[2,0]),'RealContactOverlap':([0,0],[3,0],[1,0],[4,0]),'RealContactTangent':([0,0],[1,1],[1,1],[2,0]),'RealContactDisjoint':([0,0],[1,0],[2,0],[3,0])}.items():
    r,s=compile_real_contact(*args,namespace=name);save(name,r,s);print(name,len(s),flush=True)
(out/'summary.json').write_text(json.dumps(summary,sort_keys=True,indent=2)+'\n')
