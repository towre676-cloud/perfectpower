"""Retain geometry-interpreted route and pointwise refinement certificates."""
import json
from pathlib import Path
from perfectpower.geometry_admission import compile_geometric_route_certificate, compile_refinement_mesh_certificate,compile_boundary_contact_certificate
from perfectpower.geometry_certificates import certify_route,certify_mesh
from perfectpower.polygon_routing import route

OUT=Path('receipts/geometry_admission')
def save(name,proof,spec):
    (OUT/(name+'.lean')).write_text(proof['source'])
    metadata={k:v for k,v in proof.items() if k!='source'}
    (OUT/(name+'.json')).write_text(json.dumps({'specification':spec,'proof':metadata},sort_keys=True,indent=2)+'\n')

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    square=[[0,0],[2,0],[2,2],[0,2]]
    concave=[[0,0],[6,0],[6,5],[4,5],[4,2],[2,2],[2,5],[0,5]]
    ring=[[[-3,1],[3,1],[3,3],[-3,3]],[[-3,-3],[3,-3],[3,-1],[-3,-1]],
          [[-3,-3],[-1,-3],[-1,3],[-3,3]],[[1,-3],[3,-3],[3,3],[1,3]]]
    examples=[('Square',[square],[-1,1],[3,1]),('Concave',[concave],[3,3],[3,6]),
        ('Tangent',[square],[-1,1],[1,-1]),('BoundaryOverlap',[square,square],[-1,0],[3,0]),
        ('Rational',[square],['-1/3','1/7'],['7/3','1/7']),('Zero',[],[0,0],[0,0]),
        ('Disconnected',ring,[0,0],[5,0])]
    for name,obstacles,start,end in examples:
        packet=route(obstacles,start,end);certificate=certify_route(packet)
        proof=compile_geometric_route_certificate(packet,certificate)
        save(name,proof,{'route':packet,'certificate':certificate})
    triangle=[[0,0],[6,0],[0,6]]
    mesh=[[[0,0],[6,0],[3,3]],[[0,0],[3,3],[0,6]]]
    trace=[{'triangle':0,'parameter':'1/2'}]
    packet=certify_mesh(triangle,mesh);save('Refinement',compile_refinement_mesh_certificate(packet,trace),{'mesh':packet,'trace':trace})
    for name,polygon,a,b in [('ContactOverlap',[[0,0],[4,0],[4,4],[0,4]],[1,0],[3,0]),
                              ('ContactTangent',square,[-1,1],[1,-1]),
                              ('ContactDisjoint',concave,[3,3],[3,4]),
                              ('ContactCrossing',square,[-1,1],[3,1])]:
        proof=compile_boundary_contact_certificate(polygon,a,b)
        save(name,proof,{'polygon':polygon,'start':a,'end':b})
    (OUT/'summary.json').write_text(json.dumps({'route_certificates':len(examples),'refinement_certificates':1,'boundary_contact_certificates':4,
        'scope':'universal rational segment winding avoidance; source-derived complete finite graph; all-walk Manhattan optimality/unreachability; triangular source refinement coverage; general polygon-chain coverage remains open'},indent=2)+'\n')

if __name__=='__main__':main()
