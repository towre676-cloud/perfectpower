"""Reproduce independent geometry acceptance examples and source-bound Lean."""
import json
from pathlib import Path
from perfectpower.geometry_certificates import certify_mesh,compile_mesh_certificate,certify_route,compile_route_certificate,certify_voronoi_mesh
from perfectpower.belyaev_geometry import triangulate,apply_isometry,voronoi_mesh
from perfectpower.polygon_routing import route

OUT=Path('receipts/geometry_certificates')
def save(name,value):(OUT/(name+'.json')).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
def proof(name,value):
    (OUT/(name+'.lean')).write_text(value.pop('source'));save(name+'-proof',value)

def main():
    OUT.mkdir(exist_ok=True,parents=True)
    square=[[0,0],[4,0],[4,4],[0,4]]
    fan=[[[0,0],[4,0],[2,2]],[[4,0],[4,4],[2,2]],[[4,4],[0,4],[2,2]],[[0,4],[0,0],[2,2]]]
    junction=[[[0,0],[4,0],[4,4]],[[0,0],[2,2],[0,4]],[[2,2],[4,4],[0,4]]]
    concave=[[0,0],[6,0],[6,5],[4,5],[4,2],[2,2],[2,5],[0,5]]
    transform={'matrix':[['3/5','-4/5'],['4/5','3/5']],'translation':['7/3','-2/7']}
    image=lambda p:apply_isometry(transform,p)
    for name,polygon,triangles in [('SteinerFan',square,fan),('TJunction',square,junction),
                                   ('Concave',concave,triangulate(concave)['triangles']),
                                   ('RationalMesh',list(map(image,square)),[list(map(image,t)) for t in fan])]:
        packet=certify_mesh(polygon,triangles);save(name,packet);proof(name,compile_mesh_certificate(packet))
    obstacle=[[0,0],[2,0],[2,2],[0,2]]
    ring=[[[-3,1],[3,1],[3,3],[-3,3]],[[-3,-3],[3,-3],[3,-1],[-3,-1]],
          [[-3,-3],[-1,-3],[-1,3],[-3,3]],[[1,-3],[3,-3],[3,3],[1,3]]]
    for name,obstacles,start,end in [('SquareRoute',[obstacle],[-1,1],[3,1]),
                                    ('ZeroRoute',[],[0,0],[0,0]),
                                    ('RationalRoute',[],['1/3','2/7'],['4/3','9/7']),
                                    ('Unreachable',ring,[0,0],[5,0])]:
        packet=route(obstacles,start,end);certificate=certify_route(packet)
        save(name,{'route':packet,'certificate':certificate});proof(name,compile_route_certificate(packet,certificate))
    mesh=voronoi_mesh({'a':[0,0],'b':[2,0],'c':[1,2],'duplicate':[0,0],'far':[100,100]},[[-1,-1],[3,3]])
    save('Voronoi',{'mesh':mesh,'certificate':certify_voronoi_mesh(mesh)})
    (Path('examples/geometry_certificates')/'mesh.json').write_text(json.dumps({'vertices':square,'triangles':fan},indent=2)+'\n')
    (Path('examples/geometry_certificates')/'route.json').write_text(json.dumps({'obstacles':[obstacle],'start':[-1,1],'end':[3,1]},indent=2)+'\n')
    save('summary',{'mesh_certificates':4,'route_certificates':4,'voronoi_certificates':1,
                    'square_route_cost':'6','steiner_square_area':'16',
                    'scope':'independent certificate checks and source-bound Lean arithmetic; no global Euclidean routing or full Lean polygon topology'})
if __name__=='__main__':main()
