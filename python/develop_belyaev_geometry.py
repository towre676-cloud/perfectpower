"""Regenerate Belyaev-inspired exact geometry examples and proof sources."""
import json
from pathlib import Path
from perfectpower.belyaev_cli import dispatch
from perfectpower.belyaev_geometry import fit_isometries,apply_isometry,triangulate,incircle,circumcircle
from perfectpower.geometry_lean import compile_isometry,compile_triangulation_area


def main():
    out=Path('receipts/belyaev_geometry');out.mkdir(parents=True,exist_ok=True)
    for operation in ('triangulate','route','congruence','voronoi-mesh','transport-voronoi'):
        spec=json.loads(Path(f'examples/belyaev_geometry/{operation}.json').read_text())
        packet=dispatch(operation,spec)
        (out/f'{operation}.json').write_text(json.dumps(packet,indent=2)+'\n')
    source=[[0,0],[3,0],[0,4]]
    maps=[('Rotation',{'matrix':[['3/5','-4/5'],['4/5','3/5']],'translation':['7/3','-2/7']}),
          ('Reflection',{'matrix':[['3/5','4/5'],['4/5','-3/5']],'translation':['7/3','-2/7']})]
    for name,transform in maps:
        target=[apply_isometry(transform,p) for p in source]
        fit=fit_isometries(source,target)
        compiled=compile_isometry(fit['transforms'][0])
        (out/f'{name}.lean').write_text(compiled.pop('source'))
        (out/f'{name}-proof.json').write_text(json.dumps(compiled,indent=2)+'\n')
    compiled=compile_triangulation_area(triangulate([[0,0],[4,0],[4,4],[2,2],[0,4]]))
    (out/'TriangleAreas.lean').write_text(compiled.pop('source'))
    (out/'TriangleAreas-proof.json').write_text(json.dumps(compiled,indent=2)+'\n')
    triangle=[[0,0],[4,0],[0,4]]
    (out/'circle.json').write_text(json.dumps({'triangle':triangle,'circle':circumcircle(*triangle),
        'queries':[{'point':p,**incircle(*triangle,p)} for p in [[2,2],[4,4],[5,5]]]},indent=2)+'\n')
    n=2**60;triangle=[[0,0],[n,0],[0,n]];p=[n,n-1]
    center=float(n)/2;radius=float(n)**2/2
    distance=(float(p[0])-center)**2+(float(p[1])-center)**2
    stress={'coordinate_scale':n,'triangle':triangle,'point':p,'exact':incircle(*triangle,p),
            'binary64':'INSIDE' if distance<radius else 'OUTSIDE' if distance>radius else 'ON',
            'scope':'one retained adversarial predicate example; no general floating-point failure-rate claim'}
    (out/'precision-stress.json').write_text(json.dumps(stress,indent=2)+'\n')


if __name__=='__main__':main()
