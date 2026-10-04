"""Reproduce exact topology and rational Voronoi enclosure corpus."""
import json
import gzip
from pathlib import Path
from perfectpower.symplectic_surface import surface_basis
from perfectpower.certified_voronoi import boundary_enclosure
root=Path(__file__).resolve().parents[1]
meshes=json.loads((root/'receipts/analytic_geometry/conformal_curve_meshes.json').read_text())
heat=json.loads((root/'receipts/analytic_geometry/higher_genus_intrinsic_voronoi.json').read_text())
out=root/'receipts/certified_surface';out.mkdir(exist_ok=True)
summary=[]
for mesh,h in zip(meshes,heat):
    name=h['name'];basis=surface_basis(mesh)
    cert=boundary_enclosure(mesh,h['sites'],h['distance_fields'],1)
    (out/(name+'_basis.json')).write_text(json.dumps(basis,separators=(',',':'))+'\n')
    (out/(name+'_voronoi.json.gz')).write_bytes(gzip.compress((json.dumps(cert,separators=(',',':'))+'\n').encode(),mtime=0))
    row={'name':name,'genus':mesh['genus'],'generators':len(basis['dual_generator_cycles']),
         'pieces':len(cert['pieces']),'proven_face_fraction_sum':cert['proven_face_fraction_sum'],
         'unresolved_face_fraction_sum':cert['unresolved_face_fraction_sum']}
    summary.append(row);print(row,flush=True)
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
