"""Replay saved higher-genus surfaces with producer-independent witnesses."""
import gzip
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
from perfectpower.voronoi_certificate import produce, verify, transfer_piece, SurfaceSpace

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/voronoi_witness';OUT.mkdir(exist_ok=True)
meshes=json.loads((ROOT/'receipts/analytic_geometry/conformal_curve_meshes.json').read_text())
heats=json.loads((ROOT/'receipts/analytic_geometry/higher_genus_intrinsic_voronoi.json').read_text())
rows=[]
for mesh,heat in zip(meshes,heats):
    packet=produce(mesh,heat['sites'],heat['distance_fields'],1)
    assert verify(mesh,packet)
    raw=(json.dumps(packet,separators=(',',':'))+'\n').encode()
    name=heat['name'];path=OUT/(name+'.json.gz');path.write_bytes(gzip.compress(raw,mtime=0))
    assert verify(mesh,json.loads(gzip.decompress(path.read_bytes())))
    proven=sum((Q(p['face_area_fraction']) for p in packet['pieces'] if p['site'] is not None),Q(0))
    comparison=[]
    for l,u in [(Q(1),Q(1)),(Q(99,100),Q(101,100)),(Q(9,10),Q(11,10))]:
        retained=sum((Q(p['face_area_fraction']) for p in packet['pieces'] if transfer_piece(p,l,u)['winner_index'] is not None),Q(0))
        comparison.append({'lower_scale':str(l),'upper_scale':str(u),'conditional_assigned_face_fraction_sum':str(retained),'comparison_proved':False})
    space=SurfaceSpace(mesh,packet); assigned=0
    for face in range(len(mesh['triangles'])):
        for point in [(1,0,0),(0,1,0),(0,0,1),(Q(1,3),Q(1,3),Q(1,3))]:
            query=space.point(face,point)
            assert all(Q(a)<=Q(b) for a,b in zip(query['lower'],query['upper']))
            assert query['possible_nearest_sites']
            assigned+=query['unique_winner'] is not None
    row={'query_statistics':space.statistics(),'queries_with_strict_winner':assigned,'name':name,'genus':mesh['genus'],'vertices':mesh['vertices'],'faces':len(mesh['triangles']),
         'leaves':len(packet['pieces']),'fields':len(packet['fields']),
         'path_witnesses':sum(map(len,packet['paths'])),'proven_face_fraction_sum':str(proven),
         'unresolved_face_fraction_sum':str(len(mesh['triangles'])-proven),
         'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'compressed_bytes':path.stat().st_size,
         'conditional_comparisons':comparison,'independent_replay':True,'kernel_checked_packet':False}
    rows.append(row);print(json.dumps(row),flush=True)
(OUT/'summary.json').write_text(json.dumps({'surfaces':rows,'scope':'Exact decimal-rational polyhedral metrics; no established smooth-curve comparisons.'},indent=2)+'\n')
