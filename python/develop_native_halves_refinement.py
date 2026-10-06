"""Retain the closed native halving interfaces on original actual point groups."""
import json,tempfile,re
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.native_halves_certificate import halves_certificate
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch
ROOT=Path(__file__).resolve().parents[1]

def develop():
    out=ROOT/'receipts/native_halves_refinement';out.mkdir(parents=True,exist_ok=True)
    rows=[([-1,0],None,{}),([0,-2],[3,5],{}),([-1,0],[0,0],{}),([1,0],[0,0],{})]
    for spec,p in [([0,-2],[3,5]),([-25,0],['25/4','75/8']),([1,'-1/4',1,'-1/2','-9/4'],[3,3])]:
        E=EllipticCurve(spec);rows.append((spec,encode_point(E.mul(p,2)),dict(anchor=p)))
    E=EllipticCurve([0,-7])
    for p in [[2,1],[2,-1]]:rows.append(([0,-7],encode_point(E.mul(p,2)),dict(route='quartic')))
    packets=[halves_certificate(spec,target,**kw) for spec,target,kw in rows]
    for i,p in enumerate(packets):(out/f'packet_{i}.json').write_text(json.dumps(p,indent=2)+'\n')
    source='import PerfectPower.EllipticQuarticLifts\nimport Mathlib.Tactic.Linter.Lint\n'
    source+='\n'.join('\n'.join(line for line in p['lean'].splitlines() if not line.startswith('import ')) for p in packets)
    reusable=['EllipticSquareTransport.'+name for name in ['discriminant','equation','nonsingular','vertical','slope_shift','same_x','addX_shift','addY_shift','forward_add','fibre','coordinates_injective','coordinates_cast','coordinates_backward','list_transport']]+['EllipticQuarticLifts.mem_lifts','EllipticQuarticLifts.fibre_complete']
    source+='\n'+'\n'.join('#print axioms PerfectPower.'+n for n in reusable)+'\n#lint in PerfectPower.EllipticSquareTransport\n#lint in PerfectPower.EllipticQuarticLifts\n'
    (ROOT/'audit/NativeHalvesRefinement.lean').write_text(source)
    with tempfile.TemporaryDirectory() as d,Catalogue(Path(d)/'db') as c:
        requests=[dict(op='native_halves_certificate',args=dict(specification=spec,target=target,**kw)) for spec,target,kw in rows]
        responses=[dict(request=r,response=dispatch(c,r)) for r in requests]
    (out/'service.json').write_text(json.dumps(responses,indent=2)+'\n')
    print('Generated',len(packets),'packets and',len(re.findall(r'#print axioms',source)),'audit declarations')
if __name__=='__main__':develop()
