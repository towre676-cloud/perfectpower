"""Reproduce native actual halving fibres and cold public operations."""
import json
import tempfile
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.native_halves_certificate import halves_certificate
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch
ROOT=Path(__file__).resolve().parents[1]

def develop():
    out=ROOT/'receipts/native_halves';out.mkdir(parents=True,exist_ok=True)
    fixtures=[([-1,0],None,None),([0,-2],[3,5],None),([-1,0],[0,0],None)]
    for spec,p in [([0,-2],[3,5]),([-25,0],['25/4','75/8']),([1,'-1/4',1,'-1/2','-9/4'],[3,3])]:
        E=EllipticCurve(spec);fixtures.append((spec,encode_point(E.mul(p,2)),p))
    packets=[halves_certificate(spec,target,anchor=anchor) for spec,target,anchor in fixtures]
    for i,p in enumerate(packets):(out/f'packet_{i}.json').write_text(json.dumps(p,indent=2)+'\n')
    imports='import PerfectPower.EllipticPointDivision\nimport Mathlib.Tactic.Linter.Lint\n'
    source=imports+'\n'.join('\n'.join(line for line in p['lean'].splitlines() if not line.startswith('import ')) for p in packets)
    source+='\n#print axioms PerfectPower.EllipticPointDivision.half_supplies_quartic_root\n#print axioms PerfectPower.EllipticPointDivision.no_half_of_quartic_root_free\n#lint in PerfectPower.EllipticPointDivision\n'
    (ROOT/'audit/NativeHalves.lean').write_text(source)
    requests=[dict(op='native_halves_certificate',args=dict(specification=spec,target=target,anchor=anchor)) for spec,target,anchor in fixtures]
    with tempfile.TemporaryDirectory() as d,Catalogue(Path(d)/'db') as cat:
        rows=[dict(request=r,response=dispatch(cat,r)) for r in requests]
    (out/'service.json').write_text(json.dumps(rows,indent=2)+'\n')
    print('Generated',len(packets),'native halving packets')
if __name__=='__main__':develop()
