"""Reproduce source-bound native arithmetic, residue and marked-word packets."""
import argparse
import json
from pathlib import Path
from perfectpower.native_rational_certificate import rational_certificate, two_torsion_certificate
from perfectpower.native_residue_certificate import residue_certificate
from perfectpower.native_braid_certificate import braid_certificate
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch
import tempfile

ROOT=Path(__file__).resolve().parents[1]


def bounded(lo,hi,*extra):
    return dict(op='and',args=[dict(poly=[-lo,1],relation='>='),dict(poly=[-hi,1],relation='<=')]+list(extra))


def develop(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    families={
        'rational':[rational_certificate(f) for f in [ ['-3/2',0,6],[0,0,-1,0,1],[2],
                        [1,0,1],[-1,3,-3,1],[-2,-4],['1/2','-3/2',1],[-1,0,0,0,0,0,0,0,1]]],
        'torsion':[two_torsion_certificate(dict(ainvs=a)) for a in [[0,0,0,-1,0],[0,0,0,0,-2],[1,2,3,-4,5]]],
        'residue':[residue_certificate(p) for p in [
            bounded(-10**30,10**30,dict(poly=[0,1],relation='=',modulus=6,value=1),dict(poly=[0,1],relation='=',modulus=9,value=4)),
            bounded(-50,50,dict(op='or',args=[dict(poly=[0,1],relation='=',modulus=3,value=0),dict(poly=[0,1],relation='=',modulus=4,value=1)]),dict(op='not',args=[dict(poly=[0,1],relation='=',modulus=6,value=0)])),
            bounded(-40,40,dict(poly=[3,-2],relation='>=',modulus=5,value=2)),False,
            bounded(-20,20,dict(poly=[0,1],relation='=',modulus=6,value=1),dict(poly=[0,1],relation='=',modulus=9,value=2))]],
        'braid':[braid_certificate(g,w) for g,w in [(1,[1,2,3,-3,-2,-1]),(2,[1,2,-1,3,4,5]),
                         (3,[-1,2,3,4,-5,6,7,1]),(4,[1,2,3,4,5,6,7,8,9]),(2,[])]]}
    for family,packets in families.items():
        (output/(family+'.json')).write_text(json.dumps(packets,indent=2,sort_keys=True)+'\n')
        imports='import PerfectPower.NativeRationalRoots\nimport PerfectPower.EllipticPointDivision\nimport PerfectPower.ResiduePopulation\nimport PerfectPower.PicardLefschetz\n'
        source=imports+'\n'.join('\n'.join(line for line in p['lean'].splitlines() if not line.startswith('import ')) for p in packets)+'\n'
        (ROOT/'audit'/('NativeBridge_'+family+'.lean')).write_text(source)
    requests=[dict(op='native_rational_certificate',args=dict(coefficients=[-1,0,4])),
              dict(op='native_residue_certificate',args=dict(predicate=bounded(-10**30,10**30,dict(poly=[0,1],relation='=',modulus=7,value=3)))),
              dict(op='native_two_torsion_certificate',args=dict(specification=dict(ainvs=[1,2,3,-4,5]))),
              dict(op='native_braid_certificate',args=dict(genus=3,word=[1,2,3,-2,4,5,6,7]))]
    with tempfile.TemporaryDirectory() as directory,Catalogue(Path(directory)/'db') as catalogue:
        rows=[dict(request=r,response=dispatch(catalogue,r)) for r in requests]
    (output/'service.json').write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')
    print({k:len(v) for k,v in families.items()})


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=ROOT/'receipts/native_bridges');args=parser.parse_args();develop(args.output)
