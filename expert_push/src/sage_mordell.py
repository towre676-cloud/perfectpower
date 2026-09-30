"""sage -python src/sage_mordell.py --k -1 --out receipts/sage_minus1.json
Unexecuted adapter; external algorithm evidence, never automatic Lean promotion.
"""
import argparse,json,traceback
from sage.all import EllipticCurve,QQ,proof
from sage.env import SAGE_VERSION
p=argparse.ArgumentParser();p.add_argument('--k',type=int,required=True);p.add_argument('--out',required=True);a=p.parse_args()
r={'k':a.k,'status':'external_algorithm_evidence','lean_certified':False,'sage_version':SAGE_VERSION,'model':[0,0,0,0,a.k]}
try:
 if not a.k:raise ValueError('singular curve')
 proof.all(True)
 E=EllipticCurve(QQ,[0,0,0,0,a.k])
 r['rank_bounds']=[int(z) for z in E.rank_bounds()]
 points=E.integral_points(both_signs=True)
 r['points']=sorted([[int(P[0]),int(P[1])] for P in points])
 assert all(y*y==x*x*x+a.k for x,y in r['points'])
 r['remaining_formal_premises']=['complete Mordell-Weil basis and saturation','effective integral-point bound','proof replay in pinned Lean toolchain']
except Exception as e:r.update(status='blocked',error=str(e),traceback=traceback.format_exc())
from pathlib import Path
Path(a.out).parent.mkdir(parents=True,exist_ok=True)
Path(a.out).write_text(json.dumps(r,indent=2))
