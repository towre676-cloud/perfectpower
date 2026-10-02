"""Search for reusable p=3 matrix certificates among monic positive-k sources.

From the second OEIS handoff (`scan_skolem3_candidates.py`), unchanged except for this note.
Coordinates: a source of `receipts/positive_k_next.json` has `z^3 + p z + q = 0`, i.e.
`RankOne` with `P = -p`, `Q = -q`.  Run:
  python3 python/skolem3_scan.py --receipt receipts/positive_k_next.json --radius 6 \
      --output receipts/skolem3_candidates.json
The candidates for k = 4, 33, 49, 81 are now certified in Lean (`python/rank_one_sources.py`,
`Generated/RankOneSources.lean`), where the box shows that their inverses generate the units.

Bounded unit search is discovery only. A reported candidate does not prove
unit generation or a complete Thue solution set. The modular conditions are
exact integer checks and match the shape used by the k=2 Skolem3 argument.
"""

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path


def mat(x, p, q):
    a, b, c = x
    return ((a, -q*c, -q*b),
            (b, a-p*c, -p*b-q*c),
            (c, b, a-p*c))


def mm(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))


I = ((1,0,0),(0,1,0),(0,0,1))


def norm(x, p, q):
    m = mat(x,p,q)
    return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
            -m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
            +m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))


def modular_corner_cert(x, p, q):
    a = mat(x,p,q)
    a2 = mm(a,a)
    a3 = mm(a2,a)
    if any((a3[i][j]-I[i][j])%3 for i in range(3) for j in range(3)):
        return None
    d = tuple(tuple((a3[i][j]-I[i][j])//3 for j in range(3)) for i in range(3))
    if not (a[2][0]%3 and a2[2][0]%3 and d[2][0]%3):
        return None
    return {'unit': list(x), 'norm': norm(x,p,q),
            'A20': a[2][0], 'A2_20': a2[2][0], 'D20': d[2][0]}


def scan(receipt, radius):
    d = json.loads(receipt.read_text())
    all_by_curve=Counter(src['k'] for src in d['equations'])
    rows=[]
    for src in d['equations']:
        order=src['monic_order']
        if order is None:continue
        p,q=order['p'],order['q']
        found=[]
        for x in itertools.product(range(-radius,radius+1),repeat=3):
            if x==(0,0,0) or x[1:]==(0,0):continue
            n=norm(x,p,q)
            if abs(n)!=1:continue
            cert=modular_corner_cert(x,p,q)
            if cert:found.append(cert)
        # This ordering is only a computational priority, not a claim that
        # the first candidate generates the full unit group.
        found.sort(key=lambda c:(max(abs(t) for t in c['unit']),
                                 sum(abs(t) for t in c['unit']),c['unit']))
        rows.append({'k':src['k'], 'form':src['form'], 'p':p,'q':q,
                     'searched_coordinate_radius':radius,
                     'candidate':found[0] if found else None,
                     'known_points':src['known_points']})
    return {'scope':'bounded unit candidates with exact p=3 matrix checks; no unit-generation or all-exponent proof',
            'summary':{'monic_sources':len(rows),
                       'with_p3_candidate':sum(r['candidate'] is not None for r in rows),
                       'one_source_curves_with_p3_candidate':sum(r['candidate'] is not None and
                           all_by_curve[r['k']]==1 for r in rows)},
            'rows':rows}


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--receipt',type=Path,required=True)
    ap.add_argument('--radius',type=int,default=6)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    assert 1<=args.radius<=25
    r=scan(args.receipt,args.radius)
    if args.output:args.output.write_text(json.dumps(r,indent=1,sort_keys=True)+'\n')
    print(json.dumps(r['summary'],sort_keys=True))
    for x in r['rows']:
        if x['k']==2:print('k2',x['candidate'])
