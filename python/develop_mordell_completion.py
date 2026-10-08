"""Full automatic-index-bound saturation followed by integral enumeration.

External eclib completion is kept distinct from the native exact arithmetic
checks. A bounded-prime saturation or a failed backend result cannot close a
curve. Each isolated worker can be restarted independently.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'receipts/mordell_completion'
MARKER = 'PP_MORDELL_COMPLETION:'


def worker(k):
    from math import isqrt
    from sage.all__sagemath_schemes import EllipticCurve
    import sage.all__sagemath_eclib
    import sage.all__sagemath_symbolics
    import sage.version
    from sage.libs.eclib.all import mwrank_MordellWeil
    from sage.rings.rational_field import QQ
    from sage.modules.free_module_element import vector
    from sage.schemes.elliptic_curves.ell_rational_field import EllipticCurve_rational_field
    from perfectpower.mordell_completion import check_completion_arithmetic
    path=ROOT/f'receipts/mordell_two_descent/{"m" if k<0 else "p"}{abs(k)}.json'
    source_bytes=path.read_bytes();source=json.loads(source_bytes)
    if not source['rank_determined']:
        raise ArithmeticError('matching rank witnesses required')
    E=EllipticCurve([0,k]);points=[E([QQ(x),QQ(y)]) for x,y in source['points']]
    minimal=E.minimal_model();phi=E.isomorphism_to(minimal)
    triples=[]
    for p in points:
        x,y=phi(p).xy();d=x.denominator().lcm(y.denominator())
        triples.append([int(x*d),int(y*d),int(d)])
    mw=mwrank_MordellWeil(minimal.mwrank_curve(),True)
    mw.process(triples,saturation_bound=0)
    ok,index,unsaturated=mw.saturate(max_prime=-1,min_prime=2)
    unsaturated_primes=[int(p) for p in re.findall(r'\d+',str(unsaturated))]
    if not ok or unsaturated_primes:
        raise ArithmeticError(f'global saturation failed: {unsaturated}')
    basis=[(~phi)(minimal(p)) for p in mw.points()]
    if len(basis)!=source['rank_upper_bound'] or int(mw.rank())!=len(basis):
        raise ArithmeticError('saturated basis rank differs from retained rank bound')
    pairing=E.height_pairing_matrix(basis,precision=192)
    relations=[]
    for p in points:
        rhs=vector(pairing.base_ring(),[(p.height(precision=192)+q.height(precision=192)-(p-q).height(precision=192))/2 for q in basis])
        cs=[int(c.round()) for c in pairing.solve_right(rhs)]
        if sum((n*q for n,q in zip(cs,basis)),E(0))!=p:
            raise ArithmeticError('height-proposed subgroup relation fails exact arithmetic')
        relations.append(cs)
    intervals=[]
    def exact_interval(self,xmin,xmax):
        xmin,xmax=int(xmin),int(xmax)
        if xmax-xmin>10**7:
            raise ArithmeticError('interval exceeds exact enumeration budget')
        a4,a6=int(self.a4()),int(self.a6());xs=[]
        for x in range(xmin,xmax+1):
            n=x**3+a4*x+a6
            if n>=0 and isqrt(n)**2==n:xs.append(x)
        intervals.append(dict(min=xmin,max=xmax,x_coordinates=xs))
        return set(xs)
    # Replace only the historical PARI interval-search crash path. This is an
    # exhaustive exact scan of the very same interval, never a truncation.
    EllipticCurve_rational_field.integral_x_coords_in_interval=exact_interval
    integral=E.integral_points(mw_base=basis,both_signs=True,verbose=True)
    packet=dict(schema='pp-mordell-completion/1',k=k,curve=source['curve'],
        engine=f'passagemath {sage.version.version}: eclib automatic-index-bound saturation; Sage integral_points',
        source_descent=str(path.relative_to(ROOT)),source_sha256=hashlib.sha256(source_bytes).hexdigest(),
        source_points=source['points'],rank_upper_bound=source['rank_upper_bound'],
        basis_points=[[str(c) for c in p.xy()] for p in basis],
        original_to_basis=relations,saturation_max_prime=-1,saturation_min_prime=2,
        backend_saturation_ok=bool(ok),unsaturated_primes=unsaturated_primes,
        source_subgroup_index=int(index),regulator_approximation=str(mw.regulator()),
        complete_basis_by_backend=True,integral_points=[[str(c) for c in p.xy()] for p in integral],
        x_coordinates=sorted({int(p[0]) for p in integral}),exact_interval_scans=intervals,
        integral_enumeration_method='integral_points(mw_base=globally_saturated_basis, both_signs=True)',
        integral_list_complete_by_backend=True,lean_complete_basis_proved=False,
        lean_integral_list_proved=False)
    packet.update(check_completion_arithmetic(packet,source))
    print(MARKER+json.dumps(packet),flush=True)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--worker',type=int)
    parser.add_argument('--workers',type=int,default=4);parser.add_argument('--timeout',type=float,default=180)
    parser.add_argument('--keys');parser.add_argument('--refresh',action='store_true')
    args=parser.parse_args()
    if args.worker is not None:
        worker(args.worker);return
    if not 1<=args.workers<=8 or not 0<args.timeout<=600:parser.error('bounded workers and timeout required')
    sources={json.loads(p.read_text())['k']:p for p in (ROOT/'receipts/mordell_two_descent').glob('[mp][0-9]*.json')}
    keys=sorted(map(int,args.keys.split(','))) if args.keys else sorted(sources)
    if not set(keys)<=set(sources):parser.error('keys must belong to retained frontier')
    OUT.mkdir(exist_ok=True)
    def run(k):
        name=f'{"m" if k<0 else "p"}{abs(k)}';path=OUT/(name+'.json')
        source_hash=hashlib.sha256(sources[k].read_bytes()).hexdigest()
        if path.exists() and not args.refresh:
            old=json.loads(path.read_text())
            if old.get('status')=='complete' and old['source_sha256']==source_hash:return old
        started=time.monotonic()
        try:
            result=subprocess.run([sys.executable,__file__,'--worker',str(k)],cwd=ROOT,
                text=True,capture_output=True,timeout=args.timeout)
            lines=[line[len(MARKER):] for line in result.stdout.splitlines() if line.startswith(MARKER)]
            log='\n'.join(line for line in result.stdout.splitlines() if not line.startswith(MARKER))+'\n'+result.stderr
            (OUT/(name+'.log')).write_text(log)
            if result.returncode!=0 or len(lines)!=1:raise RuntimeError(log[-2000:])
            packet=json.loads(lines[0]);packet.update(status='complete',elapsed_seconds=round(time.monotonic()-started,3))
        except subprocess.TimeoutExpired:
            packet=dict(k=k,status='timeout',timeout_seconds=args.timeout)
        except Exception as error:
            packet=dict(k=k,status='error',error=str(error))
        path.write_text(json.dumps(packet,indent=2)+'\n');return packet
    rows=[]
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures={pool.submit(run,k):k for k in keys}
        for f in as_completed(futures):
            row=f.result();rows.append(row)
            if row['status']!='complete' or len(rows)%20==0:
                print(len(rows),'/',len(keys),row['k'],row['status'],flush=True)
    packets=[json.loads(p.read_text()) for p in OUT.glob('[mp][0-9]*.json')]
    complete=sorted((p for p in packets if p.get('status')=='complete'),key=lambda p:p['k'])
    census={r['k']:r for r in map(json.loads,(ROOT/'data/mordell_census.jsonl').read_text().splitlines())}
    changed=[dict(k=p['k'],before=census[p['k']]['x_coordinates'],after=p['x_coordinates'],
                  added=sorted(set(p['x_coordinates'])-set(census[p['k']]['x_coordinates'])),
                  removed=sorted(set(census[p['k']]['x_coordinates'])-set(p['x_coordinates'])))
             for p in complete if p['x_coordinates']!=census[p['k']]['x_coordinates']]
    summary=dict(schema='pp-mordell-completion-frontier/1',baseline_commit='7a99f461b0268b7bdc4b10f63a8c4dac269ec196',
        frontier_curves=len(sources),complete_bases_by_backend=len(complete),
        integral_lists_complete_by_backend=len(complete),remaining=sorted(set(sources)-{p['k'] for p in complete}),
        empty_integral_lists=sum(not p['x_coordinates'] for p in complete),
        nonempty_integral_lists=sum(bool(p['x_coordinates']) for p in complete),
        integral_points_both_signs=sum(len(p['integral_points']) for p in complete),
        subgroup_enlargements=[dict(k=p['k'],index=p['source_subgroup_index']) for p in complete if p['source_subgroup_index']>1],
        changed_integral_lists=changed,lean_list_closures=0,
        rows=[dict(k=p['k'],rank=p['rank_upper_bound'],source_subgroup_index=p['source_subgroup_index'],
                   x_coordinates=p['x_coordinates'],receipt=f'receipts/mordell_completion/{"m" if p["k"]<0 else "p"}{abs(p["k"])}.json') for p in complete])
    (OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print({k:v for k,v in summary.items() if k not in ('rows','subgroup_enlargements')},flush=True)


if __name__=='__main__':main()
