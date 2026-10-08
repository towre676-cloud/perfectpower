"""Bounded analytic discovery on rank-one isogeny partners; exact positive images."""
import argparse,json,subprocess
from concurrent.futures import ThreadPoolExecutor,as_completed
from pathlib import Path
from perfectpower.elliptic_two_descent import gp_executable
from perfectpower.mordell_three_isogeny import isogeny_point,augment_isogeny_witnesses

ROOT=Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser();p.add_argument('--gp');p.add_argument('--timeout',type=float,default=20)
    p.add_argument('--workers',type=int,default=3);args=p.parse_args()
    if not 0<args.timeout<=60 or not 1<=args.workers<=8:p.error('bounded timeout and workers required')
    items=[(f,json.loads(f.read_text())) for f in (ROOT/'receipts/mordell_two_descent').glob('[mp]*.json')]
    items=[(f,r) for f,r in items if not r['rank_determined'] and r['backend_reported_lower']==r['rank_upper_bound']==1]
    def run(item):
        path,original=item;k=original['k'];row=dict(k=k,partner_k=-27*k,timeout=args.timeout,stack_bytes=512000000,lifts=[])
        script=f'default(parisize,512000000);\ndefault(realprecision,100);\nE=ellinit([0,{-27*k}]);P=ellheegner(E);print("PP_HEEGNER:",vector(#P,j,Str(P[j])));quit\n'
        try:r=subprocess.run([gp_executable(args.gp),'-fq'],input=script,text=True,capture_output=True,timeout=args.timeout,check=True)
        except subprocess.TimeoutExpired:return dict(row,status='timeout')
        warning='***   Warning: new stack size = 512000000 (488.281 Mbytes).'
        lines=[s.split(':',1)[1] for s in r.stdout.splitlines() if s.startswith('PP_HEEGNER:')]
        if len(lines)!=1 or '***' in r.stderr.replace(warning,''):return dict(row,status='backend_error',message=r.stderr[-600:])
        point=json.loads(lines[0]);image=isogeny_point(k,point,dual=True)
        if image is None:return dict(row,status='kernel_point')
        record=dict(source_kind='heegner_partner',partner_point=point,mordell_point=image)
        updated=augment_isogeny_witnesses(original,[record]);path.write_text(json.dumps(updated,indent=2)+'\n')
        return dict(row,status='image_returned',lifts=[record],rank_lower=updated['witness_rank_lower_bound'],rank_determined=updated['rank_determined'])
    rows=[];errors={}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures={pool.submit(run,item):item[1]['k'] for item in items}
        for future in as_completed(futures):
            k=futures[future]
            try:row=future.result();rows.append(row);print(k,row['status'],flush=True)
            except Exception as error:errors[k]=str(error)
    out=ROOT/'receipts/mordell_isogeny_search/heegner_pilot.json'
    old=json.loads(out.read_text()) if out.exists() else None
    runs=old.get('runs',[dict(rows=old['rows'],errors=old['errors'])]) if old else []
    runs.append(dict(rows=sorted(rows,key=lambda r:r['k']),errors=errors))
    out.write_text(json.dumps(dict(schema='pp-mordell-heegner-pilot/1',rows=sorted(rows,key=lambda r:r['k']),errors=errors,runs=runs,
        integral_lists_promoted=0,analytic_rank_claimed=False),indent=2)+'\n')


if __name__=='__main__':main()
