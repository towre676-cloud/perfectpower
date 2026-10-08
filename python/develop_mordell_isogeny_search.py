"""Discover on 3-isogenous partners; apply retained images in a separate phase."""
import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
import json
from pathlib import Path
import subprocess
from perfectpower.mordell_three_isogeny import partner_covers,isogeny_point,augment_isogeny_witnesses
from perfectpower.quartic_cover_reduction import reduce_cover
from perfectpower.mordell_cover_charts import search_cover_box,lift_chart_point

ROOT=Path(__file__).resolve().parents[1]


def main():
    p=argparse.ArgumentParser();p.add_argument('--gp');p.add_argument('--height',type=int,default=10000000)
    p.add_argument('--denominator-max',type=int);p.add_argument('--timeout',type=float,default=8)
    p.add_argument('--workers',type=int,default=4);p.add_argument('--apply-only',action='store_true')
    p.add_argument('--keys',help='comma-separated original Mordell coefficients')
    args=p.parse_args();denom=args.height if args.denominator_max is None else args.denominator_max
    if not 1<=args.workers<=8 or not 1<=denom<=args.height<=10**9 or not 0<args.timeout<=60:p.error('bounded positive controls required')
    folder=ROOT/'receipts/mordell_isogeny_search';folder.mkdir(exist_ok=True)
    def source_path(k):return ROOT/'receipts/mordell_two_descent'/(('m' if k<0 else 'p')+str(abs(k))+'.json')
    if args.apply_only:
        rows=[];errors={}
        for path in sorted(folder.glob('[mp]*.json')):
            row=json.loads(path.read_text());k=row['k'];source=source_path(k)
            original=json.loads(source.read_text());records=[record for run in row['runs'] for record in run['lifts']]
            if not records:continue
            try:updated=augment_isogeny_witnesses(original,records)
            except Exception as error:
                errors[k]=str(error);continue
            source.write_text(json.dumps(updated,indent=2)+'\n')
            rows.append(dict(k=k,before=original['witness_rank_lower_bound'],after=updated['witness_rank_lower_bound'],
                             upper=updated['rank_upper_bound'],newly_closed=not original['rank_determined'] and updated['rank_determined']))
        (folder/'application.json').write_text(json.dumps(dict(schema='pp-mordell-isogeny-application/1',rows=rows,
            errors=errors,integral_lists_promoted=0,newly_closed=[r['k'] for r in rows if r['newly_closed']],
            matched_after_application=[r['k'] for r in rows if r['after']==r['upper']]),indent=2)+'\n')
        print('Applied',len(rows),'curves; newly closed',[r['k'] for r in rows if r['newly_closed']],'errors',errors,flush=True);return
    inputs=[json.loads(path.read_text()) for path in sorted((ROOT/'receipts/mordell_two_descent').glob('[mp]*.json'))]
    inputs=[row for row in inputs if not row['rank_determined']]
    if args.keys:
        keys={int(k) for k in args.keys.split(',')}
        inputs=[row for row in inputs if row['k'] in keys]
    def search(original):
        k=original['k'];path=folder/source_path(k).name
        if path.exists():row=json.loads(path.read_text())
        else:
            try:packet=partner_covers(k,timeout=min(30,args.timeout+10),gp=args.gp)
            except subprocess.TimeoutExpired:return dict(k=k,status='cover_discovery_timeout',covers=0,lifts=0)
            row=dict(schema='pp-mordell-isogeny-search/1',k=k,partner=packet,runs=[])
        attempts=[];lifts=[]
        for i,cover in enumerate(row['partner']['covers']):
            reduction=reduce_cover(-27*k,cover);chart=reduction['chart']
            result=search_cover_box(-27*k,chart['cover'],numerator_bound=args.height,
                denominator_max=denom,timeout=args.timeout,gp=args.gp)
            attempt=dict(cover_index=i,reduction=reduction,status=result['status'])
            for found in result['lifts']:
                partner=lift_chart_point(chart,found['chart_point']);point=partner['mordell_point']
                image=isogeny_point(k,point,dual=True)
                if image is None:attempt['status']='point_in_dual_kernel';continue
                lifts.append(dict(cover_index=i,partner_cover=cover,
                    partner_coordinates=partner['source_coordinates'],partner_point=point,mordell_point=image))
            attempts.append(attempt)
        row['runs'].append(dict(height=args.height,denominator_max=denom,timeout=args.timeout,
                               attempts=attempts,lifts=lifts,global_empty_proof=False))
        path.write_text(json.dumps(row,indent=2)+'\n')
        return dict(k=k,status='images_returned' if lifts else 'no_image_returned',
                    covers=len(attempts),lifts=len(lifts),cover_statuses=[a['status'] for a in attempts])
    rows=[];errors={}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures={pool.submit(search,row):row['k'] for row in inputs}
        for future in as_completed(futures):
            k=futures[future]
            try:
                row=future.result();rows.append(row)
                if row['lifts']:print('isogeny images found',k,flush=True)
            except Exception as error:errors[k]=str(error)
            if (len(rows)+len(errors))%10==0:print('processed',len(rows)+len(errors),'of',len(inputs),flush=True)
    summary=folder/'summary.json';runs=json.loads(summary.read_text()).get('runs',[]) if summary.exists() else []
    runs.append(dict(requested=len(inputs),height=args.height,denominator_max=denom,timeout=args.timeout,
        rows=sorted(rows,key=lambda r:r['k']),errors=errors))
    summary.write_text(json.dumps(dict(schema='pp-mordell-isogeny-search-frontier/1',runs=runs,
        integral_lists_promoted=0),indent=2)+'\n')
    print('Images',sum(r['lifts'] for r in rows),'errors',errors,flush=True)


if __name__=='__main__':main()
