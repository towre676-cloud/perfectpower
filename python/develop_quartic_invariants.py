"""Build the contraction atlas and search reduced models of the witness frontier."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
from fractions import Fraction as Q
from perfectpower.binary_invariants import quartic_invariants, contraction_invariants
from perfectpower.quartic_cover_reduction import reduce_cover, search_reduced_box
from perfectpower.mordell_cover_charts import search_cover_box
from perfectpower.mordell_cover_search import augment_descent

ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--height',type=int,default=10000000)
    parser.add_argument('--denominator-max',type=int)
    parser.add_argument('--timeout',type=float,default=8)
    parser.add_argument('--workers',type=int,default=8)
    parser.add_argument('--gp');parser.add_argument('--native-height',type=int,default=30)
    parser.add_argument('--models-only',action='store_true')
    args=parser.parse_args()
    if not 1<=args.workers<=8:parser.error('workers one through eight')
    if not 1<=args.height<=10**9:parser.error('height one through 10^9')
    denominator_max=args.height if args.denominator_max is None else args.denominator_max
    if not 1<=denominator_max<=args.height:parser.error('denominator maximum must lie inside numerator bound')
    if not 0<args.timeout<=60:parser.error('timeout zero through sixty')
    if not 1<=args.native_height<=10000:parser.error('native height one through ten thousand')
    folder=ROOT/'receipts/quartic_invariants';folder.mkdir(exist_ok=True)
    inputs=[];atlas=[]
    for path in sorted((ROOT/'receipts/mordell_two_descent').glob('[mp]*.json')):
        packet=json.loads(path.read_text())
        for i,cover in enumerate(packet['covers']):
            inv=quartic_invariants(cover['quartic']);contract=contraction_invariants(cover['quartic'])
            if any(contract[key]!=inv[key] for key in ('I','J')):raise ArithmeticError('contraction normalization')
            atlas.append(dict(k=packet['k'],cover_index=i,**{key:str(inv[key]) for key in ('I','J','discriminant')}))
        if not packet['rank_determined']:inputs.append((path,packet))
    (folder/'contraction_atlas.json').write_text(json.dumps(dict(schema='pp-quartic-contraction-atlas/1',
        covers=len(atlas),rows=atlas,invariants_establish_equivalence=False),indent=2)+'\n')
    runs=[];receipt=folder/'frontier.json'
    if receipt.exists():runs=json.loads(receipt.read_text()).get('runs',[])
    def process(item):
        path,packet=item;k=packet['k'];models=[];attempts=[];lifts=[];infinite=[]
        for i,cover in enumerate(packet['covers']):
            reduction=reduce_cover(k,cover);models.append(reduction)
            if args.models_only:continue
            native=search_reduced_box(reduction,height=args.native_height)
            attempt=dict(cover_index=i,native=native)
            for lift in native['lifts']:
                u,v,w=lift['source_coordinates']
                if v:lifts.append(dict(cover_index=i,cover_point=[str(Q(u,v)),str(Q(w,v*v))],mordell_point=lift['mordell_point']))
                else:infinite.append(dict(cover_index=i,**lift))
            if not native['lifts']:
                chart=reduction['chart']
                result=search_cover_box(k,chart['cover'],numerator_bound=args.height,
                    denominator_max=denominator_max,timeout=args.timeout,gp=args.gp)
                attempt['pari_status']=result['status']
                from perfectpower.mordell_cover_charts import lift_chart_point
                for found in result['lifts']:
                    lift=lift_chart_point(chart,found['chart_point']);u,v,w=lift['source_coordinates']
                    if v:lifts.append(dict(cover_index=i,cover_point=[str(Q(u,v)),str(Q(w,v*v))],mordell_point=lift['mordell_point']))
                    else:infinite.append(dict(cover_index=i,**lift))
            attempts.append(attempt)
        updated=augment_descent(packet,lifts) if lifts else packet
        # Infinite chart points can be positive witnesses as well; keep their source equation.
        if infinite:
            from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
            E=EllipticCurve([0,k]);points=updated['points'][:]
            for lift in infinite:
                point=encode_point(E.checked(lift['mordell_point']))
                if point not in points:points.append(point)
            certificate=E.independence(points,prime_bound=500,halving_limit=8)
            lower=certificate['rank_lower_bound']
            if not updated['witness_rank_lower_bound']<=lower<=updated['rank_upper_bound']:raise ArithmeticError('point bounds inconsistent')
            updated.update(points=points,independence=certificate,witness_rank_lower_bound=lower,
                rank_determined=lower==updated['rank_upper_bound'])
            updated.setdefault('projective_cover_point_lifts',[]).extend(infinite)
        if lifts or infinite:path.write_text(json.dumps(updated,indent=2)+'\n')
        row=dict(k=k,models=models,attempts=attempts,rank_lower_before=packet['witness_rank_lower_bound'],
                 rank_lower_after=updated['witness_rank_lower_bound'],rank_upper=packet['rank_upper_bound'],
                 rank_determined=updated['rank_determined'])
        (folder/(path.stem+'.json')).write_text(json.dumps(row,indent=2)+'\n')
        return dict(k=k,covers=len(models),models_improved=sum(bool(m['steps']) for m in models),
            rank_lower_before=row['rank_lower_before'],rank_lower_after=row['rank_lower_after'],
            rank_determined=row['rank_determined'],statuses=[a.get('pari_status','native_point' if a['native']['lifts'] else 'native_empty') for a in attempts])
    rows=[];errors={}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures={pool.submit(process,item):item[1]['k'] for item in inputs}
        for future in as_completed(futures):
            k=futures[future]
            try:
                row=future.result();rows.append(row)
                if row['rank_determined']:print('witness gap closed',k,flush=True)
            except Exception as error:errors[k]=str(error)
            if (len(rows)+len(errors))%10==0:print('processed',len(rows)+len(errors),'of',len(inputs),flush=True)
    run=dict(height=args.height,denominator_max=denominator_max,timeout=args.timeout,native_height=args.native_height,
        models_only=args.models_only,requested=len(inputs),rows=sorted(rows,key=lambda r:r['k']),errors=errors,
        improved_models=sum(r['models_improved'] for r in rows),newly_closed=sorted(r['k'] for r in rows if r['rank_determined']))
    runs.append(run)
    receipt.write_text(json.dumps(dict(schema='pp-quartic-invariant-frontier/1',runs=runs,
        integral_lists_promoted=0,global_minimality=False),indent=2)+'\n')
    print({key:value for key,value in run.items() if key!='rows'},flush=True)


if __name__=='__main__':main()
