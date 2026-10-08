"""Run general two-descent on the committed Mordell frontier, with checkpoints."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
from perfectpower.elliptic_two_descent import mordell_two_descent

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--gp');parser.add_argument('--workers',type=int,default=4)
    parser.add_argument('--effort',type=int,default=0);parser.add_argument('--timeout',type=float,default=30)
    parser.add_argument('--limit',type=int);parser.add_argument('--refresh',action='store_true');args=parser.parse_args()
    if not 1<=args.workers<=8:parser.error('workers one through eight')
    rows=json.loads((ROOT/'receipts/mordell_frontier.json').read_text())['remaining']
    if args.limit is not None:rows=rows[:args.limit]
    out=ROOT/'receipts/mordell_two_descent';out.mkdir(exist_ok=True)
    completed={};failed={}
    def run(row):
        name=('m' if row['k']<0 else 'p')+str(abs(row['k']))+'.json';path=out/name
        if path.exists() and not args.refresh:
            packet=json.loads(path.read_text())
            if packet['k']==row['k'] and (packet['rank_determined'] or packet['effort']>=args.effort):return packet
        packet=mordell_two_descent(row['k'],row['generators'],gp=args.gp,effort=args.effort,timeout=args.timeout)
        path.write_text(json.dumps(packet,indent=2)+'\n');return packet
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures={pool.submit(run,row):row for row in rows}
        for future in as_completed(futures):
            row=futures[future]
            try:completed[row['k']]=future.result()
            except Exception as error:failed[row['k']]=str(error)
            done=len(completed)+len(failed)
            if done%40==0 or done==len(rows):print(f'{done}/{len(rows)}: {len(completed)} results, {len(failed)} failures',flush=True)
    summary=dict(schema='pp-mordell-two-descent-frontier/1',requested=len(rows),computed=len(completed),
                 rank_determined=sum(c['rank_determined'] for c in completed.values()),
                 rank_upper_one=sum(c['rank_upper_bound']==1 for c in completed.values()),
                 cassels_improved=sum(c['cassels_removed_dimension']>0 for c in completed.values()),
                 nonmaximal_power_orders=sum(c['field']['power_order_index']>1 for c in completed.values()),
                 quartic_covers=sum(len(c['covers']) for c in completed.values()),failed=failed,
                 integral_lists_promoted=0,lean_rank_proofs=0,
                 rows=[dict(k=k,rank_lower=c['witness_rank_lower_bound'],rank_upper=c['rank_upper_bound'],
                            rank_determined=c['rank_determined'],selmer_dimension=c['selmer_dimension'],
                            cassels_removed=c['cassels_removed_dimension'],order_index=c['field']['power_order_index'])
                       for k,c in sorted(completed.items())])
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print({k:v for k,v in summary.items() if k!='rows'},flush=True)


if __name__=='__main__':main()
