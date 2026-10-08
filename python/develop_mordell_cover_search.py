"""Close frontier rank gaps using positive points on stored quartic covers."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
from perfectpower.mordell_cover_search import search_mordell_covers, augment_descent

ROOT = Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--gp'); p.add_argument('--height', type=int, default=1000000)
    p.add_argument('--timeout', type=float, default=5)
    p.add_argument('--workers', type=int, default=4)
    args = p.parse_args()
    if not 1 <= args.workers <= 8: p.error('workers from one through eight')
    folder = ROOT/'receipts/mordell_two_descent'
    inputs = [(path,json.loads(path.read_text())) for path in sorted(folder.glob('[mp]*.json'))]
    inputs = [(path,c) for path,c in inputs if not c['rank_determined']]
    before = len(inputs); results = {}; errors = {}; closed = []
    receipt = ROOT/'receipts/mordell_cover_search.json'
    runs = []
    if receipt.exists():
        previous = json.loads(receipt.read_text())
        if previous.get('schema') != 'pp-mordell-cover-search-frontier/1':
            raise ValueError('unsupported cover-search receipt')
        results = {row['k']:row for row in previous['rows']}
        errors = {int(k):v for k,v in previous['errors'].items()}
        runs = previous.get('runs', [dict(height=previous['height'],
                    requested=previous['requested'],computed=previous['computed'],
                    newly_determined=previous['newly_determined'])])
    processed = 0
    def run(item):
        path,c = item
        search = search_mordell_covers(c,height=args.height,timeout=args.timeout,gp=args.gp)
        if search['lifts']:
            updated = augment_descent(c,search['lifts'])
            path.write_text(json.dumps(updated,indent=2)+'\n')
            search.update(rank_lower_before=c['witness_rank_lower_bound'],
                          rank_lower_after=updated['witness_rank_lower_bound'],
                          rank_upper=updated['rank_upper_bound'],
                          rank_determined=updated['rank_determined'])
        else: search['rank_determined'] = False
        return search
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run,item):item[1]['k'] for item in inputs}
        for f in as_completed(futures):
            k = futures[f]
            processed += 1
            try:
                results[k] = f.result()
                errors.pop(k,None)
                if results[k]['rank_determined']:
                    closed.append(k); print('rank closed',k,flush=True)
            except Exception as e: errors[k] = str(e)
            if processed%40 == 0:
                print('processed',processed,'of',before,flush=True)
    runs.append(dict(height=args.height,requested=before,computed=before-len([k for k in futures.values() if k in errors]),
                     newly_determined=sorted(closed)))
    packet = dict(schema='pp-mordell-cover-search-frontier/1',requested=len(set(results)|set(errors)),
                  computed=len(results),newly_determined=sorted(k for k,row in results.items() if row['rank_determined']),errors=errors,
                  height=args.height,rows=[results[k] for k in sorted(results)],
                  runs=runs,integral_lists_promoted=0,global_empty_proofs=0)
    receipt.write_text(json.dumps(packet,indent=2)+'\n')
    print('Closed',len(closed),'of',before,'rank gaps; errors',errors,flush=True)


if __name__ == '__main__': main()
