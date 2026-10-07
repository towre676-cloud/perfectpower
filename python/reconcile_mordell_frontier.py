"""Reconcile census rank conditions against unconditional repository curve theorems."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def reconcile(root=ROOT):
    rows=[json.loads(s) for s in (root/'data/mordell_census.jsonl').read_text().splitlines()]
    assert len({r['k'] for r in rows})==len(rows),'duplicate census curves'
    conditional={r['k']:r for r in rows if r['certification']=='CONDITIONAL_ON_UNPROVEN_RANK'}
    source=(root/'PerfectPower/Generated/MordellDescent.lean').read_text()
    names={-int(d) if sign else int(d):f'PerfectPower.Generated.MordellDescent.no_points_{sign}{d}'
           for sign,d in re.findall(r'theorem no_points_(m?)(\d+)\s',source)}
    descent=json.loads((root/'receipts/mordell_descent.json').read_text())
    assert len(names)==descent['curves']
    closed=sorted(set(conditional)&set(names))
    assert closed==sorted(descent['census_rows_not_independently_certified'])
    registry=json.loads((root/'receipts/mordell_registry.json').read_text())
    known={-r['D']:r['lean'] for r in registry['curves']}
    known.update({r['k']:r['lean'] for r in registry['positive_curves'] if not r.get('premises')})
    additional=sorted((set(conditional)&set(known))-set(closed))
    remaining=[]
    for k in sorted(set(conditional)-set(closed)-set(additional)):
        r=conditional[k]
        remaining.append({'k':k,'x_coordinates':r['x_coordinates'],'rank':r['rank'],
          'rank_proved':r['rank_proved'],'generators':r['generators'],
          'census_label':r['certification'],
          'obligation':'complete_list_with_known_points' if r['x_coordinates'] else 'prove_empty_or_find_missing_points'})
    return {'schema':'pp-mordell-frontier/1','census_curves':len(rows),
      'conditional_census_rows':len(conditional),'unconditional_descent_curves':len(names),
      'descent_closures':[{'k':k,'lean':names[k]} for k in closed],
      'additional_unconditional_list_closures':[{'k':k,'lean':known[k]} for k in additional],
      'remaining_count':len(remaining),'empty_computed_lists':sum(not r['x_coordinates'] for r in remaining),
      'nonempty_computed_lists':sum(bool(r['x_coordinates']) for r in remaining),
      'scope':'reconciled committed census and theorem records; no new rank or completeness proof',
      'remaining':remaining}

if __name__=='__main__':
    packet=reconcile();path=ROOT/'receipts/mordell_frontier.json';path.write_text(json.dumps(packet,indent=2)+'\n')
    print({k:packet[k] for k in ['conditional_census_rows','remaining_count','empty_computed_lists','nonempty_computed_lists']})
