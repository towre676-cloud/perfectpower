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
    rank_results=root/'receipts/mordell_two_descent'
    rank_determined=0;rank_corrections=[];backend_determined=0;backend_corrections=[]
    for k in sorted(set(conditional)-set(closed)-set(additional)):
        r=conditional[k]
        remaining.append({'k':k,'x_coordinates':r['x_coordinates'],'rank':r['rank'],
          'rank_proved':r['rank_proved'],'generators':r['generators'],
          'census_label':r['certification'],
          'obligation':'complete_list_with_known_points' if r['x_coordinates'] else 'prove_empty_or_find_missing_points'})
        rank_file=rank_results/(('m' if k<0 else 'p')+str(abs(k))+'.json')
        if rank_file.exists():
            evidence=json.loads(rank_file.read_text())
            lower,upper=evidence['witness_rank_lower_bound'],evidence['rank_upper_bound']
            assert evidence['schema']=='pp-mordell-two-descent/1' and evidence['k']==k
            assert type(lower) is int and type(upper) is int and 0<=lower<=upper
            assert evidence['rank_determined'] is (lower==upper)
            remaining[-1].update(rank_lower_bound=lower,rank_upper_bound=upper,
                census_rank=r['rank'],rank_evidence=str(rank_file.relative_to(root)),
                lean_rank_proved=False)
            assert evidence['field']['bnfcertify']==1 and evidence['field']['nfcertify']==[]
            backend_lower=evidence['backend_reported_lower']
            assert type(backend_lower) is int and 0<=backend_lower<=upper
            backend_equal=backend_lower==upper
            remaining[-1].update(backend_rank_lower_bound=backend_lower,
                backend_rank_determined=backend_equal,witness_rank_determined=lower==upper,
                rank_bound_source='PARI ellrank lower and upper endpoints; bnfcertify retained')
            if backend_equal:
                remaining[-1].update(rank=upper,rank_proved=True);backend_determined+=1
                if upper!=r['rank']:backend_corrections.append(dict(k=k,census_rank=r['rank'],proved_rank=upper))
            if lower==upper:
                remaining[-1].update(rank=lower,rank_proved=True);rank_determined+=1
                if lower!=r['rank']:rank_corrections.append(dict(k=k,census_rank=r['rank'],proved_rank=lower))
    witness_frontier=remaining
    computation_closed=[];remaining=[]
    completion_dir=root/'receipts/mordell_completion'
    for row in witness_frontier:
        k=row['k'];path=completion_dir/f'{"m" if k<0 else "p"}{abs(k)}.json'
        if path.exists():
            import hashlib
            packet=json.loads(path.read_text())
            source_path=root/row['rank_evidence']
            valid=(packet.get('schema')=='pp-mordell-completion/1'
                and packet.get('status')=='complete' and packet.get('k')==k
                and packet.get('source_sha256')==hashlib.sha256(source_path.read_bytes()).hexdigest()
                and packet.get('saturation_max_prime')==-1 and packet.get('saturation_min_prime')==2
                and packet.get('backend_saturation_ok') is True and packet.get('unsaturated_primes')==[]
                and packet.get('complete_basis_by_backend') is True
                and packet.get('integral_list_complete_by_backend') is True
                and packet.get('exact_relations_checked') is True
                and packet.get('exact_integral_points_checked') is True
                and packet.get('rank_upper_bound')==row['rank_upper_bound'])
            if valid:
                from perfectpower.mordell_completion import accept_completion,verify_completion_log
                log_path=path.with_suffix('.log')
                valid=(log_path.exists() and verify_completion_log(packet,log_path.read_text())
                       and accept_completion(packet,json.loads(source_path.read_text())))
            if valid:
                computation_closed.append(dict(k=k,receipt=str(path.relative_to(root)),
                    x_coordinates=packet['x_coordinates'],complete_basis_by_backend=True,
                    integral_list_complete_by_backend=True,lean_integral_list_proved=False))
                continue
        remaining.append(row)
    return {'schema':'pp-mordell-frontier/1','census_curves':len(rows),
      'conditional_census_rows':len(conditional),'unconditional_descent_curves':len(names),
      'descent_closures':[{'k':k,'lean':names[k]} for k in closed],
      'additional_unconditional_list_closures':[{'k':k,'lean':known[k]} for k in additional],
      'external_computation_list_closures':computation_closed,
      'external_computation_list_closure_count':len(computation_closed),
      'rank_witness_frontier':witness_frontier,
      'rank_witness_frontier_count':len(witness_frontier),
      'remaining_count':len(remaining),'empty_computed_lists':sum(not r['x_coordinates'] for r in remaining),
      'nonempty_computed_lists':sum(bool(r['x_coordinates']) for r in remaining),
      'ranks_determined_by_two_descent':rank_determined,
      'ranks_determined_by_backend_bounds':backend_determined,
      'ranks_with_matching_point_witnesses':rank_determined,
      'backend_census_rank_corrections':backend_corrections,'census_rank_corrections':rank_corrections,
      'scope':'retained historical census; exact rank witnesses; external full saturation and integral-list completions tracked separately from Lean list proofs',
      'remaining':remaining}

if __name__=='__main__':
    packet=reconcile();path=ROOT/'receipts/mordell_frontier.json';path.write_text(json.dumps(packet,indent=2)+'\n')
    print({k:packet[k] for k in ['conditional_census_rows','remaining_count','empty_computed_lists','nonempty_computed_lists']})
