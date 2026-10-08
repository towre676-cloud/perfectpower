"""Attach exact reduction exclusions at every backend-required saturation prime."""
import hashlib,json,re
from pathlib import Path
from perfectpower.elliptic_reduction_saturation import reduction_saturation
ROOT=Path(__file__).resolve().parents[1]


def main():
    folder=ROOT/'receipts/mordell_completion';rows=[]
    for path in sorted(folder.glob('[mp][0-9]*.json')):
        packet=json.loads(path.read_text())
        if packet.get('status')!='complete':continue
        log=path.with_suffix('.log').read_text()
        bounds=[int(n) for n in re.findall(r'Saturation index bound[^=]*=\s*(\d+)',log)]
        required=sorted({int(p) for s in re.findall(r'Checking saturation at\s*\[([^]]*)\]',log) for p in re.findall(r'\d+',s)})
        if not bounds:raise ArithmeticError('missing automatically computed global index bound')
        proofs=[reduction_saturation(packet['k'],packet['basis_points'],ell) for ell in required]
        if not all(p['independent_mod_prime'] for p in proofs):
            raise ArithmeticError(f'finite-reduction sieve unresolved at {packet["k"]}')
        packet.update(backend_index_bound=max(bounds),backend_required_saturation_primes=required,
                      backend_log_sha256=hashlib.sha256(log.encode()).hexdigest(),
                      exact_prime_saturation=proofs)
        path.write_text(json.dumps(packet,indent=2)+'\n')
        rows.append(dict(k=packet['k'],index_bound=max(bounds),primes=required,
                         largest_auxiliary_prime=max([s['auxiliary_prime'] for p in proofs for s in p['reductions']]+[0])))
        if len(rows)%50==0:print(len(rows),'exact curve saturation packets',flush=True)
    summary=dict(schema='pp-mordell-reduction-saturation-frontier/1',curves=len(rows),
        prime_checks=sum(len(r['primes']) for r in rows),
        maximum_backend_index_bound=max(r['index_bound'] for r in rows),
        maximum_auxiliary_prime=max(r['largest_auxiliary_prime'] for r in rows),rows=rows,
        global_height_index_bound_source='external eclib; not a native height-bound theorem')
    (folder/'reduction_saturation_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print({k:v for k,v in summary.items() if k!='rows'})


if __name__=='__main__':main()
