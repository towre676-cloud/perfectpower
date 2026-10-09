"""Retain actual kernel audits of all 457 rational-group parity closures."""
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT=Path(__file__).resolve().parents[1]


def main():
    log=Path(sys.argv[1]).read_text()
    if any(s in log for s in ('error:','sorryAx','ofReduceBool')):raise ValueError('failed kernel atlas')
    audited=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    names=[]
    for name,axs in audited:
        if {a.strip() for a in axs.split(',') if a.strip()}-{'propext','Classical.choice','Quot.sound'}:raise ValueError('unsupported axiom')
        names.append(name)
    names+=re.findall(r"'([^']+)' does not depend on any axioms",log)
    sources=json.loads((ROOT/'data/mordell_parity_sources.json').read_text())
    expected=[]
    for row in sources['rows']:
        k=row['k'];tag=('m' if k<0 else 'p')+str(abs(k));ns='PerfectPower.MordellParityAtlas.Curve_'+tag+'.'
        expected.extend(ns+t for t in ['double_injective','two_saturated',*[f'no_half{j}' for j in range(len(row['halving_moduli']))]])
        if hashlib.sha256((ROOT/row['source_receipt']).read_bytes()).hexdigest()!=row['source_sha256']:raise ValueError('census source changed')
    if sorted(names)!=sorted(expected):raise ValueError('curve audit set mismatch')
    census=json.loads((ROOT/'receipts/mordell_completion/summary.json').read_text())
    if {r['k'] for r in census['rows']}!={r['k'] for r in sources['rows']}:raise ValueError('hard census coverage mismatch')
    paths=['PerfectPower/EllipticDivision.lean','PerfectPower/MordellParity.lean','data/mordell_parity_sources.json',*sources['proof_blocks']]
    packet=dict(schema='pp-mordell-parity-atlas/1',proof_status='kernel_checked',curves=len(sources['rows']),
        rank_one=sum(r['rank']==1 for r in sources['rows']),rank_two=sum(r['rank']==2 for r in sources['rows']),
        parity_obstructions=sum(len(r['halving_moduli']) for r in sources['rows']),audited_declarations=sorted(names),
        source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
        audit_sha256=hashlib.sha256(log.encode()).hexdigest(),rows=sources['rows'],
        execution_verified=False,formally_completed_curves=0,
        scope='unconditional saturation at 2 of each retained rank-one/rank-two basis inside the actual rational elliptic point group; rank upper bounds, saturation at other primes and global integral coordinate bounds remain open')
    (ROOT/'receipts/mordell_parity_atlas.json').write_text(json.dumps(packet,indent=2)+'\n')
    print(json.dumps({k:packet[k] for k in ('curves','rank_one','rank_two','parity_obstructions','proof_status','formally_completed_curves')}))


if __name__=='__main__':main()
