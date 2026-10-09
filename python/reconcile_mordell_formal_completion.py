"""Audit formal bridge proofs without promoting external curve certificates."""
import hashlib,json,re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/mordell_formal_completion'
SOURCES=['PerfectPower/MordellCompletionBridge.lean','audit/MordellCompletionBridge.lean',
         'scripts/check_mordell_completion_bridge.sh','python/reconcile_mordell_formal_completion.py',
         'lean-toolchain','lake-manifest.json']


def audited_declarations(log):
    if 'error:' in log or 'sorryAx' in log or 'Lean.ofReduceBool' in log:
        raise ValueError('failed or non-kernel formal bridge audit')
    groups=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
    free=re.findall(r"'([^']+)' does not depend on any axioms",log)
    allowed={'propext','Classical.choice','Quot.sound'}
    for _,axioms in groups:
        if {a.strip() for a in axioms.split(',') if a.strip()}-allowed:
            raise ValueError('unsupported axiom in formal bridge')
    names=[name for name,_ in groups]+free
    expected={'boundedIndex_of_finite_quotient','mem_of_bounded_multiple','eq_top_of_bounded_index','mem_of_supported_multiple',
              'eq_top_of_prime_support','not_divisible_of_reduction',
              'prime_saturated_of_reduction_separation','mem_integralBox_iff',
              'integralBox_complete','integralList_complete'}
    if {n.removeprefix('PerfectPower.MordellCompletionBridge.') for n in names}!=expected or len(names)!=10:
        raise ValueError('formal bridge audit declaration set mismatch')
    return sorted(names)


def main():
    logs={name:(OUT/name).read_text() for name in ['build.log','axioms.log']}
    if any('error:' in log or 'sorryAx' in log for log in logs.values()):
        raise ValueError('formal bridge did not build')
    declarations=audited_declarations(logs['axioms.log'])
    for name in SOURCES[:2]:
        if re.search(r'\b(sorry|axiom)\b', (ROOT/name).read_text()):
            raise ValueError('unsupported source declaration')
    completion=json.loads((ROOT/'receipts/mordell_completion/summary.json').read_text())
    rows=[dict(k=row['k'],computational_receipt=row['receipt'],
               global_saturation_prime_support='unproved in Lean',
               rank_upper_bound='unproved in Lean',
               global_integral_coordinate_bound='unproved in Lean',
               rational_to_finite_group_reduction='native evidence; Lean connection unproved',
               lean_complete_basis_proved=False,lean_integral_list_proved=False)
          for row in completion['rows']]
    parity_path=ROOT/'receipts/mordell_parity_atlas.json'
    parity_count=0
    if parity_path.exists():
        parity=json.loads(parity_path.read_text())
        if parity['proof_status']!='kernel_checked' or parity['formally_completed_curves']!=0:
            raise ValueError('invalid parity-only closure receipt')
        for name,digest in parity['source_sha256'].items():
            if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
                raise ValueError('parity closure source changed')
        covered={row['k'] for row in parity['rows']}
        if covered!={row['k'] for row in rows}:raise ValueError('parity census coverage mismatch')
        parity_count=len(covered)
        for row in rows:
            row.update(saturation_at_2='proved in Lean for retained basis',
                saturation_at_other_primes='curve-specific proofs still open',
                parity_proof_receipt='receipts/mordell_parity_atlas.json')
    packet=dict(schema='pp-mordell-formal-completion/1',status='partial; global curve proofs open',
                bridge_kernel_checks='passed',audited_declarations=declarations,
                computationally_complete_curves=len(rows),formally_completed_curves=0,
                curves_with_proved_two_saturation=parity_count,
                source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in SOURCES},
                log_sha256={p:hashlib.sha256(log.encode()).hexdigest() for p,log in logs.items()},
                rows=rows,scope='generic composition and bounded enumeration only; no external Boolean is imported as a mathematical proof')
    OUT.mkdir(exist_ok=True)
    (OUT/'status.json').write_text(json.dumps(packet,indent=2)+'\n')
    print(json.dumps({k:packet[k] for k in ['status','bridge_kernel_checks','computationally_complete_curves','formally_completed_curves']}))


if __name__=='__main__':main()
