"""Reproduce five/seven subgroup presentations and bounded saturation."""
import json
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.elliptic_subgroup_verifier import verify_subgroup_preimage
from perfectpower.elliptic_saturation_verifier import verify_saturation


def main():
    output = Path(__file__).resolve().parents[1]/'receipts'/'elliptic_five_seven'
    output.mkdir(parents=True, exist_ok=True)
    E = EllipticCurve([0, 0, 1, -1, 0]); P = E.checked([0, 0])
    F = EllipticCurve([-4, 1]); A = F.checked([0, 1]); B = F.checked([2, 1])
    examples = {}
    for p in (5, 7):
        examples[f'recover_{p}'] = E.subgroup_preimage([E.mul(P, p)], p)
        examples[f'primitive_{p}'] = E.subgroup_preimage([P], p)
        examples[f'dependent_{p}'] = E.subgroup_preimage([P, P], p)
        examples[f'hidden_{p}'] = F.subgroup_preimage([F.add(A, B), F.add(F.mul(A, p-1), F.neg(B))], p)
        T = EllipticCurve([0, -1, -1, 0, 0] if p == 5 else [-1, -4, -4, 0, 0])
        examples[f'torsion_kernel_{p}'] = T.subgroup_preimage([], p)
        examples[f'torsion_source_{p}'] = T.subgroup_preimage([[0, 0]], p)
    for name, packet in examples.items():
        if not verify_subgroup_preimage(packet): raise AssertionError(name)
    examples['saturate_35'] = E.bounded_saturation([E.mul(P, 35)], primes=[5, 7])
    examples['bounded_one_step'] = E.bounded_saturation([E.mul(P, 35)], primes=[5, 7], max_steps=1)
    examples['saturate_all_four'] = E.bounded_saturation([E.mul(P, 35)], primes=[2, 3, 5, 7], max_steps=16)
    for name in ('saturate_35', 'bounded_one_step', 'saturate_all_four'):
        if not verify_saturation(examples[name]): raise AssertionError(name)
    for name in ('saturate_35', 'saturate_all_four'):
        if examples[name]['status'] != 'closed' or examples[name]['generators'] != [['0', '0']]:
            raise AssertionError(f'unfinished claimed closure: {name}')
    summary = {}
    for name, packet in examples.items():
        (output/f'{name}.json').write_text(json.dumps(packet, indent=2)+'\n')
        summary[name] = dict(schema=packet['schema'], generators=packet['generators'], root_nodes=packet['root_nodes'])
        if 'coefficient_presentation' in packet:
            summary[name].update(relation_basis=packet['relation_basis'], coefficient_index=packet['coefficient_presentation']['coefficient_index'])
        else:
            summary[name].update(status=packet['status'], closed_primes=packet['closed_primes'], stages=len(packet['stages']))
    (output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(f'{len(examples)} reproducible examples written to {output}')


if __name__ == '__main__': main()
