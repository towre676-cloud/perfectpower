"""Export replayable browser math and current source/receipt provenance.

The browser's established mathematical payload remains byte-identical to its
retained Site version. Fresh receipt digests identify the reconstructed source
and actual exhaustive computations; the retained historical digests remain in
retained_browser_evidence.json instead of masquerading as new execution.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT/'web/integral-families/browser-data.json'


def read(path):
    return json.loads((ROOT/path).read_text())


def file_digest(path):
    return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()


def payload():
    first = read('receipts/period_bridge/results.json')
    summary = read('receipts/period_bridge/summary.json')
    deep = read('receipts/period_bridge_deep/results.json')
    adjoint = read('receipts/period_bridge_deep/e8_lift.json')
    generating = deep['generating']
    e8 = first['e8']
    lift = dict(schema='pp-e8-chevalley-tits-lift/1', dimension=adjoint['dimension'],
                cartan_dimension=8, root_spaces=240,
                adjoint_identification='verified actual Tits/Chevalley lift; diagonally conjugate on roots to eight regular 30-cycles',
                arithmetic='exact integer sparse bracket and finite adjoint exponentials; not Lean',
                characteristic_polynomial='(x^30-1)^8 * Phi_30(x)',
                cycle_products=[row['sign_product'] for row in adjoint['signed_root_orbits']],
                lie_bracket_verification=dict(alternating_basis_checks=adjoint['alternating_basis_checks'],
                                             complete_basis_triple_sweep=adjoint['exhaustive_checks_executed'],
                                             jacobi_basis_triples=adjoint['jacobi_distinct_basis_triples'],
                                             skew_basis_pairs=adjoint['skew_symmetry_basis_pairs']),
                lift_bracket_verification=dict(bracket_pairs_per_lift=adjoint['skew_symmetry_basis_pairs'],
                                              complete_basis_pair_sweep=adjoint['exhaustive_checks_executed'],
                                              simple_lifts=8,
                                              total_lift_bracket_checks=adjoint['lift_bracket_preservation_pairs']),
                lift_order=adjoint['coxeter_order'], mellin_domain=adjoint['domain'],
                weight_two_integral=adjoint['weight_two_pi_squared_coefficient'])
    pair_keys = ('A', 'D', 'cancellation_jets', 'convergence', 'harmonic_coefficients',
                 'r', 's', 'scope', 'source', 'theorem', 'weight', 'zeta_coefficients')
    e8_keys = ('combined_model', 'coxeter_order', 'cyclotomic_bridge', 'exponents',
               'pi_coefficients', 'root_orbit_lengths', 'roots')
    cyclotomic_keys = ('even_weight_checks', 'parameters', 'symbolic_identity')
    return dict(angles=first['raghava']['exact_angle_specializations'],
                pairs=[{key: str(row[key]) if key in ('A', 'D') else row[key] for key in pair_keys} for row in first['raghava']['two_order_identities']],
                cyclotomic={key: first['cyclotomic'][key] for key in cyclotomic_keys},
                e8={**{key: e8[key] for key in e8_keys},
                    '_adjoint_verified': adjoint['actual_adjoint_identification_checked'], 'adjoint_lift': lift},
                generating={key: generating[key] for key in ('families', 'family_count', 'maximum_order', 'maximum_weight', 'scope', 'source')},
                proof_scope=first['proof_scope'], source_provenance=first['source_provenance'], summary=summary)


def build():
    source_paths = {
        'summary': 'receipts/period_bridge/summary.json',
        'results': 'receipts/period_bridge/results.json',
        'deep_summary': 'receipts/period_bridge_deep/summary.json',
        'deep_results': 'receipts/period_bridge_deep/results.json',
        'adjoint_lift': 'receipts/period_bridge_deep/e8_lift.json',
        'dirichlet': 'receipts/period_bridge_deep/dirichlet.json',
        'observability': 'receipts/period_bridge_deep/observability.json',
        'coxeter': 'receipts/period_bridge_deep/coxeter.json',
    }
    data = payload()
    payload_json = json.dumps(data, sort_keys=True, separators=(',', ':'))
    return dict(schema='pp-integral-browser/1', payload_json=payload_json,
                payload_sha256=hashlib.sha256(payload_json.encode()).hexdigest(),
                source_sha256={key: file_digest(path) for key, path in source_paths.items()},
                code_sha256=read('receipts/period_bridge_deep/summary.json')['source_sha256'])


def main():
    result = build()
    DESTINATION.parent.mkdir(parents=True, exist_ok=True)
    DESTINATION.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(dict(schema=result['schema'], payload_sha256=result['payload_sha256'],
                          generating_families=len(json.loads(result['payload_json'])['generating']['families'])), sort_keys=True))


if __name__ == '__main__':
    main()
