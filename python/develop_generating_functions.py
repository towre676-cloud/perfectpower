"""Reproduce Wilf-inspired examples and exact, source-bound receipts."""
from pathlib import Path
from hashlib import sha256
import json
from perfectpower.catalogue import encoded
from perfectpower.generating_cli import execute
from perfectpower.generating_functions import RationalSeries
from perfectpower.recurrence import Recurrence
from perfectpower.binomial_periods import BinomialSum
from perfectpower.holonomic_series import ThetaSeries, differential_theta_bridge

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'receipts/generating_functions'


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    examples = ROOT/'examples/generating_functions'
    requests = {
        'budget': {'kind': 'budget', 'specification': {'coordinates': [{'weight': 1}, {'weight': 2}, {'weight': 3}]},
                   'query': {'budget': 20, 'rank': 7, 'point': [2, 0, 6], 'size': 12}},
        'large_budget': {'kind': 'budget', 'specification': {'coordinates': [{'weight': 1}, {'weight': 1}]},
                        'query': {'budget': 10**12, 'rank': 10**11+7}},
        'restricted_budget': {'kind': 'budget', 'specification': {'coordinates': [
            {'weight': 1, 'modulus': 2, 'residue': 1}, {'weight': 2, 'lower': 2, 'upper': 12}, {'weight': 3}]},
            'query': {'budget': 25, 'size': 12}},
        'finite_machine': {'kind': 'finite_machine', 'specification': {
            'model': {'observations': [0, 0], 'actions': {'a': [0, 1], 'b': [0, 1]}},
            'initial': 0, 'accepting': [0, 1], 'costs': {'a': 1, 'b': 2}}, 'query': {'size': 24}},
        'modular_large': {'kind': 'rational', 'specification': {'numerator': [1], 'denominator': [1, -2]},
                          'query': {'start': 10**18, 'size': 1, 'modulus': 1009}},
        'wz_binomial': {'kind': 'wz', 'specification': {
            'n_ratio': {'numerator': [[1, 1]], 'denominator': [[2, 2], [-2]]},
            'k_ratio': {'numerator': [[0, 1], [-1]], 'denominator': [1, 1]},
            'denominator': [[1, 1], [-1]], 'degree': 1}},
    }
    for name in ('vandermonde', 'apery2', 'apery3'):
        b = BinomialSum({'family': name}); packet = b.telescoper()
        requests[name] = {'kind': 'theta', 'specification': {'theta': packet['theta_operator'], 'initial': packet['initial_values']}, 'query': {'size': 32}}
        assert ThetaSeries(requests[name]['specification']).terms(size=32) == b.terms(size=32)
    from perfectpower.differential_modules import DifferentialModule
    b = BinomialSum({'family': 'apery2'}); packet = b.telescoper()
    op = DifferentialModule({'matrix': packet['module']['connection']}).observable()
    bridge = differential_theta_bridge(op['monic_operator'])
    assert ThetaSeries({'theta': bridge['theta'], 'initial': b.terms(size=4)}).terms(size=32) == b.terms(size=32)
    (OUT/'period_operator.json').write_text(encoded({'differential_operator': op,
        'theta_bridge': bridge, 'initial': b.terms(size=4), 'terms_cross_checked': 32,
        'scope': 'same normalized formal solution of the supplied rank-two period operator; analytic integral identification is separate'})+'\n')
    for name, request in requests.items():
        (examples/(name+'.json')).write_text(encoded(request)+'\n')
    results = {}
    for path in sorted(examples.glob('*.json')):
        raw = path.read_bytes(); request = json.loads(raw)
        result = execute(request)
        result['source'] = {'path': str(path.relative_to(ROOT)), 'sha256': sha256(raw).hexdigest()}
        (OUT/(path.stem+'.json')).write_text(encoded(result)+'\n')
        results[path.stem] = result
    assert results['budget']['count'] == 44 and results['budget']['selected'] == [2, 0, 6]
    assert results['large_budget']['selected'] == [100000000007, 899999999993]
    pell = {}
    for name, seed in [('x', (1, 3)), ('y', (0, 2))]:
        s = RationalSeries.from_recurrence(Recurrence((-1, 6), seed))
        pell[name] = {'series': s.evidence(), 'terms': s.terms(size=20)}
    assert all(x*x-2*y*y == 1 for x, y in zip(pell['x']['terms'], pell['y']['terms']))
    (OUT/'pell.json').write_text(encoded(pell)+'\n')
    summary = {'schema': 'pp-generating-function-corpus/1', 'requests': len(results),
               'budget_20_count': 44, 'trillion_budget_count': results['large_budget']['count'],
               'finite_machine_original_states': 2, 'finite_machine_reduced_states': 1,
               'dynacomp_source_commit': '70f609c', 'dynacomp_linear_dimensions': [6, 2],
               'dynacomp_switched_dimensions': [2, 1], 'binomial_terms_cross_checked_per_family': 32,
               'wz_boundary_conditions_proved': False, 'python_refinement_proved': False,
               'lean_foundation': 'PerfectPower/GeneratingFunctions.lean',
               'sources': {'wilf': 'https://www2.math.upenn.edu/~wilf/DownldGF.html',
                           'coefficient_algorithm': 'https://mathexp.eu/bostan/publications/BoMo21.pdf',
                           'wz': 'https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/rational.html'}}
    (OUT/'summary.json').write_text(encoded(summary)+'\n')
    print(encoded(summary))


if __name__ == '__main__':
    main()
