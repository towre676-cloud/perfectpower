import copy
import itertools
import json
import random
import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path

from perfectpower.generating_functions import RationalSeries, semilinear_series
from perfectpower.budget_populations import BudgetPopulation
from perfectpower.cost_resolvents import (cost_resolvent, verify_cost_resolvent, cost_quotient,
    verify_cost_quotient, finite_machine_series, dynacomp_series, dynacomp_switched_series)
from perfectpower.holonomic_series import ThetaSeries, weyl_theta_bridge, differential_theta_bridge
from perfectpower.exact_operators import Weyl
from perfectpower.binomial_periods import BinomialSum
from perfectpower.recurrence import Recurrence, from_generating_function
from perfectpower.witness_resolvent import witness_resolvent
from perfectpower.wz_certificates import discover_wz, check_wz_identity
from perfectpower.generating_cli import execute
from perfectpower.divisor_square import WorkLimit
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch


def series(out):
    return RationalSeries({k: out[k] for k in ('numerator', 'denominator')})


class RationalSeriesTests(unittest.TestCase):
    def test_random_rational_coefficients_against_long_division(self):
        rng = random.Random(1181)
        for _ in range(60):
            p = [rng.randint(-3, 3) for _ in range(rng.randint(1, 9))]
            q = [rng.choice([1, 2, -2])]+[rng.randint(-2, 2) for _ in range(rng.randint(0, 5))]
            a = RationalSeries({'numerator': p, 'denominator': q})
            expected = []
            for n in range(35):
                v = Q(p[n] if n < len(p) else 0)
                v -= sum(q[j]*expected[n-j] for j in range(1, min(n+1, len(q))))
                expected.append(v/q[0])
            self.assertEqual(a.terms(size=35), expected)

    def test_modular_composite_and_rational_units(self):
        a = RationalSeries({'numerator': [1, 2], 'denominator': [1, -1, -1]})
        for m in (4, 7, 12, 1000):
            self.assertEqual(a.terms(size=45, modulus=m), [int(x) % m for x in a.terms(size=45)])
        b = RationalSeries({'numerator': ['1/3'], 'denominator': [1, '-1/3']})
        self.assertEqual(b.coefficient(1000000, 10), pow(3, -1000001, 10))
        with self.assertRaises(ValueError):
            b.coefficient(0, 9)

    def test_large_index_and_growth_budget(self):
        a = RationalSeries({'numerator': [1], 'denominator': [1, -2, 1]})
        self.assertEqual(a.coefficient(10**18), 10**18+1)
        b = RationalSeries({'numerator': [1], 'denominator': [1, -2]})
        with self.assertRaises(WorkLimit):
            b.coefficient(10000)
        self.assertEqual(b.coefficient(10**18, 1009), pow(2, 10**18, 1009))

    def test_validation_after_cached_access(self):
        a = RationalSeries({'numerator': [1], 'denominator': [1, -1]})
        a.coefficient(1)
        for v in (True, 1.0, -1, 2**64):
            with self.assertRaises(ValueError):
                a.coefficient(v)
        with self.assertRaises(ValueError):
            RationalSeries({'numerator': [1.0], 'denominator': [1]})
        with self.assertRaises(ValueError):
            RationalSeries({'numerator': [1], 'denominator': [0, 1]})

    def test_nilpotent_and_polynomial_transients(self):
        out = witness_resolvent([[0, 1], [0, 0]], [0, 1], [[1, 0]])['outputs'][0]
        a = series(out)
        self.assertEqual(a.terms(size=6), [0, 1, 0, 0, 0, 0])
        self.assertEqual(a.subsequence(offset=1, step=0).terms(size=6), [1]*6)
        b = RationalSeries({'numerator': [1, 0, 2, 0, 1], 'denominator': [1, -1]})
        self.assertEqual(b.subsequence(1, 2).terms(size=8), [b.coefficient(1+2*n) for n in range(8)])

    def test_moments_convolution_and_prefix(self):
        a = RationalSeries({'numerator': [1], 'denominator': [1, -1]})
        b = a*a
        self.assertEqual(b.theta().terms(size=20), [n*(n+1) for n in range(20)])
        self.assertEqual(b.prefix_sums().terms(size=20), [(n+1)*(n+2)//2 for n in range(20)])
        self.assertEqual((a+a).terms(size=8), [2]*8)

    def test_existing_recurrence_and_pell_bridge(self):
        x = Recurrence((-1, 6), (1, 3)); y = Recurrence((-1, 6), (0, 2))
        a, b = RationalSeries.from_recurrence(x), RationalSeries.from_recurrence(y)
        self.assertEqual(a.denominator, (1, -6, 1))
        for n in range(18):
            self.assertEqual(a.coefficient(n)**2-2*b.coefficient(n)**2, 1)

    def test_semilinear_cells_preserve_indicator_multiplicity(self):
        predicate = {'op': 'and', 'args': [
            {'poly': [-2, 1], 'relation': '>='},
            {'op': 'or', 'args': [{'poly': [0, 1], 'relation': '=', 'modulus': 3, 'value': 1},
                                  {'poly': [0, 1], 'relation': '=', 'modulus': 3, 'value': 2}]}]}
        receipt = semilinear_series(predicate)
        self.assertEqual(series(receipt['series']).terms(size=80), [int(n >= 2 and n % 3 in (1, 2)) for n in range(80)])


class BudgetTests(unittest.TestCase):
    def test_random_restricted_populations_exhaustively(self):
        rng = random.Random(1182)
        for _ in range(35):
            coords = [{'weight': rng.randint(1, 4), 'lower': rng.randint(0, 2),
                       'upper': rng.randint(2, 6), 'modulus': rng.randint(1, 3)} for i in range(3)]
            for c in coords:
                c['residue'] = rng.randrange(c['modulus'])
            p = BudgetPopulation({'coordinates': coords})
            points = sorted(t for t in itertools.product(range(7), repeat=3)
                            if all(c['lower'] <= v <= c['upper'] and v % c['modulus'] == c['residue'] for c, v in zip(coords, t)))
            for budget in range(25):
                hits = [t for t in points if sum(c['weight']*v for c, v in zip(coords, t)) == budget]
                self.assertEqual(p.count(budget), len(hits))
                self.assertEqual(p.page(budget, size=100), [list(t) for t in hits])
                for k, t in enumerate(hits):
                    self.assertEqual(p.rank(budget, t), k)
                self.assertEqual(p.cumulative_count(budget), sum(sum(c['weight']*v for c, v in zip(coords, t)) <= budget for t in points))

    def test_trillion_coordinate_range_without_enumeration(self):
        p = BudgetPopulation({'coordinates': [{'weight': 1}, {'weight': 1}]})
        b, k = 10**12, 10**11+7
        self.assertEqual(p.count(b), b+1)
        self.assertEqual(p.select(b, k), [k, b-k])
        self.assertEqual(p.rank(b, [k, b-k]), k)
        self.assertEqual(p.count(b, modulus=12), (b+1) % 12)

    def test_huge_onset_is_a_lazy_shift(self):
        p = BudgetPopulation({'coordinates': [{'weight': 1, 'lower': 10**12}, {'weight': 2}]})
        self.assertEqual(p.count(10**12+10), 6)
        self.assertEqual(p.select(10**12+10, 2), [10**12+4, 3])

    def test_empty_and_invalid_rank_domains(self):
        p = BudgetPopulation({'coordinates': [{'weight': 1, 'lower': 3, 'upper': 1}]})
        self.assertEqual(p.count(20), 0)
        self.assertEqual(p.page(20), [])
        with self.assertRaises(ValueError):
            p.select(20, 0)
        p = BudgetPopulation({'coordinates': [{'weight': 2, 'modulus': 2, 'residue': 1}]})
        with self.assertRaises(ValueError):
            p.rank(4, [2])
        with self.assertRaises(ValueError):
            p.rank(3, [1])
        with self.assertRaises(WorkLimit):
            BudgetPopulation({'coordinates': [{'weight': 1, 'upper': 1000}]})


class CostTests(unittest.TestCase):
    def test_random_cost_words_against_dynamic_program(self):
        rng = random.Random(1183)
        for _ in range(15):
            ops = [{'cost': c, 'matrix': [[rng.randint(-1, 2) for j in range(2)] for i in range(2)]} for c in (1, 2, 3)]
            source = {'operators': ops, 'seed': [1, 2], 'readouts': [[1, -1]]}
            packet = cost_resolvent(source)
            values = [[1, 2]]
            for n in range(1, 18):
                values.append([sum(op['matrix'][i][j]*values[n-op['cost']][j]
                                   for op in ops if n >= op['cost'] for j in range(2)) for i in range(2)])
            self.assertEqual(series(packet['outputs'][0]).terms(size=18), [v[0]-v[1] for v in values])
            self.assertTrue(verify_cost_resolvent(packet, source))

    def test_quotient_is_equal_for_every_cost(self):
        source = {'operators': [{'cost': 1, 'matrix': [[1, 1], [2, 2]]}, {'cost': 2, 'matrix': [[0, 1], [1, 0]]}],
                  'seed': [1, 0], 'readouts': [[1, 1]]}
        packet = cost_quotient(source, [[1, 1]], [{'cost': 1, 'matrix': [[3]]}, {'cost': 2, 'matrix': [[1]]}], [[1]])
        self.assertTrue(verify_cost_quotient(packet))
        a = series(cost_resolvent(source)['outputs'][0]); b = series(packet['resolvent']['outputs'][0])
        self.assertEqual(a.summary(), b.summary())
        self.assertEqual(b.denominator, (1, -3, -1))

    def test_mutations_and_source_binding(self):
        source = {'operators': [{'cost': 1, 'matrix': [[1]]}], 'seed': [1], 'readouts': [[1]]}
        p = cost_resolvent(source)
        for field in ('vector', 'outputs', 'source_sha256'):
            q = copy.deepcopy(p)
            if field == 'vector': q[field][0]['numerator'] = ['2']
            elif field == 'outputs': q[field][0]['numerator'] = ['2']
            else: q[field] = '0'*64
            self.assertFalse(verify_cost_resolvent(q, source))
        q = copy.deepcopy(source); q['seed'] = [2]
        self.assertFalse(verify_cost_resolvent(p, q))
        with self.assertRaises(ValueError):
            cost_resolvent(dict(source, operators=[{'cost': 0, 'matrix': [[1]]}]))

    def test_finite_named_action_multiplicities(self):
        m = {'observations': [0, 0], 'actions': {'a': [0, 1], 'b': [0, 1]}}
        p = finite_machine_series(m, 0, [0, 1], {'a': 1, 'b': 2})
        self.assertEqual(p['transport']['reduced_dimension'], 1)
        self.assertEqual(series(p['transport']['resolvent']['outputs'][0]).terms(size=9), [1, 1, 2, 3, 5, 8, 13, 21, 34])
        with self.assertRaises(ValueError):
            finite_machine_series(m, 0, [0])

    def test_disabled_actions_and_zero_seed(self):
        m = {'observations': [0, 1], 'actions': {'go': [1, None], 'stay': [0, 1]}}
        p = finite_machine_series(m, 0, [1], {'go': 2, 'stay': 1}, quotient=False)
        self.assertEqual(series(p['outputs'][0]).terms(size=8), [0, 0, 1, 2, 3, 4, 5, 6])
        p = cost_resolvent({'operators': [{'cost': 1, 'matrix': [[0]]}], 'seed': [0], 'readouts': [[1]]})
        self.assertEqual(series(p['outputs'][0]).terms(size=6), [0]*6)

    def test_dynacomp_packet_and_input_timing(self):
        p = {'schema': 'dynacomp.linear/1', 'A': [[1, 0], [0, 1]], 'B': [[1], [2]],
             'C': [[1, 1]], 'E': [[1, 1]], 'G': [[1]], 'H': [[3]], 'D': [[1]]}
        result = dynacomp_series(p, initial=[4, 5])
        self.assertEqual(series(result['responses']['input_0']['resolvent']['outputs'][0]).terms(size=6), [3]*6)
        self.assertEqual(series(result['responses']['initial']['resolvent']['outputs'][0]).terms(size=6), [9]*6)
        p['H'] = [[4]]
        with self.assertRaises(ValueError):
            dynacomp_series(p)

    def test_dynacomp_switched_noncommuting_modes(self):
        # Original mode matrices do not commute, yet the target closes.
        a, b = [[1, 1], [2, 2]], [[0, 1], [1, 0]]
        packet = {'schema': 'dynacomp.switched/1', 'modes': {'a': a, 'b': b},
                  'E': [[1, 1]], 'G': {'a': [[3]], 'b': [[1]]}, 'C': [[1, 1]], 'D': [[1]]}
        result = dynacomp_switched_series(packet, [1, 0], {'a': 1, 'b': 2})
        self.assertTrue(verify_cost_quotient(result))
        self.assertEqual(series(result['resolvent']['outputs'][0]).denominator, (1, -3, -1))


class HolonomicTests(unittest.TestCase):
    def test_all_existing_binomial_telescopers(self):
        for name in ('vandermonde', 'apery2', 'apery3'):
            b = BinomialSum({'family': name}); p = b.telescoper()
            s = ThetaSeries({'theta': p['theta_operator'], 'initial': p['initial_values']})
            self.assertEqual(s.terms(size=32), b.terms(size=32))

    def test_inhomogeneous_equation(self):
        s = ThetaSeries({'theta': [[1], [-1]], 'forcing': [1], 'initial': []})
        self.assertEqual(s.terms(size=20), [1]*20)

    def test_singular_seeds_and_equation_consistency(self):
        s = ThetaSeries({'theta': [[0, 1]], 'initial': [7]})
        self.assertEqual(s.terms(size=5), [7, 0, 0, 0, 0])
        with self.assertRaises(ValueError):
            ThetaSeries({'theta': [[0, 1]], 'initial': []})
        with self.assertRaises(ValueError):
            ThetaSeries({'theta': [[0, 1]], 'initial': [7, 1]})
        with self.assertRaises(ValueError):
            ThetaSeries({'theta': [[0, 1]], 'forcing': [1], 'initial': [0]})
        with self.assertRaises(ValueError):
            ThetaSeries({'theta': [[0]], 'initial': [1]})

    def test_weyl_normal_ordering_against_independent_action(self):
        op = Weyl({(0, 2): 2, (3, 1): -3, (1, 0): 5})
        bridge = weyl_theta_bridge(op); h = bridge['left_power']
        a = [Q(n*n+1) for n in range(30)]
        old = op.act_series(a, 22)
        rows = [[Q(v) for v in row] for row in bridge['theta']]
        for n in range(22):
            theta = sum(sum(c*Q(n-j)**k for k, c in enumerate(row))*a[n-j]
                        for j, row in enumerate(rows) if n >= j)
            self.assertEqual(theta, old[n-h] if n >= h else 0)

    def test_clear_rational_differential_coefficients(self):
        # (1-z) D f - f=0 has f=1/(1-z), with f(0)=1.
        bridge = differential_theta_bridge([-1, [1, -1]])
        a = ThetaSeries({'theta': bridge['theta'], 'initial': [1]})
        self.assertEqual(a.terms(size=40), [1]*40)

    def test_actual_period_module_operator(self):
        from perfectpower.differential_modules import DifferentialModule
        b = BinomialSum({'family': 'apery2'})
        packet = b.telescoper()
        observable = DifferentialModule({'matrix': packet['module']['connection']}).observable()
        bridge = differential_theta_bridge(observable['monic_operator'])
        series = ThetaSeries({'theta': bridge['theta'], 'initial': b.terms(size=4)})
        self.assertEqual(series.terms(size=32), b.terms(size=32))

    def test_wz_discovery_and_mutation(self):
        rn = {'numerator': [[1, 1]], 'denominator': [[2, 2], [-2]]}
        rk = {'numerator': [[0, 1], [-1]], 'denominator': [1, 1]}
        result = discover_wz(rn, rk, [[1, 1], [-1]], degree=1)
        self.assertTrue(result['valid'])
        self.assertFalse(result['boundary_conditions_proved'])
        bad = copy.deepcopy(result['certificate']); bad['numerator'][1]['numerator'] = ['1']
        self.assertFalse(check_wz_identity(rn, rk, bad)['valid'])
        self.assertEqual(discover_wz(rn, rk, [[1]], degree=0)['status'], 'ANSATZ_UNRESOLVED')


class IntegrationTests(unittest.TestCase):
    def test_catalogue_persistence_and_service_queries(self):
        with tempfile.TemporaryDirectory() as t:
            path = str(Path(t)/'catalog.sqlite')
            spec = {'coordinates': [{'weight': 1}, {'weight': 2}]}
            with Catalogue(path) as c:
                c.register('budget_population', spec, 'budgets')
                self.assertEqual(dispatch(c, {'op': 'call', 'object': 'budgets', 'method': 'count', 'args': {'budget': 12}}), 7)
            with Catalogue(path) as c:
                self.assertEqual(dispatch(c, {'op': 'call', 'object': 'budgets', 'method': 'select', 'args': {'budget': 12, 'rank': 2}}), [4, 4])
                c.register('rational_series', {'numerator': [1], 'denominator': [1, -1]}, 'ones')
                c.register('theta_series', {'theta': [[0, 1], [0, -1]], 'initial': [1]}, 'constant')
                self.assertEqual(dispatch(c, {'op': 'call', 'object': 'ones', 'method': 'coefficient', 'args': {'index': 10**12}}), 1)

    def test_cli_roundtrip(self):
        request = {'kind': 'budget', 'specification': {'coordinates': [{'weight': 1}, {'weight': 2}]},
                   'query': {'budget': 12, 'rank': 2, 'point': [4, 4]}}
        with tempfile.TemporaryDirectory() as t:
            f = Path(t)/'input.json'; f.write_text(json.dumps(request))
            result = subprocess.run([sys.executable, '-m', 'perfectpower', 'generating-function', str(f)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            decoded = json.loads(result.stdout)
            self.assertEqual(decoded['selected'], [4, 4])
            self.assertEqual(decoded['rank'], 2)

    def test_unknown_request_fields(self):
        with self.assertRaises(ValueError):
            execute({'kind': 'budget', 'specification': {}, 'typo': 1})


if __name__ == '__main__':
    unittest.main()
