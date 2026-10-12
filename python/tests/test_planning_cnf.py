import itertools
import random
import unittest
from perfectpower.planning_cnf import encode_allocation
from perfectpower.model_counting import CNFCounter
from perfectpower.planning import CompletionPlanner

class CircuitTests(unittest.TestCase):
    def test_unique_functional_extension_and_independent_counts(self):
        for seed in range(12):
            rng = random.Random(seed)
            n = 1+seed%6
            spec = {'kind': 'allocation', 'resources': [{'name': 'a', 'min': 1, 'max': 9}, {'name': 'b', 'max': 8}],
                    'variables': [{'name': str(j), 'costs': [rng.randrange(8), rng.randrange(8)], 'upper': 1} for j in range(n)]}
            formula, circuit = encode_allocation(spec)
            ref = CompletionPlanner(dict(spec, strategy='enumeration'))
            with CNFCounter(formula, timeout=10) as counter:
                self.assertEqual(counter.count(), ref.count())
                for point in itertools.product((0, 1), repeat=n):
                    extension = circuit.extend(point)
                    feasible = ref.completions(point)['count']
                    self.assertEqual(formula.accepts(extension), bool(feasible))
                    # Unique extension is checked by an independent #SAT engine.
                    assumptions = [j+1 if x else -j-1 for j, x in enumerate(point)]
                    self.assertEqual(counter.count(assumptions), feasible)

if __name__ == '__main__':
    unittest.main()
