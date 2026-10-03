"""The four answers of the constraint compiler (`Plan.answer`, `Plan.certificate`)."""
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.compiler import (CONDITIONAL_COMPLETE, NotEnumerable, PowerConstraint,  # noqa: E402
                                   compile_constraint)


def plan(F, d=2):
    return compile_constraint(PowerConstraint(F, d))


class RegistryTransport(unittest.TestCase):
    """Exercise every registered list, including points beyond a short scan.

    Expected answers come from the committed curve lists, pulled back directly
    through x = a*n+b; they do not use the compiler's reduction helpers.
    """

    def test_all_registered_curves_under_affine_transport(self):
        registry = json.loads((ROOT / 'receipts' / 'mordell_registry.json').read_text())
        rows = [(r['k'], r, 'complete_list') for r in registry['positive_curves']]
        rows += [(-r['D'], r, 'complete_list') for r in registry['curves']]
        rows += [(-r['D'], r, 'conditional') for r in registry['conditional_curves']]
        for k, row, answer in rows:
            for a, b in ((1, 0), (2, 1), (3, -7), (-2, 9)):
                with self.subTest(k=k, a=a, b=b):
                    # (a*n+b)^3+k, in ascending coefficient order.
                    p = plan((b**3 + k, 3*a*b*b, 3*a*a*b, a**3))
                    expected = {}
                    for x, y in row['points']:
                        if (x - b) % a == 0:
                            n = (x - b) // a
                            if n >= 1:
                                expected.setdefault(n, []).append(y)
                    hits = [(n, sorted(ys)) for n, ys in sorted(expected.items())]
                    self.assertEqual(p.answer, answer)
                    self.assertEqual(p.all_hits(), hits)
                    self.assertEqual(p.certificate['premises'], row.get('premises', []))
                    self.assertFalse(p.certificate['execution_verified'])
                    for n, ys in hits:
                        self.assertEqual(p.contains(n), ys)


class Answers(unittest.TestCase):
    def test_complete_list_positive_k(self):
        for k in (2, 4, 33, 49, 81):
            p = plan((k, 0, 0, 1))
            self.assertEqual(p.answer, 'complete_list', k)
            self.assertIn(f'PerfectPower.Generated.ClassLists.K{k}.plus{k}', p.certificate['lean_theorems'])
            self.assertEqual(p.certificate['premises'], [])
        # (2n + 1)^3 + 2: the affine transport keeps the theorem
        self.assertEqual(plan((3, 6, 12, 8)).all_hits(), [])

    def test_conditional_names_its_premises(self):
        p = plan((-15, 0, 0, 1))
        self.assertEqual((p.answer, p.status), ('conditional', CONDITIONAL_COMPLETE))
        self.assertTrue(p.certificate['premises'])
        self.assertTrue(all('matveev' in x for x in p.certificate['premises']))
        self.assertEqual(p.all_hits(), [(4, [-7, 7])])

    def test_generator_and_unresolved(self):
        self.assertEqual(plan((1, 0, 2)).answer, 'generator')          # 2n^2 + 1 = m^2: Pell
        self.assertEqual(plan((1, 0, 0, 1)).answer, 'complete_list')    # n^3 + 1: K1.plus1
        p = plan((19, 0, 0, 1))                                         # n^3 + 19: census only
        self.assertEqual(p.answer, 'unresolved')
        with self.assertRaises(NotEnumerable):
            list(p.iter_hits(100))

    def test_certificate_boundary(self):
        c = plan((2, 0, 0, 1)).certificate
        self.assertFalse(c['execution_verified'])
        self.assertTrue(c['python_steps'])


if __name__ == '__main__':
    unittest.main()
