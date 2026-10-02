"""The four answers of the constraint compiler (`Plan.answer`, `Plan.certificate`)."""
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.compiler import (CONDITIONAL_COMPLETE, NotEnumerable, PowerConstraint,  # noqa: E402
                                   compile_constraint)


def plan(F, d=2):
    return compile_constraint(PowerConstraint(F, d))


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
        p = plan((1, 0, 0, 1))                                          # n^3 + 1: census only
        self.assertEqual(p.answer, 'unresolved')
        with self.assertRaises(NotEnumerable):
            list(p.iter_hits(100))

    def test_certificate_boundary(self):
        c = plan((2, 0, 0, 1)).certificate
        self.assertFalse(c['execution_verified'])
        self.assertTrue(c['python_steps'])


if __name__ == '__main__':
    unittest.main()
