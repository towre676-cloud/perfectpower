import copy
from fractions import Fraction
import json
from math import factorial, prod
import os
import unittest

from perfectpower.checked_landau import landau_certificate, check_landau
from perfectpower.divisor_square import WorkLimit


class CheckedLandauTests(unittest.TestCase):
    def test_original_factorial_divisibility(self):
        for a, b in [([2], [1,1]), ([3], [1,2]), ([6], [1,2,3]),
                     ([2,2], [1,1,1,1]), ([], []), ([4,1], [2,2,1])]:
            packet = landau_certificate(a, b)
            for n in range(30):
                numerator = prod(factorial(c*n) for c in a)
                denominator = prod(factorial(c*n) for c in b)
                self.assertEqual(numerator % denominator, 0)
            self.assertEqual(packet, json.loads(json.dumps(packet)))
            self.assertFalse(packet['execution_verified'])

    def test_cell_endpoints_and_interior(self):
        packet = landau_certificate([6], [1,2,3])
        rows = packet['arithmetic']['intervals']
        self.assertEqual(rows[0]['left'], '0')
        self.assertEqual(rows[-1]['right'], '1')
        for i, row in enumerate(rows):
            left, right = Fraction(row['left']), Fraction(row['right'])
            if i:
                self.assertEqual(left, Fraction(rows[i-1]['right']))
            for x in (left, (left+right)/2, (left+99*right)/100):
                floor = lambda c: (c*x).numerator//(c*x).denominator
                self.assertEqual(floor(6)-sum(floor(c) for c in (1,2,3)), row['delta'])

    def test_unsupported_verdicts_and_budget(self):
        for a, b in [([1,1], [2]), ([3], [1])]:
            with self.assertRaises(ValueError):
                landau_certificate(a, b)
        with self.assertRaises(WorkLimit):
            landau_certificate([6], [1,2,3], work_limit=3)

    def test_all_packet_mutations_rejected(self):
        packet = landau_certificate([3], [1,2])
        for field, value in [('lean', 'axiom unsound : False'),
                             ('proof_status', 'kernel_checked'), ('execution_verified', True),
                             ('source_sha256', '0'*64)]:
            changed = copy.deepcopy(packet); changed[field] = value
            self.assertFalse(check_landau(changed, lean='/not/a/tool')['accepted'])
        changed = copy.deepcopy(packet); changed['arithmetic']['intervals'][0]['delta'] += 1
        self.assertFalse(check_landau(changed, lean='/not/a/tool')['accepted'])

    def test_service_emits_unaccepted_proposal(self):
        from perfectpower.query_service import dispatch
        result = dispatch(None, dict(op='checked_landau',args=dict(numerator=[2],denominator=[1,1])))
        self.assertEqual(result, landau_certificate([2],[1,1]))
        self.assertEqual(result['proof_status'], 'emitted')

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN') and os.environ.get('LEAN_PATH'),
                         'Lean and pinned Mathlib required')
    def test_universal_original_kernel_proofs(self):
        for a, b in [([], []), ([2], [1,1]), ([3], [1,2]), ([6], [1,2,3]),
                     ([4,1], [2,2,1])]:
            result = check_landau(landau_certificate(a, b), timeout=120)
            self.assertTrue(result['accepted'], result)
            self.assertFalse(result['execution_verified'])
            self.assertNotIn('sorryAx', result['log'])


if __name__ == '__main__':
    unittest.main()
