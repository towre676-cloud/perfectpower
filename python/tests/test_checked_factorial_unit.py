import copy
import json
from math import factorial
import os
import unittest

from perfectpower.checked_factorial_unit import unit_certificate, check_unit
from perfectpower.divisor_square import WorkLimit


class CheckedFactorialUnitTests(unittest.TestCase):
    def test_independent_stripped_factorials(self):
        for p in (2, 3, 5, 7, 11):
            for depth in (1, 2, 3):
                for n in (0, 1, p-1, p, p+1, 31, 64, 127):
                    packet = unit_certificate(n, p, depth)
                    value = factorial(n)
                    while value % p == 0:
                        value //= p
                    self.assertEqual(packet['arithmetic']['unit'], value % p**depth)
                    self.assertFalse(packet['execution_verified'])
                    self.assertEqual(packet['proof_status'], 'emitted')

    def test_zero_index_and_large_index(self):
        self.assertEqual(unit_certificate(0, 2, 1)['arithmetic']['unit'], 1)
        packet = unit_certificate(10**100, 2, 3)
        self.assertGreater(len(packet['arithmetic']['levels']), 300)
        self.assertIn('original_factorial_unit', packet['lean'])

    def test_mutations_rejected_before_execution(self):
        packet = unit_certificate(37, 3, 2)
        for field, value in [('lean', 'axiom falsehood : False'),
                             ('source_sha256', '0'*64), ('proof_status', 'kernel_checked'),
                             ('execution_verified', True), ('namespace', 'Other')]:
            changed = copy.deepcopy(packet); changed[field] = value
            self.assertFalse(check_unit(changed, lean='/does/not/exist')['accepted'])
        changed = copy.deepcopy(packet); changed['arithmetic']['unit'] += 1
        self.assertFalse(check_unit(changed, lean='/does/not/exist')['accepted'])

    def test_domains_and_total_work_budget(self):
        for args in [(True, 2, 1), (-1, 2, 1), (1, 9, 1), (1, 2, 0)]:
            with self.assertRaises(ValueError):
                unit_certificate(*args)
        with self.assertRaises(WorkLimit):
            unit_certificate(10**100, 2, 5, work_limit=8192)
        with self.assertRaises(ValueError):
            unit_certificate(1, 2, 1, work_limit=True)

    def test_json_roundtrip(self):
        packet = unit_certificate(123, 5, 2)
        self.assertEqual(packet, json.loads(json.dumps(packet)))

    def test_service_emits_unaccepted_proposal(self):
        from perfectpower.query_service import dispatch
        result = dispatch(None, dict(op='checked_factorial_unit',args=dict(n=37,p=2,depth=3)))
        self.assertEqual(result, unit_certificate(37,2,3))
        self.assertEqual(result['proof_status'], 'emitted')

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN') and os.environ.get('LEAN_PATH'),
                         'Lean and pinned Mathlib required')
    def test_original_factorial_kernel_queries(self):
        for n, p, depth in [(0, 2, 1), (37, 2, 3), (123, 3, 2), (256, 5, 2),
                            (10**30, 2, 2)]:
            packet = unit_certificate(n, p, depth)
            result = check_unit(packet, timeout=120)
            self.assertTrue(result['accepted'], result)
            self.assertFalse(result['execution_verified'])
            self.assertNotIn('sorryAx', result['log'])


if __name__ == '__main__':
    unittest.main()
