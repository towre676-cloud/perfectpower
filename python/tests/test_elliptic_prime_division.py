import copy
import unittest
from unittest.mock import patch
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.divisor_square import WorkLimit
from perfectpower import elliptic_prime_division as d
from perfectpower.elliptic_prime_division_verifier import (verify_prime_division, verify_general_division,
                                                          silverman_division)
from perfectpower.elliptic_division import tripling_polynomials
from perfectpower import polyalg as P

E11 = EllipticCurve([0, -1, 1, 0, 0])   # 11a3, torsion Z/5
E37 = EllipticCurve([0, 0, 1, -1, 0])   # 37a1, rank 1, P=(0,0)


class PrimeDivision(unittest.TestCase):
    def test_recurrence_reproduces_tripling_and_silverman(self):
        psi, phi = d.odd_division_polynomials(E11, 3)
        self.assertEqual((psi, phi), tripling_polynomials(E11))
        for E in (E11, E37, EllipticCurve([1, 0, 1, 4, -6])):
            for n in (5, 7):
                psi, _ = d.odd_division_polynomials(E, n)
                sp, sphi = silverman_division(E, n)
                self.assertEqual(psi, sp)
                self.assertEqual(len(psi) - 1, (n*n - 1)//2)
                prod = d.division_equation(E, n, (3, 0))
                self.assertEqual(prod, P.add(sphi, P.scale(P.power(sp, 2), -3)))

    def test_five_torsion_kernel_and_empty_fifths(self):
        c = d.rational_prime_division(E11, None, 5)
        self.assertEqual(len(c['points']), 5)
        self.assertTrue(verify_prime_division(c))
        e = d.rational_prime_division(E11, c['points'][1], 5)
        self.assertEqual(e['points'], [])
        self.assertTrue(verify_prime_division(e))

    def test_recover_generator_by_five_and_seven(self):
        Pt = E37.checked([0, 0])
        for n in (5, 7):
            c = d.rational_prime_division(E37, E37.mul(Pt, n), n)
            self.assertEqual(c['points'], [['0', '0']])
            self.assertTrue(verify_prime_division(c))
        with patch('perfectpower.elliptic_prime_division.discovered_roots', return_value=iter(())):
            c = d.rational_prime_division(E37, E37.mul(Pt, 5), 5)
        self.assertIsNotNone(c['division_certificate'])
        self.assertTrue(verify_prime_division(c))

    def test_composed_division_and_mutations(self):
        Pt = E37.checked([0, 0])
        g = d.rational_division_general(E37, E37.mul(Pt, 70), 70)
        self.assertEqual(g['points'], [['0', '0']])
        self.assertEqual([s['prime'] for s in g['stages']], [2, 5, 7])
        self.assertTrue(verify_general_division(g))
        for mut in ('fibre', 'factors', 'bits'):
            c = copy.deepcopy(g)
            if mut == 'fibre':
                c['stages'][1]['fibres'][0]['points'] = []
            elif mut == 'factors':
                c['factors'] = [5, 2, 7]
            else:
                c['bit_limit'] += 1
            self.assertFalse(verify_general_division(c))
        c = d.rational_prime_division(E37, E37.mul(Pt, 7), 7)
        for field, value in (('anchor', None), ('method', 'empty_division_fibre'), ('root_nodes', 0), ('prime', 5)):
            cc = copy.deepcopy(c); cc[field] = value
            self.assertFalse(verify_prime_division(cc))

    def test_budgets_and_rejections(self):
        for n in (3, 17, True):
            with self.assertRaises(ValueError):
                d.rational_prime_division(E37, None, n)
        with self.assertRaises(ValueError):
            d.rational_division_general(E37, None, 17)
        with patch('perfectpower.elliptic_prime_division.discovered_roots', return_value=iter(())):
            with self.assertRaises(WorkLimit):
                d.rational_prime_division(E37, E37.mul(E37.checked([0, 0]), 5), 5, node_limit=10)
        with self.assertRaises(WorkLimit):
            d.rational_prime_division(EllipticCurve([0, 0, 0, -123456789, 987654321]), None, 7, bit_limit=128)
        with self.assertRaises(WorkLimit):
            d.rational_division_general(E11, None, 25, branch_limit=4)


if __name__ == '__main__':
    unittest.main()
