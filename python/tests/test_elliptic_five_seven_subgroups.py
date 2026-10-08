import copy
import json
import tempfile
import unittest
from itertools import product
from pathlib import Path
from unittest.mock import patch

from perfectpower.elliptic_arithmetic import EllipticCurve, encode_point
from perfectpower.elliptic_subgroups import row_basis
from perfectpower.elliptic_presentation import coefficient_presentation, verify_coefficient_presentation
from perfectpower.elliptic_subgroup_verifier import verify_subgroup_preimage
from perfectpower.elliptic_saturation_verifier import verify_saturation
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch
from perfectpower.divisor_square import WorkLimit
from perfectpower.elliptic_prime_division import rational_prime_division
from perfectpower.elliptic_prime_division_verifier import verify_prime_division


class FiveSevenSubgroups(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.E = EllipticCurve([0, 0, 1, -1, 0])
        cls.P = cls.E.checked([0, 0])
        cls.preimages = {p: cls.E.subgroup_preimage([cls.E.mul(cls.P, p)], p) for p in (5, 7)}
        cls.saturation = cls.E.bounded_saturation([cls.E.mul(cls.P, 35)], primes=[5, 7])

    def test_recover_generator_and_source_inclusion(self):
        for p, c in self.preimages.items():
            self.assertEqual(c['replacement_points'], [['0', '0']])
            self.assertEqual(c['relation_basis'], [[1]])
            self.assertEqual(c['coefficient_presentation']['source_inclusion_rows'], [[p]])
            self.assertTrue(verify_subgroup_preimage(json.loads(json.dumps(c))))

    def test_hidden_relation_without_individual_divisibility(self):
        E = EllipticCurve([-4, 1]); P = E.checked([0, 1]); Q = E.checked([2, 1])
        for p in (5, 7):
            source = [E.add(P, Q), E.add(E.mul(P, p-1), E.neg(Q))]
            c = E.subgroup_preimage(source, p)
            for row in c['projective_fibres']:
                if row['coefficients'] in ([0, 1], [1, 0]):
                    self.assertEqual(row['fibre']['points'], [])
            self.assertEqual(c['relation_basis'], [[1, 1]])
            self.assertEqual(c['replacement_points'][0], encode_point(P))
            self.assertTrue(verify_subgroup_preimage(c))
            lattice = c['coefficient_presentation']
            self.assertEqual(lattice['hermite_numerator_rows'], [[1, 1], [0, p]])
            self.assertEqual(lattice['source_inclusion_rows'], [[p, -1], [0, 1]])
            self.assertEqual(lattice['inclusion_smith']['smith_factors'], [1, p])

    def test_rational_five_and_seven_torsion_is_retained(self):
        # Tate normal form: order 5 at b=c=1; order 7 at b=4,c=2.
        for p, model in ((5, [0, -1, -1, 0, 0]), (7, [-1, -4, -4, 0, 0])):
            E = EllipticCurve(model); T = E.checked([0, 0])
            self.assertIsNone(E.mul(T, p))
            c = E.subgroup_preimage([], p)
            self.assertEqual(len(c['kernel_fibre']['points']), p)
            self.assertEqual(len(c['generators']), p-1)
            self.assertTrue(verify_subgroup_preimage(c))
            c = E.subgroup_preimage([T], p)
            self.assertEqual(c['relation_basis'], [])
            self.assertTrue(verify_subgroup_preimage(c))

    def test_bounded_saturation_closes_both_primes(self):
        c = self.saturation
        self.assertEqual(c['status'], 'closed')
        self.assertEqual(c['closed_primes'], [5, 7])
        self.assertEqual(c['generators'], [['0', '0']])
        self.assertFalse(c['complete_mordell_weil_group'])
        self.assertTrue(verify_saturation(c))
        short = self.E.bounded_saturation([self.E.mul(self.P, 35)], primes=[5, 7], max_steps=1)
        self.assertEqual(short['status'], 'step-limit')
        self.assertEqual(short['closed_primes'], [])
        self.assertTrue(verify_saturation(short))

    def test_hermite_lattice_matches_every_residue(self):
        for p in (2, 3, 5, 7):
            for width in range(4):
                seeds = [[], [[int(j == 0) for j in range(width)]] if width else []]
                if width > 1:
                    seeds.append([[1] + [p-1]*(width-1)])
                    seeds.append([[int(i == j) for j in range(width)] for i in range(width)])
                for rows in seeds:
                    basis = row_basis(rows, p, width)
                    c = coefficient_presentation(p, basis, width)
                    self.assertTrue(verify_coefficient_presentation(c, p, basis, width))
                    span = {tuple(sum(a*b[j] for a, b in zip(cs, basis)) % p for j in range(width))
                            for cs in product(range(p), repeat=len(basis))}
                    h = c['hermite_numerator_rows']
                    hermite_span = {tuple(sum(a*b[j] for a, b in zip(cs, h)) % p for j in range(width))
                                    for cs in product(range(p), repeat=width)}
                    self.assertEqual(span, hermite_span)

    def test_mutations_budget_and_independent_replay(self):
        c = self.preimages[7]
        for change in (
            lambda d: d.__setitem__('prime', 5),
            lambda d: d['projective_fibres'].clear(),
            lambda d: d['coefficient_presentation'].__setitem__('coefficient_index', 1),
            lambda d: d['coefficient_presentation']['source_inclusion_rows'][0].__setitem__(0, True),
            lambda d: d['coefficient_presentation']['inclusion_smith']['diagonal_matrix'][0].__setitem__(0, 1),
            lambda d: d['coefficient_presentation'].__setitem__('group_index_claimed', True)):
            bad = copy.deepcopy(c); change(bad)
            self.assertFalse(verify_subgroup_preimage(bad))
        bad = copy.deepcopy(self.saturation); bad['closed_primes'] = [5]
        self.assertFalse(verify_saturation(bad))
        with patch('perfectpower.elliptic_subgroups.subgroup_preimage', side_effect=AssertionError('search')), \
             patch('perfectpower.elliptic_prime_division.discovered_roots', side_effect=AssertionError('search')), \
             patch('perfectpower.elliptic_presentation.smith_certificate', side_effect=AssertionError('reduction')):
            self.assertTrue(verify_subgroup_preimage(c))
            self.assertTrue(verify_saturation(self.saturation))
        with self.assertRaises(WorkLimit):
            self.E.subgroup_preimage([self.E.mul(self.P, 7)], 7, node_limit=1)
        self.assertFalse(verify_subgroup_preimage(c, node_limit=1))

    def test_good_reduction_obstruction_and_mutations(self):
        E = EllipticCurve([-4, 1]); target = E.add(E.checked([0, 1]), E.checked([2, 1]))
        for p in (5, 7):
            c = rational_prime_division(E, target, p, local_obstructions=True)
            self.assertEqual(c['method'], 'good_reduction_obstruction')
            self.assertEqual(c['points'], [])
            self.assertEqual(c['root_nodes'], 0)
            self.assertTrue(verify_prime_division(c))
            for key, value in (('prime', p), ('group_order', 1), ('completed_target', [0, 0]), ('prime', True)):
                bad = copy.deepcopy(c); bad['obstruction_certificate'][key] = value
                self.assertFalse(verify_prime_division(bad))

    def test_old_packets_and_cold_service(self):
        old = self.E.subgroup_preimage([self.P], 2)
        old.pop('coefficient_presentation'); old['schema'] = 'pp-elliptic-subgroup-preimage/1'
        self.assertTrue(verify_subgroup_preimage(old))
        with tempfile.TemporaryDirectory() as tmp:
            db = Path(tmp)/'objects.sqlite'
            with Catalogue(db) as cat:
                cat.register('elliptic_curve', self.E.specification, 'E')
            with Catalogue(db) as cat:
                c = dispatch(cat, dict(op='call', object='E', method='subgroup_preimage',
                                       args=dict(points=[encode_point(self.E.mul(self.P, 7))], prime=7)))
                self.assertTrue(dispatch(cat, dict(op='verify_elliptic_subgroup_preimage', args=dict(cert=c)))['valid'])


if __name__ == '__main__':
    unittest.main()
