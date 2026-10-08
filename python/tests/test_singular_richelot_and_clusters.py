from fractions import Fraction as Q
import random
import unittest

from perfectpower import singular_richelot as R
from perfectpower.cluster_stable_reduction import PadicDomain, PuiseuxDomain, analyse, cluster_picture
from perfectpower.cluster_monodromy import topological_inertia, safe_radius

PR = [p for p in range(3, 50) if R.is_prime(p)]


class SingularRichelotTests(unittest.TestCase):
    def test_even_sextic_splits_over_Q_with_matching_lpolys(self):
        G = [[-1, 0, 1], [-4, 0, 1], [-9, 0, 1]]
        self.assertEqual(R.classify_splitting(G), 'singular_richelot')
        r = R.singular_richelot(G)
        self.assertEqual(r['field_D'], 1)
        rows = R.verify_singular_lpolys(G, PR)
        self.assertGreater(len(rows), 8)
        self.assertTrue(all(x['equal'] for x in rows))
        self.assertTrue(all(x['jacobian_order'] == x['product_order'] for x in rows))

    def test_infinity_root_rational_pencil(self):
        G = [[-1, 2, 0], [2, -4, 3], [-3, 6, -2]]
        r = R.singular_richelot(G)
        self.assertEqual(r['field_D'], 1)
        self.assertTrue(all(x['equal'] for x in R.verify_singular_lpolys(G, PR)))

    def test_quadratic_pencil_gives_weil_restriction(self):
        for G, D in (([[2, 0, 1], [0, 1, 0], [2, -4, 1]], 2), ([[-1, 0, 1], [0, 1, 0], [-1, 4, 1]], -1)):
            r = R.singular_richelot(G)
            self.assertEqual(r['field_D'], D)
            self.assertTrue(r['E2_is_conjugate_of_E1'])
            rows = R.verify_singular_lpolys(G, PR)
            self.assertEqual({x['kind'] for x in rows}, {'split', 'inert'})
            self.assertTrue(all(x['equal'] for x in rows))
            for x in rows:
                if x['kind'] == 'inert':
                    self.assertEqual(x['curve_lpoly'][1], 0)

    def test_twisted_product_is_rejected_by_lpolys(self):
        r = R.singular_richelot([[-1, 0, 1], [-4, 0, 1], [-9, 0, 1]])
        F = [Q(c) for c in r['sextic_form']]
        E1 = [R.K(Q(c)) for c in r['E1_cubic']]
        E2t = [R.K(Q(c) * 2 ** (3 - i)) for i, c in enumerate(r['E2_cubic'])]
        mism = [p for p in (5, 7, 11, 13, 17, 19, 23) if [int(c) for c in R.pmul(R.elliptic_lpoly_K(E1, p, 1, False), R.elliptic_lpoly_K(E2t, p, 1, False))] != R.curve_lpoly(F, p, 2)]
        self.assertTrue(mism)

    def test_smooth_richelot_target_isogenous(self):
        for G in ([[1, 1, 1], [3, 2, 1], [7, 3, 1]], [[1, 1, 0], [3, 2, 1], [7, 3, 1]]):
            v = R.verify_smooth_lpolys(G, PR)
            self.assertTrue(v['target_squarefree'])
            self.assertTrue(v['rows'] and all(x['equal'] for x in v['rows']))

    def test_bad_inputs(self):
        with self.assertRaises(ValueError):
            R.singular_richelot([[1, 1, 1], [3, 2, 1], [7, 3, 1]])  # nonzero determinant
        with self.assertRaises(ValueError):
            R.singular_richelot([[-1, 0, 1], [-1, 0, 1], [-9, 0, 1]])  # repeated roots
        self.assertEqual(R.classify_splitting([[0, 0, 1], [-4, 0, 1], [-9, 0, 1]]), 'singular_source')

    def test_random_constructed_splittings(self):
        rng = random.Random(5)
        for _ in range(6):
            l1 = [Q(rng.randint(-3, 3)), Q(rng.choice([1, 2]))]
            l2 = [Q(rng.randint(-3, 3)), Q(rng.choice([0, -1]))]
            if not l1[1] * l2[0] - l1[0] * l2[1]:
                continue
            G = []
            for _ in range(3):
                a, b = rng.choice([-2, -1, 1, 3]), rng.choice([-3, -1, 1, 2])
                G.append([a * l1[0] ** 2 + b * l2[0] ** 2, 2 * (a * l1[0] * l1[1] + b * l2[0] * l2[1]), a * l1[1] ** 2 + b * l2[1] ** 2])
            if R.classify_splitting(G) != 'singular_richelot':
                continue
            self.assertTrue(all(x['equal'] for x in R.verify_singular_lpolys(G, PR[:8])))


# conductor exponents printed by PARI/GP 2.17.2 genus2red for these curves
PARI = [
    (3, 1, [0, 3, 1, 4, 2, 5], 1, 2), (3, 1, [0, 3, 1, 4, 2, 5], 3, 4), (5, 1, [0, 5, 25, 1, 2], 1, 2),
    (5, 1, [0, 5, 25, 1, 2], 5, 3), (7, 1, [0, 49, 1, 344, 2], 1, 2), (3, 1, [0, 1, 2, 3, 9], 1, 2),
    (5, 5, [[0, 1], [0, -1], [0, 2], [0, -2], 1, 2], 1, 3), (5, 5, [[0, 1], [0, -1], [0, 2], [0, -2], 0], 1, 4),
    (3, 3, [[0, 1], [0, -1], [9, 1], [9, -1], 1], 1, 3), (3, 3, [[0, 1], [0, -1], [9, 1], [9, -1], [18, 1], [18, -1]], 1, 4),
    (7, 3, [[0, 49], [0, -49], 0, 1, 2], 1, 0), (5, 2, [[1, 25], [1, -25], 0, 2, 3, 4], 5, 4),
]


class ClusterTests(unittest.TestCase):
    def test_conductors_match_recorded_pari_values(self):
        for p, D, roots, c, e in PARI:
            a = analyse(PadicDomain(p, D), roots, c)
            self.assertEqual(a['reduction_over_K']['conductor_exponent'], e, (p, D, roots, c))

    def test_three_twins_theta_graph(self):
        a = analyse(PadicDomain(3), [0, 3, 1, 4, 2, 5])
        self.assertEqual(a['potential_toric_rank'], 2)
        self.assertEqual(len(a['stable_graph']['vertices']), 2)
        self.assertEqual([e['length'] for e in a['stable_graph']['edges']], ['2', '2', '2'])
        self.assertTrue(a['reduction_over_K']['semistable_over_K'])

    def test_nested_and_disjoint_depths(self):
        a = analyse(PadicDomain(5), [0, 5, 25, 1, 2])
        depths = sorted(c['depth'] for c in a['clusters'])
        self.assertEqual(depths, ['0', '1', '2'])
        self.assertEqual(a['potential_abelian_rank'], 1)

    def test_swapped_clusters_have_moved_roles(self):
        a = analyse(PadicDomain(3, 3), [[0, 1], [0, -1], [9, 1], [9, -1], 1])
        self.assertIn('rep', a['reduction_over_K']['roles'].values())
        self.assertFalse(a['ddmm_semistable_over_K'])

    def test_higher_genus_family_and_braid_replay(self):
        H = Q(1, 2)
        fams = [([{0: 0}, {1: 1}, {2: 1}, {0: 1}, {0: 2}], {1: 1}),
                ([{H: 1}, {H: -1}, {H: 2}, {H: -2}, {0: 0}], {0: 1}),
                ([{H: 1}, {H: 1, 2: 1}, {H: -1}, {H: -1, 2: 1}, {0: 1}], {0: 1}),
                ([{0: 0}, {1: 1}, {1: 2}, {1: 3}, {0: 1}, {0: 2}, {0: 3}], {0: 1})]
        for roots, c in fams:
            a = analyse(PuiseuxDomain(), roots, c)
            t = topological_inertia(roots, c, samples=1024)
            self.assertEqual(t['topological_conductor'], a['reduction_over_K']['conductor_exponent'])
            self.assertEqual(t['potential_toric_rank'], a['potential_toric_rank'])

    def test_radius_is_exact_rational(self):
        r = safe_radius([{0: 0}, {1: 1}, {0: 1}, {0: 1, 2: 1}, {0: 2}], {0: 1})
        self.assertIsInstance(r, Q)
        self.assertGreater(r, 0)

    def test_random_padic_internal_consistency(self):
        rng = random.Random(3)
        for _ in range(80):
            p = rng.choice([3, 5, 7])
            roots = set()
            while len(roots) < rng.choice([5, 6, 7, 8]):
                roots.add(rng.choice([0, 1, 2]) + rng.choice([0, 1, -1]) * p ** rng.randint(0, 3) + rng.choice([0, 1]) * p ** rng.randint(2, 4))
            a = analyse(PadicDomain(p), sorted(roots), rng.choice([1, p]))
            ra = a['reduction_over_K']
            self.assertEqual(ra['semistable_over_K'], a['ddmm_semistable_over_K'])
            self.assertLessEqual(ra['toric_rank'], a['potential_toric_rank'])
            self.assertEqual(ra['conductor_exponent'] + ra['inertia_invariants_dimension'], 2 * a['genus'])

    def test_bad_domains(self):
        with self.assertRaises(ValueError):
            PadicDomain(2)
        with self.assertRaises(ValueError):
            PadicDomain(5, 4)
        with self.assertRaises(ValueError):
            PadicDomain(7, 2)  # 2 is a square mod 7
        with self.assertRaises(ValueError):
            cluster_picture(PadicDomain(3, 3), [[0, 1], 1, 2], 1)  # not Galois stable
        with self.assertRaises(ValueError):
            cluster_picture(PuiseuxDomain(), [{Q(1, 3): 1}, {0: 1}, {0: 2}], 1)


if __name__ == '__main__':
    unittest.main()
