import unittest
from fractions import Fraction as Q
from perfectpower.flavor_rg_rays import source_table, restrict, beta, verify_ray, coercive_lower_bound, su3_census
from perfectpower.flavor_spectral_moments import moments, recover, probability_chart, jarlskog_squared, alignment_rank, su3_orientation
from perfectpower.gauge_unification import predict, triplet_atlas


class PredictionMechanismTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        table, cls.digest = source_table()
        cls.rows = restrict(table)

    def test_complete_su3_census(self):
        result = su3_census(self.rows)
        self.assertTrue(result['both_ideal_inclusions_checked'])
        self.assertEqual(result['nonzero_real_ray_count'], 5)
        for ray in result['real_roots_including_zero']:
            if ray['zero_ray']:
                continue
            self.assertIsNotNone(ray['exact_coefficients'])
            v=ray['exact_coefficients']
            self.assertTrue(verify_ray(self.rows,v))
            self.assertEqual(su3_orientation(v)['trace_A2B2'],'0')
            self.assertTrue(coercive_lower_bound(v)['certified_coercive'])

    def test_scaling_and_corruption(self):
        v=list(map(Q,['1/576','0','7/1152','1/40','1/48','1/48','1/48']))
        t=Q(7,13)
        self.assertEqual(beta(self.rows,[t*x for x in v]),[t*t*x for x in v])
        v[4]+=Q(1,10**8)
        self.assertFalse(verify_ray(self.rows,v))

    def test_moment_inversion_and_cp_boundary(self):
        # Rational doubly stochastic interior with nonzero J².
        p=probability_chart(Q(1,2),Q(1,3),Q(1,3),Q(1,3))
        self.assertGreater(jarlskog_squared(p),0)
        for up,down in [([1,2,7],[3,5,11]), ([-5,-1,6],[-7,2,5])]:
            self.assertEqual(recover(up,down,moments(up,down,p)),p)
        self.assertEqual(jarlskog_squared([[1,0,0],[0,1,0],[0,0,1]]),0)
        self.assertLess(jarlskog_squared([[Q(1,2),Q(1,2),0],[Q(1,2),0,Q(1,2)],[0,Q(1,2),Q(1,2)]]),0)

    def test_degenerate_spectra_rejected(self):
        with self.assertRaises(ValueError):
            moments([1,1,2],[1,2,3],[[1,0,0],[0,1,0],[0,0,1]])

    def test_exact_alignment_rank(self):
        r=alignment_rank([-5,-1,6],[-7,2,5],['1/576','0','7/1152','1/40','1/48','1/48','1/48'])
        self.assertEqual(r['orientation_hessian_rank'],1)
        self.assertEqual(r['flat_probability_directions_at_stationarity'],3)
        self.assertFalse(r['isolated_CP_violating_stationary_point_possible'])

    def test_gauge_prediction_without_em_input(self):
        base=predict(30,9)
        self.assertEqual(base['status'],'no_physical_UV_unification')
        self.assertLess(Q(base['log_scale_over_2pi']),0)
        r=predict(30,9,('81/10','3/2','-3'))
        self.assertEqual(r['status'],'physical_above_anchor')
        self.assertEqual(Q(r['electromagnetic_inverse_at_anchor']),Q(394,3))
        self.assertFalse(r['electromagnetic_input_used'])
        atlas=triplet_atlas(30,9)
        self.assertEqual(len(atlas['rows']),35)
        self.assertTrue(atlas['menu_complete'])

    def test_unification_singular_and_threshold_transport(self):
        self.assertEqual(predict(30,9,(1,2,2))['status'],'inconsistent')
        self.assertEqual(predict(9,9,(1,2,2))['status'],'underdetermined')
        b=(Q(81,10),Q(3,2),Q(-3));o=(Q(1,7),Q(2,7),Q(3,7))
        x2=Q(30);x3=Q(9);r=predict(x2,x3,b,offsets=o)
        L=Q(r['log_scale_over_2pi']);U=Q(r['unified_inverse'])
        self.assertEqual(U+b[1]*L+o[1],x2)
        self.assertEqual(U+b[2]*L+o[2],x3)


if __name__=='__main__':
    unittest.main()
