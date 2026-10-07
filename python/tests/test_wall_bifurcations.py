from fractions import Fraction as Q
import unittest
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall
from perfectpower.wall_bifurcations import branch_polynomials, stationary_cubic_type, late_bias_fold_census
from perfectpower.wall_vacuum_branches import biased_stationary_branches
from perfectpower.core import evaluate


class WallBifurcations(unittest.TestCase):
    def test_fold_double_root_by_direct_factorization(self):
        r=stationary_cubic_type(1,3,2)
        self.assertEqual(r['type'],'fold')
        self.assertEqual(Q(r['double_source_root']),-1)
        self.assertEqual(Q(r['simple_source_root']),2)
        # u^3-3u-2=(u+1)^2(u-2).
        for u in range(-5,6): self.assertEqual(u**3-3*u-2,(u+1)**2*(u-2))

    def test_cusp_and_both_sides_of_fold(self):
        self.assertEqual(stationary_cubic_type(1,0,0)['multiplicities'],[3])
        self.assertEqual(stationary_cubic_type(1,3,1)['distinct_real_roots'],3)
        self.assertEqual(stationary_cubic_type(1,3,3)['distinct_real_roots'],1)
        with self.assertRaises(ValueError): stationary_cubic_type(0,3,2)

    def test_exact_endpoint_fold_is_retained(self):
        m=WallModel(1,1,1,10,0,4,.5)
        r=late_bias_fold_census(m,HiggsWall(portal=1,lam=1,v_GeV=2))
        self.assertTrue(any(e['s_interval']==['0','0'] for e in r['endpoint_events']))
        self.assertFalse(any(e['physical_metastable_fold'] for e in r['endpoint_events']))

    def test_interior_fold_and_physical_face(self):
        # Broken-Higgs a=3-s, b=(1-s); D is positive throughout [0,1].
        m=WallModel(1,3,1,10,0,1,1)
        r=late_bias_fold_census(m,HiggsWall(portal=0,v_GeV=10))
        self.assertEqual(r['physical_fold_events'],[])
        # Increase bias to 3: D(0)<0, D(1)>0, so one fold must occur.
        m=WallModel(1,3,1,10,0,3,1)
        r=late_bias_fold_census(m,HiggsWall(portal=0,v_GeV=10))
        self.assertEqual(len(r['physical_fold_events']),1)
        self.assertEqual(r['physical_fold_events'][0]['Higgs_branch'],'Higgs_broken')
        self.assertFalse(r['physical_fold_events'][0]['endpoint'])
        for T,count in [(0,1),(Q(9,10),2)]:
            census=biased_stationary_branches(m,HiggsWall(portal=0,v_GeV=10),T)
            self.assertEqual(sum(x['positive_physical_Hessian'] for x in census['branches']),count)

    def test_published_benchmark_has_no_active_spinodal(self):
        m=WallModel(30000,.1,.025000033333333335,300000,3000,2.584366229533845e-13,3000)
        r=late_bias_fold_census(m,HiggsWall())
        self.assertEqual(r['physical_fold_events'],[])
        for row in r['branches'].values():
            self.assertEqual(row['all_active_window_events'],[])
            self.assertEqual(row['discriminant_sign_at_zero'],1)
            self.assertEqual(row['discriminant_sign_at_onset'],1)
        for T in [0,30,200,2999]:
            q=branch_polynomials(m,HiggsWall())
            s=Q(str(T))**2/Q(30000)**2
            for row in q.values():
                self.assertGreater(evaluate(row['D'],s),0)

    def test_no_bias_guard(self):
        with self.assertRaises(ValueError):late_bias_fold_census(WallModel(1,1,1,10,0),HiggsWall())


if __name__=='__main__':unittest.main()
