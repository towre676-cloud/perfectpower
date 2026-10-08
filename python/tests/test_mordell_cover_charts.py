import copy,unittest,os,shutil,subprocess
from unittest.mock import patch
from fractions import Fraction
from perfectpower.mordell_cover_charts import chart_cover,lift_chart_point,projective_cover_lift,search_cover_box
from perfectpower import polyalg as P

C=dict(quartic=['-2','0','0','1'],x_numerator=['0','-2','0','0','1'],y_numerator=['4','0','0','-4','0','0','1'])

class CoverCharts(unittest.TestCase):
    def test_translation_scaling_and_reciprocal_transport(self):
        for M,point in [([[1,3],[0,1]],['0','5']),([[3,0],[0,1]],['1','5']),([[0,1],[1,0]],['1/3','5/9']),([[1,0],[1,1]],['-3/2','5/4'])]:
            c=chart_cover(-2,C,M);p=lift_chart_point(c,point)
            self.assertEqual(p['source_coordinates'],[3,1,5]);self.assertEqual(p['mordell_point'],['3','5'])
        c=chart_cover(-2,C,[[1,3],[0,1]]);self.assertEqual(c['source_height_factor'],4)
        c=chart_cover(-2,C,[[3,0],[0,1]]);self.assertEqual(c['determinant'],3)

    def test_exact_binary_form_substitution_independent(self):
        import sympy as S
        t=S.Symbol('t')
        for M in ([[1,3],[0,1]],[[3,0],[0,1]],[[1,-2],[2,1]],[[0,1],[1,0]]):
            a,b=M[0];c,d=M[1];chart=chart_cover(-2,C,M)
            for key,n in [('quartic',4),('x_numerator',4),('y_numerator',6)]:
                expected=S.expand(sum(S.Rational(v)*(a*t+b)**i*(c*t+d)**(n-i) for i,v in enumerate(C[key])))
                got=sum(S.Rational(v)*t**i for i,v in enumerate(chart['cover'][key]))
                self.assertEqual(S.expand(got-expected),0)

    def test_primitive_weighted_normalization_and_ordinate_scaling(self):
        c=chart_cover(-2,C,[[2,0],[0,2]],4)
        p=lift_chart_point(c,['3','5'])
        self.assertEqual(p['source_coordinates'],[3,1,5])
        # A transformed cubic has a rational point at source infinity.
        source=chart_cover(-2,C,[[3,1],[1,0]])['cover']
        pole=lift_chart_point(chart_cover(-2,source,[[0,1],[1,0]]),['0','5'])
        self.assertEqual(pole['source_coordinates'],[1,0,5])
        self.assertIsNone(pole['source_affine_point'])
        self.assertEqual(pole['mordell_point'],['3','5'])
        # Invalid maps and nonpoints are still rejected.
        R=dict(quartic=['1','0','0','0','1'],x_numerator=['1','0','0','0','1'],y_numerator=['1','0','0','0','1'])
        with self.assertRaises(ValueError):chart_cover(-2,R,[[0,1],[1,0]])
        with self.assertRaises(ValueError):projective_cover_lift(-2,C,[1,0,1])

    def test_corruption_and_domains(self):
        c=chart_cover(-2,C,[[1,3],[0,1]])
        b=copy.deepcopy(c);b['cover']['quartic'][0]='24'
        with self.assertRaises(ValueError):lift_chart_point(b,['0','5'])
        for M in ([[1,1],[1,1]],[[True,0],[0,1]],[[1000001,0],[0,1]]):
            with self.assertRaises(ValueError):chart_cover(-2,C,M)
        for point in (['0','4'],['0','0']):
            with self.assertRaises(ValueError):lift_chart_point(c,point)
        with self.assertRaises(ValueError):search_cover_box(-2,C,denominator_min=5,denominator_max=4)

    @patch('perfectpower.mordell_cover_charts.subprocess.run')
    def test_box_bound_checks_and_timeout_are_separate(self,run):
        run.return_value=subprocess.CompletedProcess([],0,'PP_BOX_POINTS:[["0","5"]]\n','')
        c=search_cover_box(-2,C,matrix=[[1,3],[0,1]],numerator_bound=2,denominator_max=1,gp='/unused')
        self.assertEqual(c['lifts'][0]['mordell_point'],['3','5'])
        self.assertEqual(c['status'],'point_returned');self.assertFalse(c['global_empty_proof'])
        run.return_value=subprocess.CompletedProcess([],0,'PP_BOX_POINTS:[]\n','')
        self.assertEqual(search_cover_box(-2,C,gp='/unused')['status'],'no_point_returned')
        run.side_effect=subprocess.TimeoutExpired([],1)
        self.assertEqual(search_cover_box(-2,C,gp='/unused')['status'],'timeout')

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_GP') or shutil.which('gp'),'optional PARI')
    def test_live_chart_and_denominator_box(self):
        c=search_cover_box(-2,C,matrix=[[1,3],[0,1]],numerator_bound=2,denominator_max=1)
        self.assertEqual(c['lifts'][0]['mordell_point'],['3','5'])
        c=search_cover_box(-2,C,matrix=[[1,3],[0,1]],numerator_bound=10,denominator_min=2,denominator_max=3)
        self.assertFalse(c['global_empty_proof'])

if __name__=='__main__':unittest.main()
