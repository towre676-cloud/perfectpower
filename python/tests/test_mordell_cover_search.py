import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import unittest
from unittest.mock import patch
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.elliptic_certificate_verifier import verify_independence
from perfectpower.elliptic_two_descent import lift_quartic_point
from perfectpower.mordell_cover_search import augment_descent, search_mordell_covers, homogeneous_cover_lift, affine_homogeneous_lift

ROOT = Path(__file__).resolve().parents[2]


def sample():
    cover = dict(quartic=['-2','0','0','1'],
                 x_numerator=['0','-2','0','0','1'],
                 y_numerator=['4','0','0','-4','0','0','1'])
    return dict(schema='pp-mordell-two-descent/1',k=-2,
                curve=EllipticCurve([0,-2]).specification,points=[],covers=[cover],
                rank_upper_bound=1,witness_rank_lower_bound=0,rank_determined=False)


class CoverPointSearch(unittest.TestCase):
    def test_positive_point_closes_rank_on_original_model(self):
        c = sample()
        lift = dict(cover_index=0,cover_point=['3','5'],mordell_point=['3','5'])
        result = augment_descent(c,[lift])
        self.assertEqual(result['witness_rank_lower_bound'],1)
        self.assertTrue(result['rank_determined'])
        self.assertTrue(verify_independence(result['independence']))
        self.assertEqual(c['points'],[])
        self.assertEqual(result['rank_upper_bound'],c['rank_upper_bound'])

    def test_changed_lift_wrong_model_and_bad_cover_reject(self):
        lift = dict(cover_index=0,cover_point=['3','5'],mordell_point=['3','4'])
        with self.assertRaises(ValueError): augment_descent(sample(),[lift])
        lift['mordell_point'] = ['3','5']; lift['cover_index'] = True
        with self.assertRaises(ValueError): augment_descent(sample(),[lift])
        c = sample(); c['curve'] = EllipticCurve([0,-3]).specification
        with self.assertRaises(ValueError): augment_descent(c,[])
        c = sample(); c['covers'][0]['x_numerator'][0] = '1'
        with self.assertRaises(ValueError): search_mordell_covers(c)

    @patch('perfectpower.mordell_cover_search.subprocess.run')
    def test_empty_and_timeout_never_promote_rank(self, run):
        run.return_value = subprocess.CompletedProcess([],0,'PP_COVER_POINTS:[]\n','')
        result = search_mordell_covers(sample(),gp='/unused')
        self.assertFalse(result['global_empty_proof'])
        self.assertFalse(result['integral_point_completeness'])
        self.assertEqual(result['lifts'],[])
        run.side_effect = subprocess.TimeoutExpired([],1)
        result = search_mordell_covers(sample(),gp='/unused')
        self.assertEqual(result['attempts'][0]['status'],'timeout')
        self.assertFalse(result['global_empty_proof'])

    @patch('perfectpower.mordell_cover_search.subprocess.run')
    def test_backend_coordinate_errors_reject(self, run):
        for output in ('PP_COVER_POINTS:[["3","4"]]\n',
                       'PP_COVER_POINTS:[["3","5"],["3","-5"]]\n'):
            run.return_value = subprocess.CompletedProcess([],0,output,'')
            with self.assertRaises((ValueError,ArithmeticError)):
                search_mordell_covers(sample(),gp='/unused')
        run.return_value = subprocess.CompletedProcess([],0,'PP_COVER_POINTS:[["3","5"]]\n','')
        with self.assertRaises(ArithmeticError):search_mordell_covers(sample(),height=2,gp='/unused')

    def test_search_controls(self):
        for value in (True,1,10000001):
            with self.assertRaises(ValueError):search_mordell_covers(sample(),height=value)
        for value in (True,0,61):
            with self.assertRaises(ValueError):search_mordell_covers(sample(),timeout=value)

    def test_signed_homogeneous_chart_and_exact_integrality(self):
        cover = sample()['covers'][0]
        for sign in (-1,1):
            c = homogeneous_cover_lift(-2,cover,[3,1,5*sign])
            self.assertEqual(c['mordell_point'],['3',str(5*sign)])
            self.assertTrue(c['target_integral'])
            self.assertEqual(c['integral_point'],[3,5*sign])
            self.assertEqual(c['B']**2,c['A']**3-2*c['scale']**6*c['coordinates'][2]**6)
        # 2(3,5)=(129/100,-383/1000), a nonintegral rational point.
        c = affine_homogeneous_lift(-2,cover,['129/100','-383/1000'])
        self.assertEqual(c['coordinates'],[129,100,-3830])
        self.assertFalse(c['target_integral'])
        for coordinates in ([6,2,20],[3,-1,5],[3,1,4],[3,1,0],[True,1,5]):
            with self.assertRaises(ValueError):homogeneous_cover_lift(-2,cover,coordinates)

    def test_rational_map_denominators_clear_in_both_coordinates(self):
        for n in (2,3):
            # t=n²X, z=n³Y; R=t³-2n⁶ on the original k=-2 model.
            d=-2*n**6
            from fractions import Fraction
            cover=dict(quartic=[str(d),'0','0','1'],
                       x_numerator=['0',str(Fraction(d,n**2)),'0','0',str(Fraction(1,n**2))],
                       y_numerator=[str(Fraction(d*d,n**3)),'0','0',str(Fraction(2*d,n**3)),'0','0',str(Fraction(1,n**3))])
            result=homogeneous_cover_lift(-2,cover,[3*n*n,1,5*n**3])
            self.assertEqual(result['integral_point'],[3,5])
            self.assertEqual(result['scale'],2 if n==2 else 27)

    def test_all_committed_positive_lifts_and_rank_changes(self):
        receipt = json.loads((ROOT/'receipts/mordell_cover_search.json').read_text())
        closed = []
        for row in receipt['rows']:
            k = row['k']
            c = json.loads((ROOT/'receipts/mordell_two_descent'/f'{"m" if k<0 else "p"}{abs(k)}.json').read_text())
            for lift in row['lifts']:
                self.assertEqual(lift_quartic_point(k,c['covers'][lift['cover_index']],lift['cover_point']),lift['mordell_point'])
                self.assertIn(lift['mordell_point'],c['points'])
                self.assertEqual(affine_homogeneous_lift(k,c['covers'][lift['cover_index']],lift['cover_point']),lift['homogeneous'])
            if row['rank_determined']:
                self.assertTrue(verify_independence(c['independence']))
                self.assertEqual(c['witness_rank_lower_bound'],c['rank_upper_bound'])
                closed.append(k)
            self.assertFalse(row['global_empty_proof'])
        self.assertEqual(sorted(closed),receipt['newly_determined'])
        self.assertEqual(receipt['errors'],{})

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_GP') or shutil.which('gp'),'optional PARI')
    def test_live_small_cover(self):
        result = search_mordell_covers(sample(),height=10)
        self.assertTrue(result['lifts'])
        self.assertTrue(augment_descent(sample(),result['lifts'])['rank_determined'])


if __name__ == '__main__': unittest.main()
