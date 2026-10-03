import unittest
from orbit_lattice import allowed, apply, matrix_period
from rank_one_sources import Mx, mm

class OrbitLatticeTests(unittest.TestCase):
    def test_rank_one_including_negative_exponents(self):
        eta=(9337,1682,1144)
        cert=allowed(-6,12,[eta],(16,3,2),8,-2)
        powers=matrix_period(Mx(-6,12,eta),8)
        for n in range(-2*len(powers),2*len(powers)):
            w=apply(powers[n%len(powers)],(16,3,2))
            self.assertEqual([n%len(powers)] in cert['allowed_residues'],w[2]%8==0 and w[0]%2==0)
    def test_rank_two_filter(self):
        cert=allowed(6,2,[(-5,0,1),(11,1,-2)],(1,0,0),5,1)
        self.assertGreater(cert['tested_residues'],len(cert['allowed_residues']))
        self.assertIn([0,0],cert['allowed_residues'])
    def test_fail_closed(self):
        with self.assertRaises(ValueError): matrix_period([[0]*3 for _ in range(3)],3,10)
        with self.assertRaises(ValueError): allowed(6,2,[(1,0,0)],(1,0,0),5,2)
