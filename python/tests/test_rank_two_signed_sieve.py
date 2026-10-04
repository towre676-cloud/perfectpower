"""Independent signed powers versus finite modular period tables."""
import unittest
from orbit_lattice import allowed, apply, IDENTITY, matrix_period
from rank_one_sources import Mx, mm


def signed_power(unit, inverse, exponent):
    a = Mx(9, 6, unit if exponent >= 0 else inverse)
    r = IDENTITY
    for _ in range(abs(exponent)):
        r = mm(r, a)
    return r


class SignedSieveTests(unittest.TestCase):
    def test_inverse_certificates(self):
        for u, v in [((-1,-3,1),(-1,-3,-1)),((-1,0,2),(-289,-24,34))]:
            self.assertEqual(mm(Mx(9,6,u),Mx(9,6,v)),IDENTITY)
            self.assertEqual(mm(Mx(9,6,v),Mx(9,6,u)),IDENTITY)

    def test_signed_residue_equivalence(self):
        units = [(-1,-3,1),(-1,0,2)]
        inverses = [(-1,-3,-1),(-289,-24,34)]
        for modulus in [3,6,9,15,21]:
            r = allowed(9,6,units,(-3,-3,1),modulus,-3,plane=(0,1,0))
            accepted = {tuple(z) for z in r['allowed_residues']}
            m,n = r['periods']
            for e in range(-12,13):
                for f in range(-12,13):
                    w = apply(mm(signed_power(units[0],inverses[0],e),
                                 signed_power(units[1],inverses[1],f)),(-3,-3,1))
                    self.assertEqual((e % m,f % n) in accepted,
                                     w[1] % modulus == 0 and w[0] % 3 == 0)

    def test_truncated_period_rejected(self):
        with self.assertRaises(ValueError):
            matrix_period(Mx(9,6,(-1,-3,1)),15,limit=1)


if __name__ == '__main__':
    unittest.main()
