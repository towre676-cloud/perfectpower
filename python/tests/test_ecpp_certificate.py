import copy,json,unittest
from pathlib import Path
from perfectpower.ecpp_certificate import BRAINPOOL384_PRIME,verify_ecpp,ecpp_chain_details,terminal_prime,affine_add


class ECPPArithmetic(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.certificate=json.loads((Path(__file__).resolve().parents[2]/'receipts/brainpool384_ecpp/certificate.json').read_text())

    def test_complete_chain(self):
        d=ecpp_chain_details(self.certificate,BRAINPOOL384_PRIME)
        self.assertEqual(d['stages'],15)
        self.assertEqual(d['terminal_prime'],23354449048573)
        self.assertTrue(verify_ecpp(self.certificate,BRAINPOOL384_PRIME))

    def test_corruptions_and_missing_links(self):
        for change in (
            lambda c:c[0].__setitem__(0,c[0][0]+2),
            lambda c:c[0].__setitem__(1,0),
            lambda c:c[0].__setitem__(2,1),
            lambda c:c[0][4].__setitem__(0,0),
            lambda c:c[0].__setitem__(2,True),
            lambda c:c.pop(),
            lambda c:c.reverse()):
            c=copy.deepcopy(self.certificate);change(c)
            self.assertFalse(verify_ecpp(c,BRAINPOOL384_PRIME))

    def test_exact_terminal_primes_and_nonunits(self):
        for n in (2,3,5,97,1009):self.assertTrue(terminal_prime(n))
        for n in (1,4,9,341,561,True,10**14+1):self.assertFalse(terminal_prime(n))
        with self.assertRaises(ValueError):affine_add((0,1),(3,1),0,15)


if __name__=='__main__':unittest.main()
