import copy
import unittest
from fractions import Fraction as Q
import mpmath as mp
from perfectpower.legendre_endpoint import endpoint_packet,verify_endpoint


class EndpointTests(unittest.TestCase):
    def test_positive_period_enclosures(self):
        with mp.workdps(110):
            for z in ['1/4','1/64','1/1048576','1/1099511627776']:
                c=endpoint_packet(z,terms=48,bits=192,log_terms=128)
                self.assertTrue(verify_endpoint(c))
                v=mp.ellipk(1-mp.mpf(Q(z).numerator)/Q(z).denominator)
                lo,hi=(mp.mpf(Q(s).numerator)/Q(s).denominator for s in c['period_interval'])
                self.assertLess(lo,v);self.assertLess(v,hi)
                reg=v+mp.log(mp.mpf(Q(z).numerator)/Q(z).denominator)/2
                lo,hi=(mp.mpf(Q(s).numerator)/Q(s).denominator for s in c['regularized_interval'])
                self.assertLess(lo,reg);self.assertLess(reg,hi)

    def test_endpoint_is_regularized_and_divergent(self):
        c=endpoint_packet(0)
        self.assertIsNone(c['period_interval']);self.assertFalse(c['ordinary_endpoint_finite'])
        self.assertEqual(c['log_coefficient'],'-1/2');self.assertTrue(verify_endpoint(c))
        with mp.workdps(80):
            lo,hi=(mp.mpf(Q(s).numerator)/Q(s).denominator for s in c['finite_part'])
            self.assertLess(lo,mp.log(4));self.assertLess(mp.log(4),hi)

    def test_stronger_truncation(self):
        a=endpoint_packet('1/4',terms=8);b=endpoint_packet('1/4',terms=32)
        self.assertLess(Q(b['tail_upper_bound']),Q(a['tail_upper_bound']))

    def test_binding_and_input_rejections(self):
        a=endpoint_packet('1/64')
        for key,value in [('log_coefficient','1/2'),('parameter','1/2'),('tail_upper_bound','0'),
                          ('execution_verified',True),('terms',True),('ordinary_endpoint_finite',True)]:
            c=copy.deepcopy(a);c[key]=value;self.assertFalse(verify_endpoint(c))
        c=copy.deepcopy(a);c['coefficients'][0]['index']=False;self.assertFalse(verify_endpoint(c))
        for z in [-1,'1/3',True,.01]:
            with self.assertRaises(ValueError):endpoint_packet(z)
        self.assertFalse(verify_endpoint(a,work_limit=1))


if __name__=='__main__':unittest.main()
