import math
import unittest
from perfectpower.gamma_arithmetic import factorial_window_obstruction, factorial_window_lean


class FactorialWindowTests(unittest.TestCase):
    def test_witness_agrees_with_independent_finite_product(self):
        for n in range(1,32):
            for width in range(n+1):
                value=math.prod(range(n-width+1,n+1))
                for degree in (2,3,4):
                    result=factorial_window_obstruction(n,width,degree)
                    if result['status']=='NOT_POWER':
                        p=result['witness']['prime'];exponent=0
                        while value%p==0:value//=p;exponent+=1
                        self.assertEqual(exponent,result['witness']['exponent'])
                        self.assertNotEqual(exponent%degree,0)
                        value=math.prod(range(n-width+1,n+1))

    def test_huge_variable_width_and_unknown(self):
        result=factorial_window_obstruction(10**30,10**20,2)
        self.assertEqual(result['status'],'NOT_POWER')
        self.assertEqual(factorial_window_obstruction(49,1,2,[7])['status'],'UNKNOWN')
        self.assertEqual(factorial_window_obstruction(0,0,2)['status'],'UNKNOWN')
        text=factorial_window_lean(result)
        self.assertIn('legendre_window',text)
        bad=dict(result,witness=dict(result['witness'],exponent=0))
        with self.assertRaises(ValueError):factorial_window_lean(bad)

    def test_bad_domains(self):
        for args in [(3,4,2,[2]),(3,1,2,[4]),(3,1,2,[2,2]),(3,1,1,[2])]:
            with self.assertRaises(ValueError):factorial_window_obstruction(*args)


if __name__=='__main__':unittest.main()
