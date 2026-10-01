"""Independent arithmetic oracles for the integer theorems (not formal proof)."""
import math,random,unittest

class Oracles(unittest.TestCase):
    def test_scaled_newton_against_python_isqrt(self):
        rng=random.Random(20261001);hits=0
        for _ in range(12000):
            m=rng.randrange(1,50);n=rng.randrange(4*m**4,4*m**4+10**10)
            t=n//(4*m*m);r=math.isqrt(t)
            for a in (r,r+1):
                if (a-1)**2<t<(a+1)**2:
                    b=m*a+n//(4*m*a);root=math.isqrt(n)
                    self.assertTrue((b-1)**2<n<(b+1)**2)
                    self.assertIn(b,(root,root+1));hits+=1
        self.assertGreater(hits,10000)
    def test_upper_polynomial_identity(self):
        rng=random.Random(42)
        for _ in range(5000):
            x,y,q,z=[rng.randrange(-10**6,10**6) for j in range(4)]
            self.assertEqual(4*((z+1)**2-x-1),
                (2*z+1-q-y)*(2*z+3+q+y)+(q+1-y)**2+4*(q*y+y-x-1))
    def test_lower_polynomial_identity(self):
        rng=random.Random(17)
        for _ in range(5000):
            n,m,a=[rng.randrange(-10**5,10**5) for j in range(3)]
            w=4*m*m*a*a+n-4*m*m
            self.assertEqual(16*m*m*a*a*n-w*w,
                (n-4*m*m*(a-1)**2)*(4*m*m*(a+1)**2-n))

if __name__=='__main__':unittest.main()
