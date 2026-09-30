import unittest,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from engine import *
class Tests(unittest.TestCase):
 def test_cube(self):
  for n in range(-1000,1001):self.assertTrue(cube_floor(n)**3<=n<(cube_floor(n)+1)**3)
 def test_mordell(self):
  for k in range(-20,21):
   if not k:continue
   r=mordell(k,100); naive=[]
   for x in range(-10,101):
    v=x**3+k
    if v<0:continue
    y=isqrt(v)
    if y*y==v:naive.extend([(x,y)] if not y else [(x,y),(x,-y)])
   self.assertEqual(r['points'],[list(p) for p in sorted(naive)])
 def test_forms(self):
  for D,h in [(3,1),(4,1),(7,1),(8,1),(20,2),(23,3),(31,3),(84,4)]:self.assertEqual(len(reduced_forms(-D)),h)
 def test_units(self):self.assertTrue(unit_cubes(4)['all_cubes']);self.assertFalse(unit_cubes(6)['all_cubes'])
 def test_convergents(self):self.assertEqual(convergents(80),[orbit(i+1) for i in range(80)])
 def test_gf(self):self.assertEqual(gf_coeffs([0,1],[1,-2,-1],100),[Fraction(orbit(i)[1]) for i in range(100)])
 def test_triples(self):
  for m in range(2,40):
   for n in range(1,m):
    a,b,c=triple(m,n);self.assertEqual(a*a+b*b,c*c)
 def test_quartic(self):
  for a,b,c in [(1,0,1),(2,3,1),(-1,0,25)]:
   for u in range(-20,21):
    w=a*u**4+b*u*u+c
    if w<0:continue
    v=isqrt(w)
    if v*v==w:
     for z in set([v,-v]):
      X,Y=even_quartic_point(a,b,c,u,z);self.assertIn((u,z),even_quartic_lifts(a,b,c,X,Y))
 def test_lattice(self):
  for p in range(1,15):
   for lo in range(-10,11):
    for hi in range(lo,20):self.assertEqual(lattice_count(p,[0,2],lo,hi),sum(n%p in {0,2%p} for n in range(lo,hi+1)))
 def test_monomial(self):
  for a in range(1,6):
   for b in range(1,6):self.assertEqual(monomial_pairs(a,b,30),[(x,y) for x in range(1,31) for y in range(1,31) if x**a==y**b])
if __name__=='__main__':unittest.main()
