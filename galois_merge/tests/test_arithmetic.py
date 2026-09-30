import sys,unittest,random
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from arithmetic import *
class Tests(unittest.TestCase):
 def test_transport(self):
  rng=random.Random(230930)
  for _ in range(250):
   F=tuple(rng.randrange(-20,21) for _ in range(4));T=(1,0,0,1)
   for j in range(8):T=mul(T,rng.choice([(0,1,1,0),(1,1,0,1),(1,0,1,1),(1,-1,0,1),(-1,0,0,1)]))
   G=substitute(F,T);self.assertEqual(substitute(G,inverse(T)),F);self.assertEqual(discriminant(G),discriminant(F))
   for x,y in [(2,3),(-4,1),(0,0)]:self.assertEqual(evaluate(G,x,y),evaluate(F,*apply(T,(x,y))))
 def test_composition(self):
  F=(3,5,-7,2);S=(1,2,0,1);T=(0,1,-1,0)
  self.assertEqual(substitute(substitute(F,S),T),substitute(F,mul(S,T)))
 def test_mutation(self):
  c=transport_certificate((1,0,-2,1),7,(1,2,0,1));self.assertTrue(check_transport(c));c['target'][0]+=1;self.assertFalse(check_transport(c))
 def test_bounds(self):
  T=(1,-3,2,-5)
  A,B=bound_transport(T,8,9)
  for x in range(-8,9):
   for y in range(-9,10):
    a,b=apply(T,(x,y));self.assertTrue(abs(a)<=A and abs(b)<=B)
 def test_sharing(self):
  r={'form':[1,0,-2,1],'rhs':1};s={**r,'restrictions':{'a_mod_2':0}}
  self.assertEqual(intern_obligations([r,r,s])['unique_count'],2)
  self.assertNotEqual(obligation_key(r['form'],1),obligation_key(r['form'],2))
 def test_local(self):
  self.assertTrue(local_obstruction((2,0,0,2),1,2)['empty']);self.assertFalse(local_obstruction((1,0,0,1),1,3)['empty'])
 def test_offsets(self):
  e=parse_seq('%N A048624 Duplicate\n%O A048624 0,1\n%S A048624 2,5,12,29,70\n')
  self.assertEqual(match_shift(e),[2]);e['offset']=1;self.assertEqual(match_shift(e),[1])
 def test_missing(self):
  with self.assertRaises(ValueError):parse_seq('%N A000129 Pell\n%S A000129 0,1,2\n')
if __name__=='__main__':unittest.main()
