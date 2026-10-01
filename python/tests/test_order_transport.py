"""Independent symbolic coefficient checks for every order map (from the order-transport review of
fb30592), against `receipts/order_transports.json`."""
import copy,json,pathlib,sys,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
from order_transport import apply,mul,norm,det

class Poly:
 def __init__(self,terms=None):self.terms={m:c for m,c in (terms or {}).items() if c}
 @staticmethod
 def coerce(x):return x if isinstance(x,Poly) else Poly({(0,)*6:x})
 def __add__(self,other):
  other=self.coerce(other);d=self.terms.copy()
  for m,c in other.terms.items():d[m]=d.get(m,0)+c
  return Poly(d)
 __radd__=__add__
 def __neg__(self):return Poly({m:-c for m,c in self.terms.items()})
 def __sub__(self,other):return self+-self.coerce(other)
 def __rsub__(self,other):return self.coerce(other)+-self
 def __mul__(self,other):
  other=self.coerce(other);d={}
  for m,c in self.terms.items():
   for n,v in other.terms.items():
    k=tuple(a+b for a,b in zip(m,n));d[k]=d.get(k,0)+c*v
  return Poly(d)
 __rmul__=__mul__
 def __pow__(self,n):
  r=self.coerce(1)
  for _ in range(n):r=r*self
  return r
 def __eq__(self,other):return self.terms==self.coerce(other).terms

X=[Poly({tuple(int(i==j) for j in range(6)):1}) for i in range(6)]
ONE=(1,0,0)
def check(e):
 p,q=e['domain'];P,Q=e['codomain'];M=e['matrix'];g=e['generator_image'];d=det(M)
 if d==0 or d!=e['determinant'] or abs(d)!=e['index']:return False
 if e['kind']!=('ISOMORPHISM' if abs(d)==1 else 'EMBEDDING'):return False
 if apply(M,ONE)!=ONE or apply(M,(0,1,0))!=tuple(g):return False
 if mul(P,Q,g,g)!=apply(M,(0,0,1)):return False
 if apply(M,mul(p,q,X[:3],X[3:]))!=mul(P,Q,apply(M,X[:3]),apply(M,X[3:])):return False
 if norm(p,q,X[:3])!=norm(P,Q,apply(M,X[:3])):return False
 if d*d*(4*P**3-27*Q*Q)!=4*p**3-27*q*q:return False
 return True

class Tests(unittest.TestCase):
 def setUp(self):self.maps=json.loads((ROOT/'receipts'/'order_transports.json').read_text())['embeddings']
 def test_all_symbolic_identities(self):
  self.assertEqual(len(self.maps),22)
  for e in self.maps:self.assertTrue(check(e),e)
 def test_matrix_entry_mutations(self):
  for e in self.maps:
   for i in range(3):
    for j in range(3):
     bad=copy.deepcopy(e);bad['matrix'][i][j]+=1;self.assertFalse(check(bad))
 def test_generator_mutations(self):
  for e in self.maps:
   for i in range(3):
    bad=copy.deepcopy(e);bad['generator_image'][i]+=1;self.assertFalse(check(bad))
 def test_index_mutations(self):
  for e in self.maps:
   bad=copy.deepcopy(e);bad['index']+=1;self.assertFalse(check(bad))
 def test_direction_mutations(self):
  for e in self.maps:
   bad=copy.deepcopy(e);bad['domain'],bad['codomain']=bad['codomain'],bad['domain'];self.assertFalse(check(bad))


class LeanMaps(unittest.TestCase):
 def test_lean_file_matches_receipt(self):
  maps=json.loads((ROOT/'receipts'/'order_transports.json').read_text())['embeddings']
  lean=(ROOT/'PerfectPower'/'Generated'/'OrderMaps.lean').read_text()
  for i,e in enumerate(maps):
   p,q=e['domain'];P,Q=e['codomain']
   self.assertIn(f'def map_{i} : OrderMap {p} {q} {P} {Q} where',lean)
   self.assertIn(f"= {e['determinant']} := by decide",lean)
 def test_curve_sources_via_maps(self):
  import make_lean_curves as C
  from order_transport import emb
  n=0
  for cfg in C.CURVES.values():
   for s in cfg['sources']:
    if 'via' in s:
     k,(p,q),phi0=s['via'];e=json.loads((ROOT/'receipts'/'order_transports.json').read_text())['embeddings'][k]
     self.assertEqual((tuple(e['domain']),tuple(e['codomain'])),((p,q),(cfg['P'],cfg['Q'])))
     self.assertEqual(emb(cfg['P'],cfg['Q'],e['generator_image'],phi0),tuple(s['phi']));n+=1
  self.assertEqual(n,10)

if __name__=='__main__':unittest.main()
