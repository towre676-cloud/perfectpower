"""Source-to-display arithmetic regression; no browser rendering claims."""
import json,unittest
from fractions import Fraction as Q
from math import gcd,comb
from pathlib import Path
from perfectpower import e8_periods as e8
from perfectpower import raghava_coxeter as rc
ROOT=Path(__file__).resolve().parents[2]
class CalculatedResonance(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  cls.d=json.loads(json.loads((ROOT/'web/integral-families/atlas-data.json').read_text())['payload_json']);cls.c=cls.d['calculations']
 def test_populations_and_power_maps(self):
  self.assertEqual([r['exponent'] for r in self.c['primitive_phases']],[a for a in range(1680) if gcd(a,1680)==1])
  for a in e8.EXPONENTS:self.assertEqual(sum(r['image_exponent']==a for r in self.c['primitive_phases']),48)
  for r in self.d['branches']:
   self.assertEqual(r['exponent'],1+1680*r['index']);self.assertEqual(r['primitive'],gcd(r['exponent'],443520)==1);self.assertEqual(r['exponent']*264%443520,264);self.assertEqual(r['exponent']%30,1)
 def test_every_root_through_every_operator_step(self):
  c=self.c['coxeter_simple_basis'];self.assertEqual(c,[list(row) for row in e8.coxeter_matrix()])
  for root in self.d['roots']:
   point=root
   for k in range(30):
    nxt=self.d['roots'][point['next']];self.assertEqual(list(e8.matvec(c,point['simple_coordinates'])),nxt['simple_coordinates']);self.assertEqual(list(e8.coxeter_action(tuple(point['doubled_root']))),nxt['doubled_root']);point=nxt
   self.assertEqual(point,root)
 def test_moments_and_cancellation(self):
  for name,spectrum in [('reflection',rc.e8_reflection_spectrum()),('adjoint',rc.e8_adjoint_spectrum()),('induced_adjoint',rc.induce_spectrum(rc.e8_adjoint_spectrum(),264))]:
   m=rc.moment_vector(spectrum,3);self.assertEqual(self.c['profiles'][name]['moments'],list(map(str,m)));self.assertEqual(self.c['profiles'][name]['mellin'],list(map(str,rc.mellin_from_moments(m))))
  self.assertEqual(self.c['profiles']['adjoint']['mellin'][1],'0');self.assertEqual(self.c['profiles']['induced_adjoint']['mellin'][1],'0')
 def test_direct_matrix_series_and_mellin_partials(self):
  m=e8.identity();e=[Q(1),Q(0),Q(0)];sums=[Q(0)]*3;r=c=Q(0)
  for row in self.c['series']:
   n=row['n'];m=e8.matmul(m,rc.e8_reflection_operator());trace=sum(m[i][i] for i in range(8));self.assertEqual(str(trace),row['trace'])
   for j in range(3):sums[j]+=e[j]*Q(trace,n*n*comb(2*n,n));self.assertEqual(float(sums[j]),row['partial'][j])
   for j in (2,1):e[j]+=e[j-1]/(n*n)
   r+=Q(240 if n%30==0 else 0,n*n);cp=e8.matrix_power(e8.coxeter_matrix(),n);c+=Q(sum(cp[i][i] for i in range(8)),n*n)
   self.assertEqual(float(r),row['root_mellin']);self.assertEqual(float(c),row['cartan_mellin']);self.assertEqual(float(r+c),row['adjoint_mellin']);self.assertEqual(Q(row['mellin_tail_bound']),Q(248,n))
  for j,b in enumerate(self.c['series_enclosures']):self.assertLessEqual(Q(b['lower']),sums[j]);self.assertGreaterEqual(Q(b['upper']),sums[j]);self.assertTrue(b['independent_enclosure_overlap'])
if __name__=='__main__':unittest.main()
