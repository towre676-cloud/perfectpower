"""Independent CP, product-family covariance, and global spectrum checks."""
from pathlib import Path
import json,sys
import numpy as np
import sympy as sp
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
from develop_valentiner_frames import generators,group_closure,numeric
from develop_valentiner_link import match_link,coefficient_functions
from develop_m22_global_modes import rho
from perfectpower.flavor_mediator import canonical_mediator,mixing_record

def cp_fixture():
 r=json.loads((ROOT/'receipts/m22_interactions/valentiner_cp.json').read_text())
 X=np.array([[complex(sp.sympify(t).evalf()) for t in row] for row in r['unitary_CP_matrix']])
 return X

def test_sextic_CP_and_involution():
 X=cp_fixture();F,link,norm=coefficient_functions();rng=np.random.default_rng(610805)
 assert np.max(abs(X@X.conj()-np.eye(3)))<2e-14
 assert np.max(abs(X.conj().T@X-np.eye(3)))<2e-14
 for _ in range(10):
  v=rng.normal(size=3)+1j*rng.normal(size=3);v/=np.linalg.norm(v)
  assert abs(F(X@v.conj())-F(v).conjugate())<3e-14


def test_product_family_operator_covariance():
 rng=np.random.default_rng(666);u=rng.normal(size=3)+1j*rng.normal(size=3);d=rng.normal(size=3)+1j*rng.normal(size=3)
 L=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3))
 gu,gd=map(numeric,[generators()[0],generators()[3]])
 dressed=abs(u.conj()@L@d)**2
 transformed=abs((gu@u).conj()@(gu@L@gd.conj().T)@(gd@d))**2
 assert abs(dressed-transformed)<1e-11
 assert abs(abs(u.conj()@d)**2-abs((gu@u).conj()@(gd@d))**2)>.01


def test_physical_CP_with_reverse_mediator_coupling():
 X=cp_fixture();r=json.loads((ROOT/'receipts/m22_interactions/valentiner_link.json').read_text())
 W=np.array([[complex(*t) for t in row] for row in r['CP_basis']]);group=group_closure(generators())[0]
 L=numeric(group[r['selected_link_element']]);Cu=W@np.diag([.07,.31,.9]);Cd=W@np.diag([.08,.27,.85])
 Yu=canonical_mediator(.9*np.eye(3),Cu,h=.6)['Y'];Yd=match_link(L,Cd,g_reverse=.23)
 Yucp=canonical_mediator(.9*np.eye(3),X@Cu.conj(),h=.6)['Y'];Ydcp=match_link(X@L.conj()@X.conj().T,X@Cd.conj(),g_reverse=.23)
 a,b=mixing_record(Yu,Yd),mixing_record(Yucp,Ydcp)
 assert abs(a['J'])>.01 and abs(a['J']+b['J'])<2e-14
 for key in ('Vus','Vcb','Vub','depth'):assert abs(a[key]-b[key])<2e-14
 H=Yu@Yu.conj().T;K=Yd@Yd.conj().T
 assert abs(np.linalg.det(H@K-K@H).imag)>1e-10


def test_canonical_connection_spectrum_independent_traces():
 data=json.loads((ROOT/'receipts/m22_interactions/cap_transport.json').read_text());vs=sorted(data['component_vertices']);indices={v:i for i,v in enumerate(vs)}
 L=6*np.eye(252,dtype=np.int64)
 for e in data['transport_edges']:
  a,b=indices[e['source']],indices[e['target']]
  L[6*b:6*b+6,6*a:6*a+6]=-rho(e['permutation']).astype(np.int64)
 # Power traces independently verify the stored characteristic factor spectrum.
 r=json.loads((ROOT/'receipts/m22_interactions/m22_global_modes.json').read_text());power=np.eye(252,dtype=np.int64)
 for k in range(1,8):
  power=power@L
  expected=sum((-f['ascending_coefficients'][0])**k*f['multiplicity'] for f in r['canonical_connection_characteristic_factors'])
  assert int(np.trace(power))==expected
 assert r['global_zero_modes']==3 and r['global_squared_mass_gap']==.5
 assert sum(x['multiplicity'] for x in r['global_squared_mass_spectrum'])==44352

def test_symmetric_cube_messenger_bilinear():
 from math import factorial
 source=json.loads((ROOT/'receipts/m22_interactions/valentiner_invariants.json').read_text())['sextic']['terms']
 coeff={tuple(r['powers']):complex(sp.sympify(r['coefficient']).evalf()) for r in source}
 mons=[(a,b,3-a-b) for a in range(4) for b in range(4-a)]
 mult=np.array([factorial(3)/(factorial(a)*factorial(b)*factorial(c)) for a,b,c in mons])
 Q=np.zeros((10,10),complex)
 for i,a in enumerate(mons):
  for j,b in enumerate(mons):
   powers=tuple(x+y for x,y in zip(a,b));m=factorial(6)/np.prod([factorial(k) for k in powers])
   Q[i,j]=coeff.get(powers,0)*np.sqrt(mult[i]*mult[j])/m
 assert np.max(abs(Q.conj().T@Q-1.6*np.eye(10)))<2e-14
 def cubic(v):return np.array([np.sqrt(m)*np.prod(v**np.array(a)) for a,m in zip(mons,mult)])
 rng=np.random.default_rng(61036);points=[rng.normal(size=3)+1j*rng.normal(size=3) for _ in range(10)]
 V=np.column_stack([cubic(v) for v in points]);Vi=np.linalg.inv(V)
 for g in generators():
  S=np.column_stack([cubic(numeric(g)@v) for v in points])@Vi
  assert np.max(abs(S.T@Q@S-Q))<2e-12

if __name__=='__main__':
 import unittest
 suite=unittest.TestSuite(unittest.FunctionTestCase(fn) for fn in (
 test_sextic_CP_and_involution,test_product_family_operator_covariance,
 test_physical_CP_with_reverse_mediator_coupling,test_canonical_connection_spectrum_independent_traces,
 test_symmetric_cube_messenger_bilinear))
 result=unittest.TextTestRunner(verbosity=2).run(suite);raise SystemExit(not result.wasSuccessful())
