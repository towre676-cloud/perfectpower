import sys,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
import numpy as np
from scipy.optimize import minimize
from develop_valentiner_frames import generators,group_closure,numeric
r=json.load(open(ROOT/'receipts/m22_interactions/valentiner_invariants.json'))
import sympy as s
x=s.symbols('x y z');poly=s.sympify(r['sextic']['polynomial'],locals=dict(zip(('x','y','z'),x)))
fun=s.lambdify(x,poly,'numpy')
der=s.lambdify(x,[s.diff(poly,t) for t in x],'numpy')
def vec(a):
 v=a[:3]+1j*a[3:];return v/np.linalg.norm(v)
def single(a):
 v=vec(a);fv=fun(*v)
 cg=-fv/abs(fv)*np.conjugate(np.array(der(*v)))
 g=np.r_[cg.real,cg.imag];z=np.r_[v.real,v.imag]
 return -abs(fv),(g-z*(z@g))/np.linalg.norm(a)
def obj(a):return single(a)[0]
rng=np.random.default_rng(310806)
sol=[]
for i in range(16):
 m=minimize(single,rng.normal(size=6),jac=True,method='BFGS',options={'gtol':1e-10,'maxiter':250})
 sol.append((m.fun,vec(m.x)))
print('range',min(a for a,v in sol),max(a for a,v in sol),flush=True)
v=sol[0][1]
group=[numeric(g) for g in group_closure(generators())[0]]
orbit=[]
for g in group:
 u=g@v
 if all(abs(abs(u.conj()@w)-1)>1e-7 for w in orbit):orbit.append(u)
print('line orbit',len(orbit),flush=True)
start=np.concatenate([np.r_[orbit[j].real,orbit[j].imag] for j in [0,1,4,6,9,13]])
weights=np.array([.07,.31,.9])
def frames(a):
 cols=[vec(a[6*i:6*i+6]) for i in range(6)]
 Cs=[np.column_stack(cols[3*i:3*i+3])*weights for i in range(2)]
 us=[]
 for C in Cs:us.append(np.linalg.eigh(C@C.conj().T)[1])
 V=us[0].conj().T@us[1];p=abs(V)**2
 u,w,c=np.sqrt([p[0,1],p[0,2],p[1,2]])
 depth=w*(1-w*w)/(u*c)
 J=float(np.imag(V[0,0]*V[1,1]*V[0,1].conj()*V[1,0].conj()))
 return {'Ceff':float(depth),'J':J,'squared_magnitudes':p.tolist()}
def total(a,k):
 vs=[vec(a[6*i:6*i+6]) for i in range(6)]
 value=sum(-abs(fun(*v)) for v in vs)+k*abs(vs[0].conj()@vs[3])**2
 grad=np.concatenate([single(a[6*i:6*i+6])[1] for i in range(6)])
 overlap=vs[0].conj()@vs[3]
 for i,cg in [(0,2*k*np.conjugate(overlap)*vs[3]),(3,2*k*overlap*vs[0])]:
  g=np.r_[cg.real,cg.imag];z=np.r_[vs[i].real,vs[i].imag]
  grad[6*i:6*i+6]+=(g-z*(z@g))/np.linalg.norm(a[6*i:6*i+6])
 return value,grad
# Independent central finite difference check of the analytic optimization gradient.
probe=start+.03*rng.normal(size=36);value,grad=total(probe,.013)
fd=np.array([(total(probe+np.eye(36)[i]*1e-6,.013)[0]-total(probe-np.eye(36)[i]*1e-6,.013)[0])/2e-6 for i in range(36)])
assert np.max(abs(fd-grad))<2e-8
out=[]
for k in [0.,.001,-.001,.01]:
 m=minimize(lambda a:total(a,k),start,jac=True,method='BFGS',options={'gtol':1e-9,'maxiter':500})
 out.append({'quartic_coefficient':k,'objective':float(m.fun),'gradient_norm':float(np.linalg.norm(m.jac)),'success':bool(m.success),'observables':frames(m.x)})
 print(out[-1],flush=True)
assert abs(out[0]['observables']['Ceff']-out[-1]['observables']['Ceff'])>1e-5
assert all(t['gradient_norm']<1e-7 for t in out)
json.dump({'scope':'Numerical local stationary branches on fixed unit-norm triplets, with phases analytically minimized; no global minimum certificate. No target input.','maximum_found_sextic_modulus':-min(a for a,v in sol),'numerical_line_orbit':len(orbit),'initial_orbit_indices':[0,1,4,6,9,13],'column_weights':weights.tolist(),'maximum_gradient_check_error':float(np.max(abs(fd-grad))),'cases':out},open(ROOT/'receipts/m22_interactions/valentiner_alignment_response.json','w'),indent=2)
