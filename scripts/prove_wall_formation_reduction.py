"""Exact polynomial reduction and stochastic-flow identities; requires SymPy."""
from pathlib import Path
import json
import sympy as s
u,y,h,lam,mu,alpha,H,h0,kappa,c,cH,T,v,eps=s.symbols('u y h lam mu alpha H h0 kappa c cH T v eps',positive=True)
V=lam*(u*u-1)**2/4+mu**2*(y+alpha*u*u/mu**2)**2/2+H*(h*h-h0*h0+kappa*(u*u-1)/H)**2/4+c*T*T*u*u/(2*v*v)+cH*T*T*h*h/(2*v*v)
valley=-alpha*u*u/mu**2
red=s.expand(V.subs({y:valley,h:0}));le=lam+kappa**2/H
bridge=v*v*(le*(1+eps)+kappa*h0*h0)/c
identities={
 'Gaussian_valley_stationarity':s.diff(V,y).subs(y,valley),
 'source_force_on_restored_branch':s.diff(red,u)-u*(le*u*u+c*T*T/v**2-le-kappa*h0*h0),
 'temperature_bridge_reduced_force':s.diff(red,u).subs(T*T,bridge)-le*(u**3+eps*u),
 'Higgs_curvature_on_valley':s.diff(V,h,2).subs({h:0,y:valley})-(-H*h0*h0+kappa*(u*u-1)+cH*T*T/v**2),
 'induced_valley_kinetic_metric':s.diff(valley,u)**2-4*alpha**2*u*u/mu**4,
}
t,gamma,a=s.symbols('t gamma a',positive=True);q=a/s.sqrt(1+2*t*a*a/gamma)
identities['exact_quartic_Bernoulli_flow']=s.diff(q,t)+q**3/gamma
r,theta,area,dt=s.symbols('r theta area dt',positive=True)
d=s.exp(-r*dt/gamma);var=theta/area*(1-d*d)/r
identities['OU_equilibrium_covariance']=d*d*theta/(area*r)+var-theta/(area*r)
identities['OU_zero_mass_limit']=s.limit(var,r,0)-2*theta*dt/(area*gamma)
identities['OU_half_step_composition']=s.exp(-r*dt/gamma)*theta/area*(1-s.exp(-r*dt/gamma))/r+theta/area*(1-s.exp(-r*dt/gamma))/r-var
checks={name:bool(s.simplify(expr)==0) for name,expr in identities.items()}
assert all(checks.values()),checks
root=Path(__file__).resolve().parents[1]
(root/'receipts/flavor_cosmology/wall_formation_exact_identities.json').write_text(json.dumps({'all_passed':True,'identities':checks,'sympy_version':s.__version__},indent=2,sort_keys=True)+'\n')
print(json.dumps(checks,indent=2))
