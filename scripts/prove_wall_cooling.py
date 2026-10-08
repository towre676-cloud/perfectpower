"""Exact thermal bulk classification, energy cancellation and PT reference identities."""
from pathlib import Path
import json
import sympy as s
U,Z,U0,Z0,y,lam,H,kappa,h0,c,cH,t2,alpha,mu=s.symbols('U Z U0 Z0 y lam H kappa h0 c cH t2 alpha mu',positive=True)
le=lam+kappa*kappa/H
V=lam*(U-1)**2/4+H*(Z-h0*h0+kappa/H*(U-1))**2/4+(c*U+cH*Z)*t2/2
Ub=1-(c-kappa*cH/H)*t2/lam;Zb=h0*h0+kappa/H*(1-Ub)-cH*t2/H
Ur=(le+kappa*h0*h0-c*t2)/le
G=s.hessian(V,(U,Z))
check={
 'squared_field_convexity_determinant':G.det()-lam*H/4,
 'broken_source_stationarity':s.diff(V,U).subs({U:Ub,Z:Zb}),
 'broken_Higgs_stationarity':s.diff(V,Z).subs({U:Ub,Z:Zb}),
 'restored_Higgs_source_stationarity':s.diff(V,U).subs({U:Ur,Z:0}),
 'broken_branch_excess_potential':(V-V.subs({U:Ub,Z:Zb}))-(le*(U-Ub)**2/4+kappa*(U-Ub)*(Z-Zb)/2+H*(Z-Zb)**2/4),
 'restored_branch_excess_potential':(V-V.subs({U:Ur,Z:0}))-(le*(U-Ur)**2/4+kappa*(U-Ur)*Z/2+H*Z**2/4+s.diff(V,Z).subs({U:Ur,Z:0})*Z),
 'origin_KKT_excess':V-V.subs({U:0,Z:0})-(le*U*U/4+kappa*U*Z/2+H*Z*Z/4+s.diff(V,U).subs({U:0,Z:0})*U+s.diff(V,Z).subs({U:0,Z:0})*Z),
}
x,nu=s.symbols('x nu',real=True);f=s.cosh(x)**(-nu)
check['PT_ground_state_factorization']=(-s.diff(f,x,2)+(nu**2-nu*(nu+1)/s.cosh(x)**2)*f)/f
u,d,a,eta,R=s.symbols('u d a eta R',real=True)
Vs=le*(u*u-a*a)**2/4+mu**2*(y+alpha*u*u/mu**2)**2/2
ur,yr=s.symbols('ur yr',real=True);r=yr+alpha*ur*ur/mu**2
remainder=le*(3*ur*ur-a*a)*d*d/2+le*ur*d**3+le*d**4/4+alpha*r*d*d+mu**2*(eta+2*alpha*ur*d/mu**2+alpha*d*d/mu**2)**2/2
check['paired_action_polynomial_Taylor_remainder']=Vs.subs({u:ur+d,y:yr+eta})-Vs.subs({u:ur,y:yr})-s.diff(Vs,u).subs({u:ur,y:yr})*d-s.diff(Vs,y).subs({u:ur,y:yr})*eta-remainder
phi,hh,gg,ss,v=s.symbols('phi hh gg ss v',real=True)
raw=lam*(phi*phi-1)**2/4+mu**2*(ss+alpha*phi*phi/mu**2)**2/2+H*(hh*hh+gg*gg-h0*h0+kappa/H*(phi*phi-1))**2/4
for name,coords,prediction in [
 ('phi_phi_phi',(phi,phi,phi),6*le*phi+12*alpha**2*phi/mu**2),
 ('phi_phi_S',(phi,phi,ss),2*alpha),
 ('phi_phi_h',(phi,phi,hh),2*kappa*hh),
 ('phi_h_h',(phi,hh,hh),2*kappa*phi),
 ('h_h_h',(hh,hh,hh),6*H*hh),
 ('h_G_G',(hh,gg,gg),2*H*hh)]:
 check['cubic_'+name]=s.diff(raw,*coords).subs(gg,0)-prediction
m,q,HH,A,z=s.symbols('m q HH A z',positive=True)
g=s.sqrt(2*m*m/HH)/s.sinh(m*z+A)
check['nonlinear_restored_Higgs_tail']=s.diff(g,z,2)-m*m*g-HH*g**3
check['Robin_defect_energy_factorization']=4*(q**3-m**3)/(3*HH)-2*q*(q*q-m*m)/HH+2*(q-m)**2*(q+2*m)/(3*HH)
checks={k:bool(s.simplify(s.expand(v))==0) for k,v in check.items()};assert all(checks.values()),checks
# Exact rational model: comparisons before taking square roots.
from fractions import Fraction as Q
L=Q('0.0000176188164948');HH=Q('.13');K=Q('1e-7');h=Q('.0082');C=Q('.025');CH=Q('.4');v=Q(30000)
LE=L+K*K/HH;A=1+K*h*h/LE
TB2=v*v*(HH*h*h-K*(A-1))/(CH-K*C/LE);TCP2=v*v*(LE+K*h*h)/C
assert 0<TB2<TCP2 and C-K*CH/HH>0 and HH*LE-K*K>0
out={'identities':checks,'all_passed':True,'exact_bulk_Higgs_temperature_squared_GeV2':str(TB2),'exact_source_temperature_squared_GeV2':str(TCP2),
     'global_bulk_minimum_reason':'V after exact Gaussian elimination is a strictly convex quadratic in U=u^2,Z=h^2 on the nonnegative quadrant; KKT coefficients and positive Hessian classify its unique squared-field minimum.',
     'sympy_version':s.__version__}
root=Path(__file__).resolve().parents[1];(root/'receipts/flavor_cosmology/wall_cooling_exact.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps(out,indent=2))
