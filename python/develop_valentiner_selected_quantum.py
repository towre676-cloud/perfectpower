"""Complete selected stabilizer and MS-bar one-loop radial audit.

The complete stabilizer is now computed from its exact line covariant. Quantum model:
nine canonical chiral fields, W=a det K+b I6bar+c(det K)^2, plus the
explicit hard scalar selector. No gauge or quark loops are included.
"""
from pathlib import Path
from functools import lru_cache
import json
import math
import numpy as np
import sympy as s
from develop_valentiner_frames import generators, group_closure, mul
from develop_valentiner_susy_vacua import source_critical_locus
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'receipts/m22_interactions/valentiner_selected_quantum.json'


def selected_stabilizer():
    smooth = source_critical_locus()
    elements, _, _ = group_closure(generators())
    zero = (0, 0, 0, 0)
    scalars = [g for g in elements if all(g[1][i] == zero for i in (1,2,3,5,6,7))
               and g[1][0] == g[1][4] == g[1][8]]
    assert len(elements) == 1080 and len(scalars) == 3
    cosets = {frozenset(mul(z, g) for z in scalars) for g in elements}
    assert len(cosets) == 360 and all(len(c) == 3 for c in cosets)
    direct=json.loads((ROOT/'receipts/m22_interactions/valentiner_direct_stabilizer.json').read_text())
    assert direct['full_45_line_factorization_verified']
    assert direct['full_projective_sextic_stabilizer_order']==360
    assert direct['full_SU3_tensor_stabilizer_order']==1080
    assert direct['classification_theorem_used'] is False
    # The exact covariant plus exhaustive projectivity filtering closes the upper bound.
    return {'smoothness': smooth, 'known_exact_group_order': len(elements),
            'projective_scalar_kernel_order': len(scalars), 'projective_image_order': len(cosets),
            'direct_projective_automorphism_upper_bound': 360,
            'direct_incidence_group_order':direct['complete_incidence_group_order'],
            'full_SU3_tensor_stabilizer_order': 1080,
            'selected_global_minima': 1080,
            'classification_theorem_used': False,
            'direct_certificate': 'receipts/m22_interactions/valentiner_direct_stabilizer.json',
            'scope': 'Complete selected global minimum set for the positive norm/Gram selector with bc>0; not a complete census of unperturbed F-flat vacua.'}


@lru_cache(None)
def radial_symbols():
    r,a,b,c,lam,eta,v2 = s.symbols('r a b c lambda eta v2', real=True)
    d = 32*b+2*c
    f = a*r**2+d*r**5
    hs = 2*a*r+5*d*r**4
    ha = -a*r+(40*b-2*c)*r**4
    common = 6*lam*(r*r-v2)
    qs = (hs*hs+f*s.diff(hs,r)+common+12*lam*r*r,
          hs*hs-f*s.diff(hs,r)+common,
          ha*ha+f*s.diff(ha,r)+common+4*eta*r*r,
          ha*ha-f*s.diff(ha,r)+common,
          hs*hs,ha*ha)
    return (r,a,b,c,lam,eta,v2),f,tuple(map(s.expand,qs))


def radial_certificate():
    symbols,f,qs = radial_symbols();r,a,b,c,lam,eta,v2 = symbols
    weights = (1,1,8,8,-2,-16)
    supertrace = s.expand(sum(n*q*q for n,q in zip(weights,qs)))
    sub = {a:-(32*b+2*c)*r**3,v2:r*r}
    selected = [s.factor(q.subs(sub)) for q in qs]
    derivative = s.factor(s.diff(supertrace,r).subs(sub))
    susy = {lam:0,eta:0}
    assert s.expand(supertrace.subs(susy).subs(sub)) == 0
    assert s.expand(derivative.subs(susy)) == 0
    # Differentiate before imposing the selected relation: a and v2 are fixed couplings.
    tree_curvature = s.factor(s.diff(3*f*f+9*lam*(r*r-v2)**2,r,2).subs(sub))
    assert s.expand(tree_curvature-6*selected[0]) == 0
    benchmark = {b:1,c:1,lam:s.Rational(1,100),eta:s.Rational(1,50)}
    exact = s.cancel(derivative.subs(benchmark)/r**3).subs(r**6,s.Rational(1,34**2))
    exact = s.factor(-exact/34)
    assert exact != 0
    return {'mass_squared_order': ['singlet_real','singlet_imaginary','adjoint_real','adjoint_imaginary','singlet_Weyl','adjoint_Weyl'],
            'supertrace_weights':list(weights), 'off_shell_mass_squared':[str(q) for q in qs],
            'selected_mass_squared':[str(q) for q in selected],
            'supertrace_M4_polynomial':str(supertrace),
            'supertrace_M4_selected_radial_derivative':str(derivative),
            'benchmark_exact_supertrace_derivative':str(exact),
            'tree_radial_curvature':str(tree_curvature),
            'supersymmetric_selected_potential_and_tadpole_cancel':True,
            'radius_shift': '-V1_prime(r0)/(6*m_singlet_real_squared)',
            'calibration_counterterm_convention':'delta V=-delta_m2*Tr(Kdagger*K); delta_m2=V1_prime(r0)/(6*r0)',
            'scale_response':'mu*d(V1_prime)/dmu=-d(Str M4)/dr/(32*pi^2)',
            'scope':'MS-bar chiral matter determinant with explicit hard scalar quartics; no gauge, quark or gravitational determinants, kinetic running or UV completion.'}


def loop_functions(a=.1,b=.1,c=.1,lam=.0001,eta=.0002):
    symbols,f,qs = radial_symbols();r,*_ = symbols
    r0=float(np.cbrt(-a/(32*b+2*c)));v2=r0*r0
    args=(a,b,c,lam,eta,v2)
    sub=dict(zip(symbols[1:],args))
    mass=s.lambdify(r,[q.subs(sub) for q in qs],'numpy')
    slope=s.lambdify(r,[s.diff(q,r).subs(sub) for q in qs],'numpy')
    tree=s.lambdify(r,(3*f*f+9*symbols[4]*(r*r-symbols[6])**2).subs(sub),'numpy')
    treeprime=s.lambdify(r,s.diff(3*f*f+9*symbols[4]*(r*r-symbols[6])**2,r).subs(sub),'numpy')
    weights=np.array((1,1,8,8,-2,-16))
    def V1(x,mu=1.):
        q=np.array(mass(x),float)
        if np.any(q<=0):raise ValueError('positive-mass local patch required')
        return float(np.sum(weights*q*q*(np.log(q/mu**2)-1.5))/(64*math.pi**2))
    def tadpole(x,mu=1.):
        q=np.array(mass(x),float);dq=np.array(slope(x),float)
        if np.any(q<=0):raise ValueError('positive-mass local patch required')
        return float(np.sum(weights*q*dq*(np.log(q/mu**2)-1))/(32*math.pi**2))
    return r0,mass,V1,tadpole,tree,treeprime


def benchmark_response():
    from scipy.optimize import brentq
    r0,mass,V1,tad,tree,treeprime=loop_functions()
    curvature=6*mass(r0)[0]
    rows=[]
    for mu in (.05,.1,.2):
        shift=-tad(r0,mu)/curvature
        root=brentq(lambda x:treeprime(x)+tad(x,mu),r0-.005,r0+.005,xtol=1e-14)
        rows.append({'mu':mu,'V1_at_tree_radius':V1(r0,mu),'radial_tadpole':tad(r0,mu),
                     'linear_radius_shift':shift,'one_loop_potential_local_stationary_radius':root,
                     'relative_linear_radius_shift':shift/r0,'delta_m2_to_retain_radius':tad(r0,mu)/(6*r0)})
    return {'parameters':{'a':.1,'b':.1,'c':.1,'lambda':.0001,'eta':.0002},'tree_radius':r0,
            'tree_mass_squared':list(map(float,mass(r0))), 'scale_scan':rows,
            'scope':'Local positive-mass stationary continuation; no assertion of global one-loop vacuum ordering or two-loop precision.'}


def build():
    return {'selected_stabilizer':selected_stabilizer(),'radial_one_loop':radial_certificate(),
            'benchmark':benchmark_response()}

if __name__=='__main__':
    OUT.write_text(json.dumps(build(),indent=2,sort_keys=True)+'\n')
    print(OUT.relative_to(ROOT))
