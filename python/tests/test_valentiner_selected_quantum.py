"""Independent tensor Hessian, exact supertrace and formal-elimination checks."""
import sys,json
from pathlib import Path
import numpy as np
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
from develop_valentiner_selected_quantum import selected_stabilizer,radial_symbols,radial_certificate,loop_functions,benchmark_response
from develop_valentiner_frame_selection import full_sextic_polynomial
from develop_valentiner_massless_rays import ray_profile


def test_complete_stabilizer_bounds_meet():
    result=selected_stabilizer()
    assert result['smoothness']['gradient_F6_zero_iff_triplet_zero']
    assert result['known_exact_group_order']==3*result['projective_image_order']==1080
    assert result['full_SU3_tensor_stabilizer_order']==result['selected_global_minima']==1080


def test_off_shell_mass_spectrum_against_original_tensor():
    P=full_sextic_polynomial();v=P.gens;det=s.Matrix(3,3,v).det()
    W=.1*(det+P.as_expr()+det*det)
    gradient=s.lambdify(v,[s.diff(W,z) for z in v],'numpy',cse=True)
    r0,mass,*_=loop_functions()
    basis=[]
    for i in range(3):
        E=np.zeros((3,3),complex);E[i,i]=1;basis.append(E)
    for i,j in ((0,1),(0,2),(1,2)):
        E=np.zeros((3,3),complex);E[i,j]=E[j,i]=1/np.sqrt(2);basis.append(E)
        E=np.zeros((3,3),complex);E[i,j]=1j/np.sqrt(2);E[j,i]=-1j/np.sqrt(2);basis.append(E)
    directions=[E/np.sqrt(2) for E in basis]+[1j*E/np.sqrt(2) for E in basis]
    def potential(K):
        A=K.conj().T@K;N=np.trace(A).real
        G=np.linalg.norm(A-N*np.eye(3)/3)**2
        return np.linalg.norm(gradient(*K.flatten()))**2+.0001*(N-3*r0*r0)**2+.0002*G
    for r in (r0,r0+.001):
        K=r*np.eye(3);eps=1e-5;H=np.zeros((18,18));center=potential(K)
        for i,di in enumerate(directions):
            H[i,i]=(potential(K+eps*di)+potential(K-eps*di)-2*center)/eps**2
            for j in range(i):
                dj=directions[j]
                H[i,j]=H[j,i]=(potential(K+eps*(di+dj))-potential(K+eps*(di-dj))-potential(K+eps*(-di+dj))+potential(K-eps*(di+dj)))/(4*eps**2)
        q=mass(r);expected=sorted([q[0],q[1]]+[q[2]]*8+[q[3]]*8)
        assert np.allclose(np.linalg.eigvalsh(H),expected,rtol=3e-6,atol=2e-9)


def test_exact_supersymmetric_cancellation_and_fixed_coupling_curvature():
    result=radial_certificate()
    assert result['supersymmetric_selected_potential_and_tadpole_cancel']
    assert s.sympify(result['benchmark_exact_supertrace_derivative']).is_Rational
    assert s.sympify(result['benchmark_exact_supertrace_derivative'])!=0


def test_loop_tadpole_is_derivative_and_scale_response():
    r0,mass,V1,tad,*_=loop_functions();eps=1e-7
    assert np.isclose((V1(r0+eps,.1)-V1(r0-eps,.1))/(2*eps),tad(r0,.1),rtol=2e-6)
    symbols,_,qs=radial_symbols();r,a,b,c,lam,eta,v2=symbols
    trace=sum(n*q*q for n,q in zip((1,1,8,8,-2,-16),qs))
    value=float(s.diff(trace,r).subs({r:r0,a:.1,b:.1,c:.1,lam:.0001,eta:.0002,v2:r0*r0}))
    assert np.isclose((tad(r0,.2)-tad(r0,.1))/np.log(2),-value/(32*np.pi**2),rtol=1e-10)


def test_supersymmetric_numeric_tadpole():
    r0,mass,V1,tad,*_=loop_functions(lam=0,eta=0)
    for mu in (.05,.1,.2):
        assert abs(V1(r0,mu))<1e-18 and abs(tad(r0,mu))<1e-17


def test_local_loop_continuation_and_counterterm():
    result=benchmark_response()
    r0,mass,V1,tad,tree,treeprime=loop_functions()
    for row in result['scale_scan']:
        root=row['one_loop_potential_local_stationary_radius'];mu=row['mu']
        assert abs(treeprime(root)+tad(root,mu))<1e-12
        assert abs(tad(r0,mu)-6*r0*row['delta_m2_to_retain_radius'])<1e-18
        assert abs((root-r0)-row['linear_radius_shift'])<5e-6


def test_massless_three_ray_receipt_replays():
    receipt=json.loads((ROOT/'receipts/m22_interactions/valentiner_massless_rays.json').read_text())
    for record in receipt['rays']:
        assert ray_profile(tuple(record['null_direction']))==record
        assert all(z=='0' for z in record['effective_W_coefficients'].values())
