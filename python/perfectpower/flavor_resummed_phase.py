"""Higher determinant terms of a neutral-scalar one-loop mass correction.

Resumming one-loop matrices does not calculate genuine two-loop diagrams.
Exact resolvent examples establish structural statements; the actual B0
counterexample is separately checked at high precision.
"""
import numpy as np
from .flavor_quantum import scalar_threshold


def spectral_phase_example(structured=False):
    C=np.diag([.4,.7,1.1]);D=np.block([[.1*np.eye(3),np.zeros((3,3))],[C,np.eye(3)]])
    if structured:
        G=np.zeros((4,6,6),complex);G[0,:3,:3]=.2*np.eye(3);G[1,3:,:3]=2*C
        G[2,3,1]=G[2,4,0]=2;G[3,3,1]=2j;G[3,4,0]=-2j
        H=np.array([[.3,.2,0,0],[.2,.8,.3,.3],[0,.3,1.2,.4],[0,.3,.4,1.7]])
    else:
        G=np.zeros((3,6,6),complex);G[0,:3,:3]=.2*np.eye(3)
        G[1,3,1]=G[1,4,0]=.2;G[2,3,1]=.2j;G[2,4,0]=-.2j
        O=np.array([[1,2,2],[2,1,-2],[2,-2,1]])/3;H=O@np.diag([.3,.8,1.4])@O.T
    p=scalar_threshold(D,G,H);X=p['mass_basis_correction']/p['fermion_masses'][:,None]
    rows=[]
    for t in [.1,.2,.5,1.]:
        rows.append({'formal_loop_multiplier':t,'determinant_phase':float(np.angle(np.linalg.slogdet(np.diag(p['fermion_masses'])+t*p['mass_basis_correction'])[0]))})
    return {'D':D,'vertices':G,'scalar_Hessian':H,'first_order_phase':p['delta_theta'],
      'quadratic_determinant_phase':float(-np.trace(X@X).imag/2),
      'resummed_phase':p['resummed_one_loop_matrix_phase'],'relative_correction_norm':p['relative_correction_norm'],
      'positive_scalar_eigenvalues':p['scalar_masses_squared'].tolist(),'formal_scaling':rows,
      'scope':'Positive scalar spectral counterexample to extending first-order phase protection to a resummed one-loop matrix. Structured example couples the Higgs only to a diagonal source at the Hessian level. Neither example supplies a complete invariant vacuum or genuine two-loop matching.'}


def exact_resolvent_phase_certificate():
    import sympy as s
    O=s.Matrix([[1,2,2],[2,1,-2],[2,-2,1]])/3;assert O*O.T==s.eye(3)
    C=s.diag(s.Rational(2,5),s.Rational(7,10),s.Rational(11,10));a=s.Rational(1,10);b=g=s.Rational(1,5)
    T=s.zeros(3);T[0,1]=T[1,0]=1;U=s.zeros(3);U[0,1]=s.I;U[1,0]=-s.I;B=s.zeros(3)
    for j,mass2 in enumerate([s.Rational(3,10),s.Rational(4,5),s.Rational(7,5)]):
        L=s.diag(*[a*(1+mass2)/((a*a+mass2)*(1+mass2)+mass2*h*h) for h in C.diagonal()])
        K=s.diag(*[mass2*h/((a*a+mass2)*(1+mass2)+mass2*h*h) for h in C.diagonal()])
        vertex=g*(O[1,j]*T+O[2,j]*U);bj=b*O[0,j];B+=bj*bj*L+bj*K*vertex
    linear=s.im(s.trace(B/a));quadratic=s.factor(-s.im(s.trace(B*B))/(2*a*a));assert linear==0 and quadratic!=0
    e=s.symbols('e',real=True);det=s.expand((a*s.eye(3)-e*B).det()/a**3)
    assert s.im(det.coeff(e,1))==0;assert s.im(det.coeff(e,2))==quadratic
    return {'orthogonal_scalar_mixing':[[str(x) for x in row] for row in O.tolist()],
      'resolvent_first_order_phase':str(linear),'resolvent_quadratic_phase_coefficient':str(quadratic),
      'exact_resolvent_kernel':'D^dagger (D D^dagger+s I)^(-1): upper blocks L=a(M^2+s)/den, K=s C/den, den=(a^2+s)(M^2+s)+s C^2',
      'counterterm_top_block':'sum_alpha [b_alpha^2 L_alpha(C)+b_alpha K_alpha(C) H_alpha]',
      'scope':'Exact rational spectral-kernel counterexample, not the physical B0 integral. Physical finite B0 is evaluated independently.'}


def high_precision_B0_top_block(digits=80):
    import mpmath as mp
    with mp.workdps(digits):
        a=mp.mpf(1)/10;b=g=mp.mpf(1)/5;hs=[mp.mpf(2)/5,mp.mpf(7)/10,mp.mpf(11)/10]
        O=mp.matrix([[1,2,2],[2,1,-2],[2,-2,1]])/3;T=mp.matrix(3);T[0,1]=T[1,0]=1;U=mp.matrix(3);U[0,1]=1j;U[1,0]=-1j;B=mp.matrix(3)
        for j,ss in enumerate([mp.mpf(3)/10,mp.mpf(4)/5,mp.mpf(7)/5]):
            L=[];K=[]
            for h in hs:
                trace=a*a+h*h+1;gap=mp.sqrt(trace*trace-4*a*a);lo=2*a*a/(trace+gap);hi=(trace+gap)/2
                def f(x):return 1-(x*mp.log(x)-ss*mp.log(ss))/(x-ss)
                slope=(f(hi)-f(lo))/(hi-lo);F11=f(lo)+slope*(a*a-lo);F12=slope*a*h;F22=f(lo)+slope*(h*h+1-lo)
                L.append(a*F11+h*F12);K.append(a*F12+h*F22)
            vertex=g*(O[1,j]*T+O[2,j]*U);bj=b*O[0,j]
            B+=bj*bj*mp.diag(L)+bj*mp.diag(K)*vertex
        X=-B/(a*16*mp.pi**2);quadratic=-sum((X*X)[i,i] for i in range(3)).imag/2
        phase=mp.arg(mp.det(mp.eye(3)+X));linear=sum(X[i,i] for i in range(3)).imag
        return {'precision_digits':digits,'first_order_phase':mp.nstr(linear,60),
          'quadratic_determinant_phase':mp.nstr(quadratic,60),'resummed_phase':mp.nstr(phase,60),
          'scope':'Direct high-precision divided-difference spectral evaluation of the physical finite B0 top block; no SVD phase subtraction.'}


def Higgs_sequestering_certificate():
    import sympy as s
    y,e,t,a,eta,ss,N,h=s.symbols('y e t a eta ss N h',real=True)
    traceC2=3*(e*eta+t*ss)**2+a*a*N;portal=s.expand(-12*y*y*h*traceC2)
    coeff=[s.expand(portal).coeff(h).coeff(eta,2),s.expand(portal).coeff(h).coeff(ss,2),s.expand(portal).coeff(h).coeff(eta).coeff(ss),s.expand(portal).coeff(h).coeff(N)]
    assert coeff==[-36*y*y*e*e,-36*y*y*t*t,-72*y*y*e*t,-12*y*y*a*a]
    return {'source_Higgs_portal_beta_at_zero_portals':[str(x) for x in coeff],
      'order':['eta^2','s^2','eta*s','adjoint_norm'],
      'normalization':'16*pi^2 coefficients, H^dagger H multiplying source quadratics',
      'closed_zero_portal_condition':'For each real sector: y=0 or all three source Yukawa coefficients e=t=a=0',
      'sequestered_resummed_theorem':'If no scalar mass eigenmode has both Higgs and source vertices, the corrected top mass block is a Hermitian function of C. Its determinant ratio is positive when the correction norm is below one.',
      'scope':'Zero portals and arbitrary source quartics: Higgs and source scalar sectors have no shared scalar-loop product. Fermion boxes alone necessarily generate the displayed portals for nonzero Higgs and source Yukawas. Additional fields or interactions can change this result.'}
