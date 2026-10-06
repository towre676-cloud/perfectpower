"""Canonical single-source functional masses and their operator boundary.

Polynomial coefficients and backgrounds are explicit inputs. Neutral first-order
mass-phase protection does not imply two-loop protection or a CKM prediction.
"""
import numpy as np


def _hermitian(C):
    C=np.asarray(C,complex)
    if C.ndim!=2 or C.shape[0]!=C.shape[1] or not np.all(np.isfinite(C)) or np.max(abs(C-C.conj().T))>1e-10*max(1,np.linalg.norm(C)):
        raise ValueError('Finite Hermitian square source required')
    return (C+C.conj().T)/2


def matrix_polynomial(C,coefficients):
    C=_hermitian(C);p=np.zeros_like(C);I=np.eye(len(C))
    coefficients=np.asarray(coefficients,float)
    if coefficients.ndim!=1 or not len(coefficients) or not np.all(np.isfinite(coefficients)):
        raise ValueError('Finite nonempty real coefficient vector required')
    for a in coefficients[::-1]:p=p@C+a*I
    return (p+p.conj().T)/2


def polynomial_variation(C,H,coefficients):
    """Exact Frechet derivative, including repeated source eigenvalues."""
    C,H=_hermitian(C),_hermitian(H)
    if C.shape!=H.shape:raise ValueError('Matching source and variation required')
    matrix_polynomial(C,coefficients) # validates real polynomial
    powers=[np.eye(len(C),dtype=complex)]
    for _ in range(len(coefficients)-1):powers.append(powers[-1]@C)
    out=np.zeros_like(C)
    for k,a in enumerate(coefficients[1:],1):
        for j in range(k):out+=a*powers[j]@H@powers[k-1-j]
    return (out+out.conj().T)/2


def functional_spectrum(C,a,coefficients):
    """Full real two-state blocks, with positive heavy mass function."""
    C=_hermitian(C);M=matrix_polynomial(C,coefficients);n=len(C)
    if not np.isfinite(a) or a<=0 or min(np.linalg.eigvalsh(M))<=0:raise ValueError('Positive Higgs mass and heavy mass function required')
    h,U=np.linalg.eigh(C);m=np.polynomial.polynomial.polyval(h,coefficients)
    D=np.block([[a*np.eye(n),np.zeros((n,n))],[C,M]])
    masses=[];left=[];right=[];family=[]
    for i,(x,b) in enumerate(zip(h,m)):
        L,s,Rh=np.linalg.svd([[a,0.],[x,b]]);s[1]=a*b/s[0]
        for j in range(2):
            masses.append(s[j]);left.append(np.r_[L[0,j]*U[:,i],L[1,j]*U[:,i]]);right.append(np.r_[Rh[j,0]*U[:,i],Rh[j,1]*U[:,i]]);family.append(i)
    order=np.argsort(masses);L=np.column_stack(left)[:,order];R=np.column_stack(right)[:,order]
    return {'mass_matrix':D,'masses':np.asarray(masses)[order],'left':L,'right':R,'family_labels':np.asarray(family)[order],
            'source_eigenvalues':h,'heavy_mass_eigenvalues':m,'doublet_frame':L[:n,:n], 'source_eigenvectors':U}


def functional_vertices(C,variations,coefficients,higgs_derivative=1.):
    C=_hermitian(C);n=len(C);H=[_hermitian(v) for v in variations];G=np.zeros((len(H)+1,2*n,2*n),complex)
    for i,v in enumerate(H):
        G[i,n:,:n]=v;G[i,n:,n:]=polynomial_variation(C,v,coefficients)
    G[-1,:n,:n]=higgs_derivative*np.eye(n)
    return G


def positive_quartic_certificate():
    """Exact rational interval checks, not calibrated measured quark masses."""
    import sympy as s
    lam=s.symbols('lambda');a=s.Integer(1);h=[-10,-20,30];delta=s.Rational(1,1000);k=s.Rational(1,100000);r=s.Integer(100)
    coefficients=[delta+k*r*r,0,-2*k*r,0,k]
    intervals=[(s.Rational(9,100000),s.Rational(1,10000)),(s.Rational(44,1000),s.Rational(46,1000)),(s.Rational(208,1000),s.Rational(210,1000))]
    rows=[]
    for x,(lo,hi) in zip(h,intervals):
        m=delta+k*(x*x-r)**2;p=lam**2-(a*a+x*x+m*m)*lam+a*a*m*m
        # hi^2 < trace/2 places the sign-changing root on the light branch.
        assert p.subs(lam,lo*lo)>0 and p.subs(lam,hi*hi)<0 and hi*hi<(a*a+x*x+m*m)/2
        assert a*a+x*x+m*m-hi*hi>100 # heavy branch from trace minus light root
        rows.append({'source_eigenvalue':str(x),'heavy_mass_entry':str(m),'light_mass_interval':[str(lo),str(hi)],'characteristic_polynomial':str(p),'heavy_mass_strictly_above':10})
    assert sum(h)==0
    return {'source_trace':'0','positive_mass_function':'1/1000 + (C**2 - 100*I)**2/100000',
            'polynomial_coefficients':[str(v) for v in coefficients],'source_degree':4,'fermion_operator_dimension':7,'rows':rows,
            'strict_light_mass_ratio_lower_bounds':['440','104/23'],'exactly_three_states_below':1,'exactly_three_states_above':10,
            'scope':'Constructive hierarchy with explicit source and coefficient inputs; no measured mass or mixing prediction.'}


def charge_and_operator_certificate():
    """Specified singlet/adjoint source content, diagonal shaping Z2 factors."""
    import sympy as s
    q,u,h,c=s.symbols('q u h c')
    # Charges of coefficients in additive notation. Constant heavy mass sets
    # U_R=U_L=u; Higgs-to-q_R fixes Q_L=q+h. Source mass forces c=0,
    # source mixing then q=u, so the unwanted Higgs-to-U_R has charge zero.
    assert s.expand((u-q+c)-(u-u+c))==u-q
    contractions=['eta**2 I','s**2 I','eta*s I','Tr(A**2) I','eta*A','s*A','A**2-Tr(A**2)*I/3']
    return {'linear_source_heavy_mass_forbidden_by_existing_Z2':True,
            'ordinary_phase_charge_implication':'constant heavy mass + Higgs ordinary Yukawa + same-source mixing + same-source heavy Yukawa imply Higgs-heavy Yukawa allowed',
            'quadratic_source_decomposition':'2 singlets plus one ordinary 8: singlet multiplicity 4, ordinary 8 multiplicity 3',
            'single_source_contractions':contractions,'quadratic_heavy_mass_contractions_per_quark_sector':14,'two_sector_total':28,'sufficient_linear_protected_slice_dimension':22,'excluded_opposite_adjoint_coefficients':6,
            'reason_for_doubling':'Either same-sector quadratic or opposite-sector quadratic is even under both shaping signs. Mixed up-down degree-two products are forbidden.',
            'included_fields':'The two original source singlets eta,s and one ordinary adjoint A per sector; one heavy triplet bilinear. No mediator fields or higher operators counted.',
            'same_source_scope':'At this degree the same-source heavy mass commutes with C=z I+g A; all adjoint off-diagonal derivatives have a real common divided-difference factor.',
            'allowed_cross_operator':'bar(U_up,L) [A_down**2 - Tr(A_down**2)*I/3] U_up,R / Lambda + h.c.'}


def wrong_source_example():
    from .flavor_quantum import scalar_threshold
    C=np.diag([.4,.7,1.1]);B=np.array([[.2,.13j,.1],[-.13j,.5,.17],[.1,.17,-.7]])
    A=np.array([[0,1,0],[1,0,0],[0,0,0]],complex);T=np.diag([1.,-1.,0.]);epsilon=.07
    M=np.eye(3)+epsilon*B@B;D=np.block([[.2*np.eye(3),np.zeros((3,3))],[C,M]])
    G=np.zeros((3,6,6),complex);G[0,:3,:3]=.2*np.eye(3);G[1,3:,:3]=.3*A;G[2,3:,3:]=epsilon*(B@T+T@B)
    H=np.array([[.8,.1,.03],[.1,.9,.2],[.03,.2,1.4]])
    result=scalar_threshold(D,G,H)
    commutator=C@M-M@C
    return {'first_order_neutral_scalar_phase':result['delta_theta'],'UV_phase_coefficient':result['UV_phase_coefficient'],
            'maximum_imaginary_vertex_pair':float(np.max(abs((result['mass_basis_vertices']*result['mass_basis_vertices'].swapaxes(1,2)).imag))),
            'relative_correction_norm':result['relative_correction_norm'],'tree_determinant_phase':float(np.angle(np.linalg.det(D))),
            'heavy_mass_minimum_eigenvalue':float(min(np.linalg.eigvalsh(M))),'source_mass_commutator_norm':float(np.linalg.norm(commutator)),
            'source_CP_cycle':float(np.imag(B[0,1]*B[1,2]*B[2,0])),
            'scalar_eigenvalues':result['scalar_masses_squared'].tolist(),
            'scope':'Positive finite spectral counterexample for a permitted wrong-source operator and real scalar mixing; not a solved complete invariant scalar vacuum or all-diagram theta calculation.'}


def exact_wrong_source_resolvent_certificate():
    import sympy as s
    f=s.Rational;C=s.diag(f(2,5),f(7,10),f(11,10));B=s.Matrix([[f(1,5),f(13,100)*s.I,f(1,10)],[-f(13,100)*s.I,f(1,2),f(17,100)],[f(1,10),f(17,100),-f(7,10)]])
    A=s.Matrix([[0,1,0],[1,0,0],[0,0,0]]);T=s.diag(1,-1,0);e=f(7,100);zero=s.zeros(3);I=s.eye(3)
    D=(f(1,5)*I).row_join(zero).col_join(C.row_join(I+e*B*B));G=[s.zeros(6) for _ in range(3)]
    G[0][:3,:3]=f(1,5)*I;G[1][3:,:3]=f(3,10)*A;G[2][3:,3:]=e*(B*T+T*B)
    O=s.Matrix([[1,2,2],[2,1,-2],[2,-2,1]])/3;assert O.T*O==s.eye(3)
    correction=s.zeros(6)
    for b,t in enumerate([f(3,10),f(4,5),f(7,5)]):
        V=sum((O[j,b]*G[j] for j in range(3)),s.zeros(6))
        correction-=V*D.H*(D*D.H+t*s.eye(6)).inv()*V
    phase=s.simplify(s.im(s.trace(D.inv()*correction)));assert phase!=0
    return {'rational_resolvent_first_order_phase_without_loop_prefactor':str(phase),
            'nonzero_exactly':True,'tree_determinant_positive':bool(s.det(D)>0),
            'scope':'Exact real resolvent-kernel termwise-protection counterexample; the physical B0 threshold is computed separately.'}


def polynomial_second_variation(C,H,K,coefficients):
    """Mixed second derivative; scalar seagull vertices remain Hermitian."""
    C,H,K=_hermitian(C),_hermitian(H),_hermitian(K)
    if C.shape!=H.shape or C.shape!=K.shape:raise ValueError('Matching source and variations required')
    matrix_polynomial(C,coefficients);n=len(C);out=np.zeros_like(C)
    for degree,a in enumerate(coefficients):
        for i in range(degree):
            for j in range(i+1,degree):
                for first,second in [(H,K),(K,H)]:
                    term=np.eye(n,dtype=complex)
                    for position in range(degree):term=term@(first if position==i else second if position==j else C)
                    out+=a*term
    return (out+out.conj().T)/2


def orientation_response(weights_up,weights_down):
    """Four CKM directions at fixed complete spectra in the functional slice."""
    u,d=np.asarray(weights_up,float),np.asarray(weights_down,float)
    def observables(t):
        t12,t23,t13,delta=t;c12,c23,c13=np.cos([t12,t23,t13]);s12,s23,s13=np.sin([t12,t23,t13]);phase=np.exp(1j*delta)
        W=np.array([[c12*c13,s12*c13,s13/phase],[-s12*c23-c12*s23*s13*phase,c12*c23-s12*s23*s13*phase,s23*c13],
                    [s12*s23-c12*c23*s13*phase,-c12*s23-s12*c23*s13*phase,c23*c13]])
        V=u[:,None]*W*d[None,:]
        return np.array([abs(V[0,1]),abs(V[1,2]),abs(V[0,2]),np.imag(V[0,0]*V[1,1]*V[0,1].conjugate()*V[1,0].conjugate())])
    t=np.array([.22,.04,.0035,1.15]);step=1e-6;J=np.column_stack([(observables(t+step*np.eye(4)[i])-observables(t-step*np.eye(4)[i]))/(2*step) for i in range(4)])
    return {'benchmark_parameters':t.tolist(),'observables':observables(t).tolist(),'Jacobian':J.tolist(),'Jacobian_rank':int(np.linalg.matrix_rank(J)),
            'Jacobian_determinant':float(np.linalg.det(J)),'scope':'Relative source eigenframes vary; all six fermion masses in each sector and their doublet weights remain fixed. This is freedom, not a scalar-vacuum or CKM prediction.'}


def exact_quadratic_source_multiplicities():
    from fractions import Fraction as F
    from develop_valentiner_frames import group_closure,generators,mul,product,conjugate
    from develop_valentiner_invariants import Z,O,add,sub,scale,exact_integer
    group=group_closure(generators())[0];total=[Z,Z]
    def trace(g):return tuple(sum(F(g[1][3*i+i][j],g[0]) for i in range(3)) for j in range(4))
    for g in group:
        t,t2=trace(g),trace(mul(g,g));chi=sub(product(t,conjugate(t)),O);chi2=sub(product(t2,conjugate(t2)),O)
        v=add(chi,scale(O,2));v2=add(chi2,scale(O,2));square=scale(add(product(v,v),v2),F(1,2))
        total[0]=add(total[0],square);total[1]=add(total[1],product(square,chi))
    result=[exact_integer(scale(t,F(1,len(group)))) for t in total];assert result==[4,3]
    return {'group_order':len(group),'exact_singlet_multiplicity':result[0],'exact_ordinary_adjoint_multiplicity':result[1],
            'CP_even_witness':'All seven independent displayed matrix contractions are CP covariant with real coefficients, saturating the unitary count.'}


def exact_cross_source_running_tensor():
    """Exact scalar-loop mixing in the declared ordinary-channel normalization.

    Vcross=lambda Tr(q(Au)q(Ad)), q(A)=A^2-Tr(A^2)I/3.
    An insertion kappa bar(U_L)Au^2 U_R/Lambda induces
    16pi^2 beta(kappa_cross)=10 kappa lambda/3 for q(Ad).
    Only this scalar-loop contribution is computed, not complete EFT running.
    """
    import sympy as s
    B=[]
    for i in range(3):
        for j in range(i+1,3):
            r=s.zeros(3);r[i,j]=r[j,i]=1;B.append(r)
            r=s.zeros(3);r[i,j]=s.I;r[j,i]=-s.I;B.append(r)
    B.extend([s.diag(1,-1,0),s.diag(1,1,-2)]);metric=[s.trace(b*b) for b in B]
    x=s.symbols('x0:9',real=True);X=s.Matrix([[x[0],x[3]+s.I*x[4],x[5]+s.I*x[6]],[x[3]-s.I*x[4],x[1],x[7]+s.I*x[8]],[x[5]-s.I*x[6],x[7]-s.I*x[8],x[2]]])
    result=s.zeros(3)
    for i,a in enumerate(B):
        for j,b in enumerate(B):
            T=a*b+b*a;result+=T*s.trace(T*X)/(metric[i]*metric[j])
    expected=s.Rational(10,3)*X+s.Rational(22,9)*s.trace(X)*s.eye(3)
    assert all(s.expand(v)==0 for v in result-expected)
    return {'exact_general_Hermitian_tensor_identity':True,'tensor_map':'S(X) = (10/3) X + (22/9) Tr(X) I',
            'traceless_channel_eigenvalue':'10/3','singlet_channel_eigenvalue':'32/3','basis_norms':[str(g) for g in metric],
            'ordinary_portal_definition':'lambda Tr[(Au**2-Tr(Au**2)I/3)(Ad**2-Tr(Ad**2)I/3)]',
            'same_source_dimension5_insertion':'kappa bar(U_up,L) Au**2 U_up,R / Lambda + h.c.',
            'induced_wrong_source_dimension5_insertion':'kappa_cross bar(U_up,L) [Ad**2-Tr(Ad**2)I/3] U_up,R / Lambda + h.c.',
            'scalar_loop_beta_times_16pi_squared':'10*kappa*lambda/3',
            'derivation':'Cross term of beta V=(1/32 pi^2)Tr[(H_V+H_insertion)^2] on the canonical eight real Au coordinates; external fermion bilinear treated as a single insertion.',
            'scope':'Exact one-loop scalar mixing tensor, not the complete dimension5 anomalous dimension including fermion and gauge diagrams.'}


def high_precision_wrong_source_phase(digits=80):
    """Independent direct weak-basis B0 trace, without the numpy Dirac SVD."""
    import mpmath as mp
    with mp.workdps(digits):
        f=lambda v:mp.mpf(str(v));I=mp.eye(3);Z=mp.zeros(3);e=f('.07');a=f('.2')
        C=mp.diag([f('.4'),f('.7'),f('1.1')]);B=mp.matrix([[f('.2'),f('.13')*1j,f('.1')],[-f('.13')*1j,f('.5'),f('.17')],[f('.1'),f('.17'),-f('.7')]])
        A=mp.matrix([[0,1,0],[1,0,0],[0,0,0]]);T=mp.diag([1,-1,0]);M=I+e*B*B;D=mp.zeros(6);G=[mp.zeros(6) for _ in range(3)]
        for i in range(3):
            for j in range(3):
                D[i,j]=a*I[i,j];D[i+3,j]=C[i,j];D[i+3,j+3]=M[i,j]
                G[0][i,j]=a*I[i,j];G[1][i+3,j]=f('.3')*A[i,j];G[2][i+3,j+3]=e*(B*T+T*B)[i,j]
        H=mp.matrix([[f('.8'),f('.1'),f('.03')],[f('.1'),f('.9'),f('.2')],[f('.03'),f('.2'),f('1.4')]])
        scalar,O=mp.eighe(H);fermion2,U=mp.eighe(D*D.H);correction=mp.zeros(6)
        for k,t in enumerate(scalar):
            V=sum((O[j,k]*G[j] for j in range(3)),mp.zeros(6))
            weights=[1-(x*mp.log(x)-t*mp.log(t))/(x-t) for x in fermion2]
            correction-=V*D.H*U*mp.diag(weights)*U.H*V/(16*mp.pi**2)
        trace=D**-1*correction;phase=mp.im(sum(trace[i,i] for i in range(6)))
        return {'decimal_digits':digits,'first_order_B0_phase':mp.nstr(phase,65),'method':'Direct Hermitian DDdagger functional calculus in the weak basis; no numpy Dirac SVD.'}
