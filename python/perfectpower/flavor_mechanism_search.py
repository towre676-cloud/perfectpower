"""Exact restricted-algebra census and finite-channel soft-current running."""
from fractions import Fraction as F
from itertools import combinations
import numpy as np
from .exact_nonet_algebra import *

NINE_INDICES=[10,11,22,23,39,48,49,50,51]


def coordinate_subalgebra_census(table):
    support={}
    for k,i,j,c in table:
        if F(c):support.setdefault((i,j),set()).add(k)
    closed=[]
    for mask in range(1<<9):
        subset={NINE_INDICES[k] for k in range(9) if mask>>k&1}
        if all(support.get((i,j),set())<=subset for i in subset for j in subset if i<=j):closed.append(sorted(subset))
    return {'ambient_indices':NINE_INDICES,'coordinate_supports_examined':512,'closed_supports':closed,
       'scope':'Complete census of coordinate subspaces in the certified nine-operator adjoint-pair algebra; not all rotated subspaces or nonlinear RG-invariant varieties.'}


def exact_subalgebra(table,seeds,ambient=52):
    import sympy as s
    tensor={}
    for k,i,j,c in table:tensor[k,i,j]=F(c)
    def product(a,b):
        out=[s.Rational(0)]*ambient
        for (k,i,j),c in tensor.items():
            out[k]+=s.Rational(c.numerator,c.denominator)*(a[i]*b[j]+(a[j]*b[i] if i!=j else 0))
        return s.Matrix(out)
    B=s.Matrix.hstack(*(s.Matrix(x) for x in seeds));history=[]
    while True:
        cols=B.columnspace();B=s.Matrix.hstack(*cols);history.append(len(cols))
        products=[product(a,b) for i,a in enumerate(cols) for b in cols[i:]]
        new=s.Matrix.hstack(B,*products).columnspace()
        if len(new)==len(cols):return {'dimension':len(cols),'dimension_history':history,'exact_rational_basis':[list(map(str,v)) for v in cols]}
        B=s.Matrix.hstack(*new)


def current_eigenvalues(Q,D,polys):
    """Tr[(G^-1 H4)(G^-1 Hq)] on the exact finite current irreps."""
    self8=polys[11];H=hessian_polys(self8);K=[[ZERO for _ in PAIRS] for _ in PAIRS]
    for col,(i,j) in enumerate(PAIRS):
        derivatives=[(2+i,2+j,2 if i==j else 1)]
        if i!=j:derivatives.append((2+j,2+i,1))
        for a,b,n in derivatives:
            for m,c in H.get((a,b),{}).items():
                row=PAIRS.index(tuple(k-2 for k in m));K[row][col]=add(K[row][col],scale(c,F(n,METRIC[i]*METRIC[j])))
    KN,KD=integer_matrix(K);values=[]
    for P in Q[2:]:
        out=matmul(KN,P);candidate=None
        for index in np.ndindex((36,36)):
            for z in range(2):
                if P[z][index]:candidate=F(int(out[z][index]),int(P[z][index])*KD);break
            if candidate is not None:break
        assert equal(out,scaled(P,candidate*KD))
        values.append(str(candidate))
    return {'finite8_self_current_eigenvalues':values,
      'channel_order':['8prime','9','CP_pair5'],'radial_current_eigenvalue':'16',
      'exact_field_matrix_eigenidentities':True,
      'scalar_current_beta':'beta(g_uR)=(16 lambda_u+k_R kappa_u)g_uR+4 lambda_R g_dR; swap u,d for beta(g_dR)',
      'Yukawa_addition':'+12 a_u^2 g_uR, with source adjoint Yukawa a_u and three colors',
      'mass_beta':'beta(M_R^2)=4(g_uR^2+g_dR^2)',
      'normalization':'All beta coefficients multiplied by 16*pi^2; Gaussian soft-current UV class.'}


def mediation_beta(radial,anisotropy,cross,gu,gd,mass2,eigenvalues,adjoint_yukawa=(0,0)):
    radial=np.asarray(radial);anisotropy=np.asarray(anisotropy);gu=np.asarray(gu);gd=np.asarray(gd);cross=np.asarray(cross)
    k=np.array([float(F(x)) for x in eigenvalues]);a=np.asarray(adjoint_yukawa)
    bu=(16*radial[0]+k*anisotropy[0]+12*a[0]**2)*gu+4*cross*gd
    bd=(16*radial[1]+k*anisotropy[1]+12*a[1]**2)*gd+4*cross*gu
    bm=4*(gu**2+gd**2)
    exchange=-gu*gd/np.asarray(mass2)
    b_exchange=-(bu*gd+gu*bd)/mass2+gu*gd*bm/np.asarray(mass2)**2
    return {'beta_gu':bu,'beta_gd':bd,'beta_mass2':bm,'exchange':exchange,'beta_exchange':b_exchange}


def heavy_scalar_matching_certificate():
    """Massless-light-source expansion of a positive Gaussian heavy block."""
    import sympy as s
    t,M,a,d=s.symbols('t M a d',positive=True)
    light=a*t*t;H=s.Matrix([[light+d*d*t*t/M**2,d*t],[d*t,M**2]])
    large=(s.trace(H)+s.sqrt(s.trace(H)**2-4*H.det()))/2
    series=s.series(large,t,0,6).removeO().expand()
    assert s.simplify(series-(M**2+d*d*t*t/M**2+a*d*d*t**4/M**4))==0
    f=lambda z:z*z*(s.log(z/M**2)-s.Rational(3,2))
    threshold=s.series(f(series)-f(M**2),t,0,6).removeO().expand()/4
    assert s.simplify(threshold+d*d*t*t/2+a*d*d*t**4/(2*M**2))==0
    return {'exact_two_by_two_spectral_expansion':str(series),
      'general_matching_at_mu_M_16pi2':'Delta V2=-Tr(D D^T)/2; Delta V4=-Tr(D H_EFT D^T)/(2 M^2)',
      'wavefunction_16pi2':'Delta Z_a=2 sum_R g_aR^2 sum_i E_Ri^2/M_R^2 = sum_R dim(R) g_aR^2/(4 M_R^2) times I8',
      'canonical_potential':'Delta V4_canonical=Delta V4-(Delta Z x).grad(V4)/2',
      'scope':'Leading one-loop heavy-scalar matching for Gaussian soft mediation with massless light sources and expansion in fields/M; finite source masses, gauge/quark thresholds and higher powers require additional matching.'}
