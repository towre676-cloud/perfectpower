"""Complete CP-even renormalizable potential for two shaped real nonets.

Each sector has eta, the nonet trace coordinate s, and a real adjoint a[8].
Both eta and the whole nonet are odd under that sector's independent Z2.
The retained family symmetry is 3.A6 with its certified generalized CP.
Projector tensors are evaluated numerically in the declared Hermitian basis.
"""
import numpy as np
from valentiner_adjoint_quartics import BASIS,EMBED

D_TENSOR=np.einsum('aij,bjk,cki->abc',BASIS,BASIS,BASIS).real
D_TENSOR=(D_TENSOR+np.swapaxes(D_TENSOR,1,2))/2
QUADRATIC_NAMES=['eta2','s2','eta_s','adjoint_norm']
SELF_NAMES=['eta4','eta3_s','eta2_s2','eta_s3','s4','eta2_norm','eta_s_norm',
            's2_norm','eta_traceA3','s_traceA3','norm2','finite8_self']
MIXED_NAMES=([f'{a}_up__{b}_down' for a in QUADRATIC_NAMES for b in QUADRATIC_NAMES]
             +[f'{a}_up_dot_{b}_down' for a in ['eta_A','s_A','A2_8'] for b in ['eta_A','s_A','A2_8']]
             +['finite8_cross','finite9_cross','CP_pair5_cross'])
OPERATOR_NAMES=([f'{n}_up' for n in QUADRATIC_NAMES]+[f'{n}_down' for n in QUADRATIC_NAMES]
                +[f'{n}_up' for n in SELF_NAMES]+[f'{n}_down' for n in SELF_NAMES]+MIXED_NAMES)


def sector_features(x,projectors):
    eta,s=x[:2];a=x[2:];N=a@a;A2=np.einsum('ijk,j,k->i',D_TENSOR,a,a);T3=a@A2
    q=np.array([eta*eta,s*s,eta*s,N]);dq=np.zeros((4,10))
    dq[0,0]=2*eta;dq[1,1]=2*s;dq[2,:2]=[s,eta];dq[3,2:]=2*a
    cov=np.array([eta*a,s*a,A2]);dc=np.zeros((3,8,10))
    dc[0,:,0]=a;dc[0,:,2:]=eta*np.eye(8);dc[1,:,1]=a;dc[1,:,2:]=s*np.eye(8)
    dc[2,:,2:]=2*np.einsum('ijk,k->ij',D_TENSOR,a)
    w=np.einsum('aij,i,j->a',EMBED,a,a);dw=2*np.einsum('aij,j->ai',EMBED,a)
    finite=w@projectors[2]@w
    values=np.array([eta**4,eta**3*s,eta*eta*s*s,eta*s**3,s**4,eta*eta*N,eta*s*N,
                     s*s*N,eta*T3,s*T3,N*N,finite])
    grad=np.zeros((12,10));grad[:5,:2]=[[4*eta**3,0],[3*eta*eta*s,eta**3],
                    [2*eta*s*s,2*s*eta*eta],[s**3,3*eta*s*s],[0,4*s**3]]
    grad[5,0]=2*eta*N;grad[5,2:]=2*eta*eta*a
    grad[6,:2]=[s*N,eta*N];grad[6,2:]=2*eta*s*a
    grad[7,1]=2*s*N;grad[7,2:]=2*s*s*a
    grad[8,0]=T3;grad[8,2:]=3*eta*A2
    grad[9,1]=T3;grad[9,2:]=3*s*A2
    grad[10,2:]=4*N*a;grad[11,2:]=2*dw.T@projectors[2]@w
    return q,dq,cov,dc,w,dw,values,grad


def operators(x,projectors):
    x=np.asarray(x,float)
    if x.shape!=(20,) or not np.all(np.isfinite(x)):raise ValueError('Twenty finite real scalar coordinates required')
    up,down=[sector_features(v,projectors) for v in [x[:10],x[10:]]]
    uq,udq,uc,udc,uw,udw,uv,udv=up;dq,ddq,dc,ddc,dw,ddw,dv,ddv=down
    values=list(uq)+list(dq)+list(uv)+list(dv);gradient=np.zeros((60,20))
    gradient[:4,:10]=udq;gradient[4:8,10:]=ddq;gradient[8:20,:10]=udv;gradient[20:32,10:]=ddv
    k=32
    for i in range(4):
        for j in range(4):
            values.append(uq[i]*dq[j]);gradient[k,:10]=udq[i]*dq[j];gradient[k,10:]=ddq[j]*uq[i];k+=1
    for i in range(3):
        for j in range(3):
            values.append(uc[i]@dc[j]);gradient[k,:10]=udc[i].T@dc[j];gradient[k,10:]=ddc[j].T@uc[i];k+=1
    for P in projectors[2:]:
        values.append(uw@P@dw);gradient[k,2:10]=udw.T@P@dw;gradient[k,12:]=ddw.T@P.T@uw;k+=1
    assert k==60
    return np.array(values),gradient


def potential(x,coefficients,projectors):
    values,gradient=operators(x,projectors);c=np.asarray(coefficients,float)
    if c.shape!=(60,):raise ValueError('Sixty real coefficients required')
    return float(values@c),gradient.T@c


def bounded_coefficients(seed=20261006):
    """All sixty coefficients nonzero, with a global quartic lower bound.

    No CKM magnitude, CP phase or golden coefficient is an input.
    The dominant six radial quartics bound total norm^4/6. Every other
    normalized displayed quartic has magnitude at most total norm^4.
    """
    rng=np.random.default_rng(seed);c=rng.uniform(-.0007,.0007,60)
    c[:8]=[-2.,-.8,.027,-2.,-1.8,-.7,-.019,-2.1]
    for start in [8,20]:
        c[start+0]=1.;c[start+4]=1.;c[start+10]=1.;c[start+11]=-.025
    c[-3:]=rng.choice([-1.,1.],3)*np.array([.014,.021,.017])
    dominant={8,12,18,20,24,30};remainder=sum(abs(c[i]) for i in range(8,60) if i not in dominant)
    lower=1/6-remainder
    assert lower>0 and np.all(c!=0)
    return c,{'quartic_total_norm_lower_bound':float(lower),'all_sixty_coefficients_nonzero':True,
              'proof':'Six positive radial quartics >= total norm^4/6; triangle bound on all remaining normalized quartics.',
              'uses_CKM_or_golden_targets':False}


def search_coefficients(index):
    """Declared reproducible bounded search family, independent of CKM targets."""
    c,_=bounded_coefficients(20261006+index);rng=np.random.default_rng(501+index)
    c[8:]=rng.uniform(-.002,.002,52)
    for start in [8,20]:c[start]=c[start+4]=c[start+10]=1.
    c[-3:]=rng.uniform(-.05,.05,3)
    other=[i for i in range(8,60) if i not in {8,12,18,20,24,30}]
    c[other]*=.12/sum(abs(c[i]) for i in other)
    return c,rng


def joint_higgs(z,c,projectors,portals,mu2,lam=.13):
    """Neutral canonical Higgs coordinate h=sqrt(2)*vev; HdaggerH=h²/2."""
    x=z[:20];h=z[20];q,g=operators(x,projectors);v,dv=potential(x,c,projectors)
    h2=h*h/2;portal=q[:8]@portals
    return v-mu2*h2+lam*h2*h2+h2*portal,np.r_[dv+h2*g[:8].T@portals,h*(-mu2+2*lam*h2+portal)]


def numerical_hessian(x,coefficients,projectors,step=.01):
    n=len(x);H=np.empty((n,n))
    for j in range(n):
        h=step*max(1,abs(x[j]));e=np.zeros(n);e[j]=h
        coarse=(potential(x+e,coefficients,projectors)[1]-potential(x-e,coefficients,projectors)[1])/(2*h)
        fine=(potential(x+e/2,coefficients,projectors)[1]-potential(x-e/2,coefficients,projectors)[1])/h
        H[:,j]=(4*fine-coarse)/3
    return (H+H.T)/2


def nonet_fields(x):
    return [(float(v[0]),float(v[1]),np.einsum('i,ijk->jk',v[2:],BASIS)) for v in [x[:10],x[10:]]]


def exact_operator_census():
    """Character averages in Q(sqrt(5),omega), without fitted tensors."""
    from fractions import Fraction as F
    from develop_valentiner_frames import group_closure,generators,mul,product,conjugate
    from develop_valentiner_invariants import Z,O,add,sub,scale,exact_integer
    group=group_closure(generators())[0];totals=[Z,Z,Z,Z]
    for g in group:
        powers=[];p=g
        for k in range(1,5):
            tr=tuple(sum(F(p[1][3*i+i][j],p[0]) for i in range(3)) for j in range(4))
            powers.append(sub(product(tr,conjugate(tr)),O));p=mul(p,g)
        def symmetric(chars,n):
            h=[O]
            for degree in range(1,n+1):
                h.append(scale(sum_fields([product(chars[k-1],h[degree-k]) for k in range(1,degree+1)]),F(1,degree)))
            return h[n]
        def sum_fields(items):
            out=Z
            for item in items:out=add(out,item)
            return out
        v=[add(t,scale(O,2)) for t in powers]
        q=symmetric(v,2)
        vals=[q,symmetric(v,4),product(q,q),symmetric(powers,4)]
        totals=[add(t,scale(value,F(1,len(group)))) for t,value in zip(totals,vals)]
    dims=[exact_integer(v) for v in totals]
    assert dims==[4,12,29,2],dims
    return {'group_order':len(group),'single_sector_quadratics':dims[0],
            'single_sector_quartics':dims[1],'mixed_quartics_before_CP':dims[2],
            'pure_adjoint_self_quartics':dims[3],'mixed_CP_even_quartics':28,
            'mixed_CP_odd_quartics':1,'scalar_coefficients_without_Higgs':60,
            'scalar_coefficients_with_Higgs':70,
            'CP_reduction':'CP exchanges the inequivalent 5 and 5-prime channels; their difference is odd. The displayed 28 operators are even and independent.',
            'scope':'Two real (8+1+1) sectors with independent odd Z2 charges, diagonal 3.A6, and the declared generalized CP. Excludes higher-degree and derivative operators.'}
