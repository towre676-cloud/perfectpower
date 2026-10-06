"""Complete renormalizable scalar sector of the declared adjoint mediator.

The source/link self-potentials are the specified higher-degree breaking EFT.
Bare quark kinetic terms are canonical; heavy tree matching is exact.
"""
import numpy as np
from scipy.optimize import minimize
from valentiner_rank_lifting import base_potential,unpack,pack,cross_operators,DEFAULT_CROSS
from valentiner_joint import Jet
from valentiner_adjoint_quartics import BASIS,quartic_projectors,quartic_value_gradient
from develop_valentiner_susy_vacua import holomorphic_down_matching
from perfectpower.flavor_mediator import canonical_mediator
from perfectpower.flavor_prediction import observables
from perfectpower.flavor_completion import physical_chart
from valentiner_adjoint_quarks import match as adjoint_quark_match

RHO=.1;MEDIATOR_MASS=10.;EPSILON=300.;PENALTIES=(30.,30.)
QUARTIC_COEFFICIENTS=np.array([.1,.2,.3,.4,.5])
MASS_COEFFICIENTS=np.array([.1,.2,.3,.01,.02,.03,.04])
RADIAL_STABILIZER=1e-10


def z_components(x):
    L,A,B=unpack(x);Z=A.conj().T@L@B
    return np.einsum('aij,ji->a',BASIS,Z)


def uv_pack(x,t):return np.r_[x,t.real,t.imag]


def uv_unpack(w):return w[:54],w[54:62]+1j*w[62:70]


def source_terms(x,t):
    L,A,B=unpack(x);z=np.concatenate([L.ravel(),A.ravel(),B.ravel()]);js=[]
    for i,v in enumerate(z):
        g=np.zeros(54,complex);g[i]=1;g[i+27]=1j;js.append(Jet(v,g))
    L,A,B=[np.array(js[i:i+9],object).reshape(3,3) for i in [0,9,18]]
    tr=lambda M:sum(M[i,i] for i in range(3));dag=lambda M:M.conj().T
    na,nb,nl=[tr(dag(M)@M).real for M in [A,B,L]]
    ra,rb=dag(A)@A,dag(B)@B;S=np.einsum('a,aij->ij',t,BASIS)
    Z=dag(A)@L@B
    zv=[tr(BASIS[a]@Z) for a in range(8)]
    # All seven allowed two-mediator/source-bilinear quartics.
    nS=np.vdot(t,t).real
    mixed=[na*nS,nb*nS,nl*nS,tr(S.conj().T@S@ra).real,tr(S@S.conj().T@ra).real,
           tr(S.conj().T@S@rb).real,tr(S@S.conj().T@rb).real]
    # The six pure source/link quartics are nonzero already in the source EFT;
    # these additional terms avoid a vanishing link quadratic or scalar cubic.
    D=sum(sign*L[0,a]*L[1,b]*L[2,c] for (a,b,c),sign in [((0,1,2),1),((1,2,0),1),((2,0,1),1),((0,2,1),-1),((2,1,0),-1),((1,0,2),-1)])
    extra=.0001*nl+.001*D.real+.001*nl*nl+.002*tr(dag(L)@L@dag(L)@L).real+.002*na*na+.003*nb*nb
    return zv,mixed,extra,(na+nb+nl)**6


def potential(w,projectors,epsilon=EPSILON):
    x,t=uv_unpack(w);value,gradient=base_potential(x,PENALTIES)
    _,vs,jac=cross_operators(x,True);value+=epsilon*(DEFAULT_CROSS[2:]@vs[2:]);gradient+=epsilon*(DEFAULT_CROSS[2:]@jac[2:])
    zv,mixed,extra,radial=source_terms(x,t);z=np.array([q.v for q in zv]);zjac=np.array([q.g for q in zv])
    value+=epsilon*(np.vdot(t,t).real-2*np.vdot(t,z).real+extra.v.real)
    gradient+=epsilon*(-2*np.real(t.conj()@zjac)+extra.g.real)
    value+=RADIAL_STABILIZER*radial.v.real;gradient+=RADIAL_STABILIZER*radial.g.real
    delta=RHO**2/MEDIATOR_MASS**2
    value+=epsilon*delta*sum(c*q.v.real for c,q in zip(MASS_COEFFICIENTS,mixed))
    gradient+=epsilon*delta*sum((c*q.g.real for c,q in zip(MASS_COEFFICIENTS,mixed)),np.zeros(54))
    L,A,B=unpack(x);ra,rb=A.conj().T@A,B.conj().T@B
    na,nb,nl=[np.vdot(M,M).real for M in [A,B,L]];S=np.einsum('a,aij->ij',t,BASIS)
    physical_mass_gradient=(MASS_COEFFICIENTS[0]*na+MASS_COEFFICIENTS[1]*nb+MASS_COEFFICIENTS[2]*nl)*t
    for c,R,left in [(MASS_COEFFICIENTS[3],ra,False),(MASS_COEFFICIENTS[4],ra,True),(MASS_COEFFICIENTS[5],rb,False),(MASS_COEFFICIENTS[6],rb,True)]:
        physical_mass_gradient+=c*np.einsum('aij,ji->a',BASIS,R@S if left else S@R)
    dz=epsilon*(t.conj()-z.conj()+delta*physical_mass_gradient.conj())
    qv,qg=quartic_value_gradient(t,projectors,QUARTIC_COEFFICIENTS)
    quartic_scale=epsilon**2*RHO**10/MEDIATOR_MASS**4
    value+=quartic_scale*qv;dz+=quartic_scale*qg
    return float(value),np.r_[gradient,2*dz.real,-2*dz.imag]


def hessian(w,projectors,epsilon=EPSILON,step=1e-5):
    E=np.eye(70);H=np.column_stack([(potential(w+step*e,projectors,epsilon)[1]-potential(w-step*e,projectors,epsilon)[1])/(2*step) for e in E])
    return (H+H.T)/2


def solve(w,projectors,epsilon=EPSILON):
    fun=lambda w:potential(w,projectors,epsilon)
    fit=minimize(fun,w,method='BFGS',jac=True,options={'maxiter':600,'gtol':2e-8});z=fit.x
    for _ in range(4):
        v,g=fun(z)
        if max(abs(g))<1e-8:break
        H=hessian(z,projectors,epsilon);step=np.linalg.solve(H,-g)
        if np.linalg.norm(step)>.05:break
        z+=step
    v,g=fun(z);H=hessian(z,projectors,epsilon)
    sscale=np.sqrt(epsilon)*RHO**5/MEDIATOR_MASS
    physical_scales=np.r_[np.full(54,RHO**4/np.sqrt(2)),np.full(16,RHO**5/(np.sqrt(2)*sscale))]
    return z,{'energy_scaled':v,'stationarity_max':float(max(abs(g))),'minimum_scaled_Hessian_eigenvalue':float(np.linalg.eigvalsh(H)[0]),
              'minimum_canonical_scalar_mass_squared':float(np.linalg.eigvalsh(physical_scales[:,None]*H*physical_scales[None,:])[0]),'iterations':int(fit.nit)}


def quarks(w):
    x,t=uv_unpack(w);L,A,B=unpack(x)
    S=np.sqrt(EPSILON)*RHO**5/MEDIATOR_MASS*np.einsum('a,aij->ij',t,BASIS)
    up=adjoint_quark_match(RHO*L,RHO*A,RHO*B,S,'up');down=adjoint_quark_match(RHO*L,RHO*A,RHO*B,S,'down')
    yu,yd=up['Y'],down['Y']
    Uu,su,_=np.linalg.svd(yu);Ud,sd,_=np.linalg.svd(yd);V=Uu[:,::-1].conj().T@Ud[:,::-1]
    obs=physical_chart(V);obs['spectra']=[su[::-1].tolist(),sd[::-1].tolist()];obs['unitarity_residual']=float(np.max(abs(V.conj().T@V-np.eye(3))))
    return yu,yd,V,obs,down
