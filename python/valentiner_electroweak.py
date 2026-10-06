"""Joint flavor/Higgs branch with all four renormalizable norm portals."""
import numpy as np
from scipy.optimize import minimize
from valentiner_adjoint_uv import potential,hessian,uv_unpack,RHO,EPSILON,MEDIATOR_MASS,BASIS
from valentiner_canonical_quarks import PARAMETERS,match
from perfectpower.flavor_canonical import full_spectrum

PORTALS=np.array([1e-4,2e-4,3e-4,4e-4])
HIGGS_QUARTIC=.13
SCALE_S=np.sqrt(EPSILON)*RHO**5/MEDIATOR_MASS
COORDINATE_SCALES=np.r_[np.full(54,np.sqrt(2)*RHO),np.full(16,np.sqrt(2)*SCALE_S)]


def norm_data(w):
    norms=np.array([RHO**2*np.vdot(w[a:b],w[a:b]).real for a,b in [(0,9),(9,18),(18,27)]])
    # Each source real part has its imaginary part 27 coordinates later.
    norms+=np.array([RHO**2*np.vdot(w[a+27:b+27],w[a+27:b+27]).real for a,b in [(0,9),(9,18),(18,27)]])
    norms=np.r_[norms,SCALE_S**2*np.vdot(w[54:],w[54:]).real]
    J=np.zeros((4,70))
    for k,(a,b) in enumerate([(0,9),(9,18),(18,27)]):
        J[k,a:b]=2*RHO**2*w[a:b];J[k,a+27:b+27]=2*RHO**2*w[a+27:b+27]
    J[3,54:]=2*SCALE_S**2*w[54:]
    return norms,J


def portal_hessian():
    diag=np.zeros(70)
    for k,(a,b) in enumerate([(0,9),(9,18),(18,27)]):
        diag[a:b]=diag[a+27:b+27]=2*RHO**2*PORTALS[k]
    diag[54:]=2*SCALE_S**2*PORTALS[3]
    return np.diag(diag)


def branch(seed,projectors,vev=.03):
    def fun(w):
        v,g=potential(w,projectors);n,J=norm_data(w)
        return v+vev**2*(PORTALS@n)/RHO**10,g+vev**2*(PORTALS@J)/RHO**10
    fit=minimize(fun,seed,jac=True,method='BFGS',options={'gtol':2e-8,'maxiter':500});w=fit.x
    for _ in range(4):
        value,g=fun(w)
        if max(abs(g))<1e-8:break
        H=hessian(w,projectors)+vev**2*portal_hessian()/RHO**10
        step=np.linalg.solve(H,-g)
        if np.linalg.norm(step)>.2:break
        w+=step
    value,g=fun(w);n,J=norm_data(w)
    H=RHO**10*hessian(w,projectors)+vev**2*portal_hessian()
    H=H/COORDINATE_SCALES[:,None]/COORDINATE_SCALES[None,:]
    mixed=np.sqrt(2)*vev*(PORTALS@J)/COORDINATE_SCALES
    full=np.block([[H,mixed[:,None]],[mixed[None,:],np.array([[4*HIGGS_QUARTIC*vev**2]])]])
    mu_squared=2*HIGGS_QUARTIC*vev**2+PORTALS@n
    return w,full,{'vev':vev,'Higgs_quartic':HIGGS_QUARTIC,'Higgs_mass_parameter_squared':float(mu_squared),
                   'portals':PORTALS.tolist(),'stationarity_scaled_max':float(max(abs(g))),
                   'minimum_71_scalar_mass_squared':float(np.linalg.eigvalsh(full)[0]),
                   'energy_scaled_flavor_portal':float(value),'iterations':int(fit.nit)}


def vertices(sector,spurion=1.):
    _,_,_,lf,lr,sf,sr,cl,ca,y=PARAMETERS[sector]
    G=np.zeros((71,12,12),complex)
    # Canonical sigma = sqrt(2) Re/Im phi, in the saved coordinate order.
    for i in range(3):
        for j in range(3):
            k=3*i+j
            for imag in [0,1]:
                f=(1j if imag else 1)/np.sqrt(2)
                G[k+27*imag,3+j,i]=spurion*cl*f.conjugate()
                G[9+k+27*imag,6+j,i]=spurion*ca*f.conjugate()
                G[18+k+27*imag,3+i,9+j]=spurion*lf*f
                G[18+k+27*imag,9+j,3+i]=spurion*lr*f.conjugate()
    for a in range(8):
        for imag in [0,1]:
            f=(1j if imag else 1)/np.sqrt(2);k=54+a+8*imag
            G[k,6:9,9:12]=spurion*sf*f*BASIS[a]
            G[k,9:12,6:9]=spurion*sr*f.conjugate()*BASIS[a]
    G[70,:3,:3]=y*np.eye(3)/np.sqrt(2)
    return G


def scaled_kernel(fields,sector,spurion=1.):
    if not np.isfinite(spurion) or spurion<=0:raise ValueError('Positive real spurion required')
    k=match(*fields,sector)
    k=dict(k,F=spurion*k['F'],M=spurion*k['M'],C=spurion*k['C'],
           G=spurion**2*k['G'],Z1=k['Z1']/spurion**2,heavy_gap=spurion*k['heavy_gap'],
           hermitian_similarity=spurion*k['hermitian_similarity'])
    return k
