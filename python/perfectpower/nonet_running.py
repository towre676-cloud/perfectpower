"""One-loop running for the minimal real-nonet/vectorlike-quark action.

24 real scalars: 20 singlets plus all four Higgs components. Yukawa tensors
use 24 Weyl flavor/weak indices per color. Lepton Yukawas are zero in this
specified benchmark; SM leptons remain in the gauge beta coefficients.
All outputs are 16*pi^2-normalized MS-bar coefficients above the heavy scale.
"""
import numpy as np
from fractions import Fraction
from .nonet_potential import BASIS,operators,OPERATOR_NAMES,D_TENSOR
from .quartic_renormalization import polynomial_hessians


def yukawa_tensors(parameters):
    """parameters shape (2,4): y_H, g_eta, g_s, g_adjoint."""
    p=np.asarray(parameters,float)
    if p.shape!=(2,4):raise ValueError('Two sectors with four real Yukawa coefficients required')
    Y=np.zeros((24,24,24),complex)
    # q_up=0:3,q_down=3:6,u^c=6:9,d^c=9:12,
    # U_L=12:15,U_R^c=15:18,D_L=18:21,D_R^c=21:24.
    def vertex(a,left,right,M):
        Y[a,left,right]=M;Y[a,right,left]=M.T
    I=np.eye(3)
    for f,(y,g,s,a) in enumerate(p):
        left=slice(12+6*f,15+6*f);right=slice(6+3*f,9+3*f);off=10*f
        vertex(off,left,right,g*I);vertex(off+1,left,right,s*I)
        for k,B in enumerate(BASIS):vertex(off+2+k,left,right,a*B.conj())
    yu,yd=p[:,0];qu=slice(0,3);qd=slice(3,6);u=slice(6,9);d=slice(9,12)
    r=np.sqrt(2)
    vertex(20,qd,u,-yu*I/r);vertex(20,qu,d,yd*I/r)
    vertex(21,qd,u,-1j*yu*I/r);vertex(21,qu,d,-1j*yd*I/r)
    vertex(22,qu,u,yu*I/r);vertex(22,qd,d,yd*I/r)
    vertex(23,qu,u,1j*yu*I/r);vertex(23,qd,d,-1j*yd*I/r)
    return Y


def gauge_casimirs():
    color=np.full(24,4/3);weak=np.r_[np.full(6,3/4),np.zeros(18)]
    hyper=np.r_[np.full(6,1/36),np.full(3,4/9),np.full(3,1/9),np.full(6,4/9),np.full(6,1/9)]
    return np.array([color,weak,hyper])


def yukawa_beta(parameters,gauge=(0,0,0)):
    Y=yukawa_tensors(parameters);Y2=np.einsum('aij,aik->jk',Y.conj(),Y);gamma=3*np.einsum('aij,bij->ab',Y.conj(),Y).real
    beta=np.empty_like(Y);C=np.sum(np.asarray(gauge)[:,None]**2*gauge_casimirs(),axis=0)
    for a,Ya in enumerate(Y):
        beta[a]=(Y2.T@Ya+Ya@Y2)/2+2*sum((Yb@Ya.conj().T@Yb for Yb in Y),np.zeros((24,24),complex))
        beta[a]+=np.einsum('b,bij->ij',gamma[a],Y)-3*(C[:,None]+C[None,:])*Ya
    templates=[]
    for f in range(2):
        for j in range(4):
            p=np.zeros((2,4));p[f,j]=1;templates.append(yukawa_tensors(p))
    values=np.array([np.vdot(T,beta).real/np.vdot(T,T).real for T in templates]).reshape(2,4)
    recovered=yukawa_tensors(values);error=float(np.max(abs(recovered-beta)))
    if error>1e-9:raise ValueError('Running generated an omitted renormalizable Yukawa tensor')
    # Higgs anomalous dimension is common to all four real components.
    gamma[20:,20:]-=np.eye(4)*(9*np.asarray(gauge)[1]**2/4+3*np.asarray(gauge)[2]**2/4)
    return values,gamma,{'tensor_closure_error':error,'Weyl_flavor_weak_count_per_color':24,'real_scalar_count':24,
      'normalization':'16*pi^2 beta coefficients; gY uses SM hypercharge, not GUT normalization',
      'scope':'Complete one-loop dimensionless Yukawa running for the specified renormalizable action; lepton Yukawas set zero.'}


def quartic_value_gradient(z,projectors):
    x=z[:20];h=z[20:];v,g=operators(x,projectors);norm=h@h;hh=norm/2
    out=np.r_[v[8:],hh*hh,hh*v[:8]];grad=np.zeros((61,24));grad[:52,:20]=g[8:]
    grad[52,20:]=norm*h
    grad[53:,:20]=hh*g[:8];grad[53:,20:]=v[:8,None]*h
    return out,grad


def fermion_box(z,parameters):
    hh=np.dot(z[20:],z[20:])/2;result=0
    for f,(y,g,s,a) in enumerate(np.asarray(parameters)):
        x=z[10*f:10*f+10];A=np.einsum('a,aij->ij',x[2:],BASIS);C=(g*x[0]+s*x[1])*np.eye(3)+a*A
        K=C@C+y*y*hh*np.eye(3);result-=6*np.trace(K@K).real
    return float(result)


def coupled_quartic_beta(coefficients,projectors,parameters,gauge,seed=741,samples=150):
    c=np.asarray(coefficients,float)
    if c.shape!=(61,):raise ValueError('52 source + one Higgs + eight portal coefficients required')
    _,gamma,ycert=yukawa_beta(parameters,gauge);rng=np.random.default_rng(seed);design=[];parts=[]
    g3,g2,gy=np.asarray(gauge);pure_gauge=9*g2**4/8+3*g2*g2*gy*gy/4+3*gy**4/8
    def value(z):
        v,gradient=quartic_value_gradient(z,projectors);H=polynomial_hessians(lambda t:quartic_value_gradient(t,projectors)[1].T@c,z,step=.25)
        return np.array([np.trace(H@H)/2,(gradient.T@c)@(gamma@z),fermion_box(z,parameters),pure_gauge*(z[20:]@z[20:])**2/4])
    for _ in range(samples):
        z=rng.normal(size=24);design.append(quartic_value_gradient(z,projectors)[0]);parts.append(value(z))
    design=np.array(design);parts=np.array(parts);coef=np.linalg.lstsq(design,parts,rcond=1e-12)[0];errors=[]
    for _ in range(5):
        z=rng.normal(size=24);direct=value(z);found=quartic_value_gradient(z,projectors)[0]@coef;errors.append(float(np.max(abs(direct-found))/max(1,np.max(abs(direct)))))
    if max(errors)>1e-9:raise ValueError('Coupled quartic beta failed independent polynomial validation')
    return coef.sum(axis=1),{'parts':dict(zip(['scalar','wavefunction_Yukawa_gauge','fermion_box','pure_gauge'],coef.T.tolist())),
      'off_grid_relative_errors':errors,'Yukawa_tensor_certificate':ycert,'Higgs_gamma':float(gamma[20,20]),
      'scope':'One-loop full dimensionless running of the specified unbroken minimal action; no lepton Yukawas. Not yet a threshold-matched physical CKM flow.'}


def gauge_beta(gauge):
    return np.array([-3.,-19/6,27/2])*np.asarray(gauge)**3


def gauge_threshold_delta_inverse(gauge,masses,matching_scale):
    """Heavy vectorlike matching: 1/g_low² = 1/g_high² - sum Δb log(m/μ)/(8π²)."""
    masses=np.asarray(masses,float)
    if masses.shape!=(2,3) or np.any(masses<=0) or matching_scale<=0:raise ValueError('Six positive heavy masses and positive matching scale required')
    logs=np.log(masses/matching_scale);delta=np.array([2/3*logs.sum(),0.,16/9*logs[0].sum()+4/9*logs[1].sum()])
    return -delta/(8*np.pi*np.pi)


def finite_mediator_current_running(source_quartics,projectors):
    """Scalar UV beta(g_R)/g_R from Tr[H4 Hess(q_R)] in finite irreps.

    Input has two [radial, finite8_self] quartic pairs. Dimension-one
    current running also receives source wavefunction terms separately.
    """
    rng=np.random.default_rng(37);ratios=[]
    for f,(radial,anisotropy) in enumerate(source_quartics):
        values=[]
        for P in projectors[2:]:
            w,E=np.linalg.eigh(P);e=E[:,w>.5][:,0]
            from valentiner_adjoint_quartics import EMBED
            Q=np.einsum('n,nij->ij',e,EMBED)
            x=rng.normal(size=8)
            def grad(a):
                from .nonet_potential import sector_features
                feat=sector_features(np.r_[0.,0.,a],projectors)
                return radial*feat[7][10,2:]+anisotropy*feat[7][11,2:]
            H=polynomial_hessians(grad,x);q=x@Q@x;values.append(float(np.trace(H@Q)*2/q))
        ratios.append(values)
    return np.array(ratios)


def analytic_yukawa_beta(parameters,gauge):
    p=np.asarray(parameters,float);g3,g2,gy=np.asarray(gauge);out=np.zeros_like(p)
    yu,yd=p[:,0];trace=9*(yu*yu+yd*yd)
    for f,(y,g,s,a) in enumerate(p):
        b=g*g+s*s;k=b+8*a*a/3;hyper=(8/3 if f==0 else 2/3)*gy*gy
        out[f,0]=y*(1.5*(y*y-p[1-f,0]**2)+trace+k/2-8*g3*g3-9*g2*g2/4-(17/12 if f==0 else 5/12)*gy*gy)
        out[f,1:3]=p[f,1:3]*(21*b+8*a*a+y*y-8*g3*g3-hyper)
        out[f,3]=a*(3*b+8*a*a+y*y-8*g3*g3-hyper)
    return out


def heavy_mass_beta(masses,parameters,gauge):
    g3,_,gy=np.asarray(gauge);p=np.asarray(parameters);k=p[:,1]**2+p[:,2]**2+8*p[:,3]**2/3
    return np.asarray(masses)*(k/2-8*g3*g3-np.array([8/3,2/3])*gy*gy)


def thermal_quadratic(z,c,projectors,parameters,gauge):
    """Leading high-temperature coefficient V_T=T² times this value."""
    v,g=quartic_value_gradient(z,projectors)
    H=polynomial_hessians(lambda x:quartic_value_gradient(x,projectors)[1].T@c,z,step=.25)
    ferm=0;hh=z[20:]@z[20:]/2
    for f,(y,g,s,a) in enumerate(parameters):
        x=z[10*f:10*f+10];b=g*x[0]+s*x[1]
        ferm+=(3*b*b+a*a*(x[2:]@x[2:])+3*y*y*hh)/4
    _,g2,gy=np.asarray(gauge)
    return float(np.trace(H)/24+ferm+(3*g2*g2+gy*gy)*hh/16)


def quadratic_basis(z):
    x=np.asarray(z);values=[];gradient=np.zeros((9,24));H=np.zeros((9,24,24))
    for f in range(2):
        off=10*f;k=4*f;eta,s=x[off:off+2];a=x[off+2:off+10]
        values.extend([eta*eta,s*s,eta*s,a@a]);gradient[k,off]=2*eta;gradient[k+1,off+1]=2*s
        gradient[k+2,off:off+2]=[s,eta];gradient[k+3,off+2:off+10]=2*a
        H[k,off,off]=H[k+1,off+1,off+1]=2;H[k+2,off,off+1]=H[k+2,off+1,off]=1
        H[k+3,off+2:off+10,off+2:off+10]=2*np.eye(8)
    values.append(x[20:]@x[20:]/2);gradient[8,20:]=x[20:];H[8,20:,20:]=np.eye(4)
    return np.array(values),gradient,H


def scalar_gamma(parameters,gauge):
    p=np.asarray(parameters);out=np.zeros((24,24))
    for f in range(2):
        off=10*f;out[off:off+2,off:off+2]=18*np.outer(p[f,1:3],p[f,1:3]);out[off+2:off+10,off+2:off+10]=6*p[f,3]**2*np.eye(8)
    out[20:,20:]=(9*np.sum(p[:,0]**2)-9*gauge[1]**2/4-3*gauge[2]**2/4)*np.eye(4)
    return out


def fermion_box_coefficients(parameters):
    out=np.zeros(61)
    for f,(y,g,s,a) in enumerate(parameters):
        out[12*f:12*f+12]=-6*np.array([3*g**4,12*g**3*s,18*g*g*s*s,12*g*s**3,3*s**4,
          6*g*g*a*a,12*g*s*a*a,6*s*s*a*a,4*g*a**3,4*s*a**3,a**4/2,0])
        out[53+4*f:57+4*f]=-12*y*y*np.array([3*g*g,3*s*s,6*g*s,a*a])
    out[52]=-18*np.sum(np.asarray(parameters)[:,0]**4)
    return out


class RunningKernel:
    """Fast polynomial projection of all 83 minimal-action one-loop RGEs."""
    def __init__(self,projectors,algebra,seed=950):
        self.projectors=projectors;self.algebra=algebra;rng=np.random.default_rng(seed)
        points=rng.normal(size=(100,24));data=[quartic_value_gradient(z,projectors) for z in points]
        V=np.array([v for v,g in data]);G=np.array([g for v,g in data]);pinv=np.linalg.pinv(V,rcond=1e-12)
        self.gamma_templates=[]
        for off in [0,10]:
            for a,b in [(off,off),(off+1,off+1),(off,off+1)]:
                t=np.zeros((24,24));t[a,b]=1;t[b,a]=1;self.gamma_templates.append(t)
            t=np.zeros((24,24));t[off+2:off+10,off+2:off+10]=np.eye(8);self.gamma_templates.append(t)
        t=np.zeros((24,24));t[20:,20:]=np.eye(4);self.gamma_templates.append(t)
        self.wave=np.array([pinv@np.einsum('pkf,fg,pg->pk',G,t,points) for t in self.gamma_templates])
        qdata=[quadratic_basis(z) for z in points];QV=np.array([v for v,g,h in qdata]);QG=np.array([g for v,g,h in qdata]);qpinv=np.linalg.pinv(QV)
        self.mass_wave=np.array([qpinv@np.einsum('pkf,fg,pg->pk',QG,t,points) for t in self.gamma_templates])
        H=np.array([polynomial_hessians(lambda y:quartic_value_gradient(y,projectors)[1],z) for z in points[:24]])
        HQ=qdata[0][2];qp=np.linalg.pinv(QV[:24])
        self.mass_scalar=np.einsum('lp,pjk->ljk',qp,np.einsum('jab,pkab->pjk',HQ,H))
        # Inputs are complete exact rational polynomial identities for scalar A;
        # projections of wave/mass maps have independent point checks in tests.
    def beta(self,quartics,quadratics,parameters,masses,gauge):
        c=np.asarray(quartics);q=np.asarray(quadratics);p=np.asarray(parameters);gauge=np.asarray(gauge)
        weights=[]
        for f in range(2):weights.extend([18*p[f,1]**2,18*p[f,2]**2,18*p[f,1]*p[f,2],6*p[f,3]**2])
        weights.append(9*np.sum(p[:,0]**2)-9*gauge[1]**2/4-3*gauge[2]**2/4)
        bc=np.einsum('kij,i,j->k',self.algebra,c,c)+np.einsum('r,rki,i->k',weights,self.wave,c)+fermion_box_coefficients(p)
        bc[52]+=9*gauge[1]**4/8+3*gauge[1]**2*gauge[2]**2/4+3*gauge[2]**4/8
        bq=np.einsum('ijk,j,k->i',self.mass_scalar,q,c)+np.einsum('r,rki,i->k',weights,self.mass_wave,q)
        for f,(y,eta,s,a) in enumerate(p):bq[4*f:4*f+4]-=12*masses[f]**2*np.array([3*eta*eta,3*s*s,6*eta*s,a*a])
        return {'quartics':bc,'quadratics':bq,'Yukawas':analytic_yukawa_beta(p,gauge),
                'heavy_masses':heavy_mass_beta(masses,p,gauge),'gauge':gauge_beta(gauge)}
