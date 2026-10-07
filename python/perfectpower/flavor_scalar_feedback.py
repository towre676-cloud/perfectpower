"""Full Gaussian/non-Gaussian scalar feedback and weak-coupling continuation.

Fixed MS inputs, local first-order force. No resummed vacuum, gauge contribution,
global vacuum selection or golden-frame prediction is implied.
"""
import numpy as np
from .nonet_potential import operators,joint_higgs,nonet_fields
from .nonet_mediators import mediation_plan,currents,completed_hessian
from .flavor_hermitian import block_spectrum
from .flavor_quantum import fermion_CW_gradient,scalar_threshold


def scalar_CW(H,mu=1.):
    H=np.asarray(H,float)
    if H.ndim!=2 or H.shape[0]!=H.shape[1] or not np.all(np.isfinite(H)) or not np.isfinite(mu) or mu<=0:
        raise ValueError('Finite square Hessian and positive scale required')
    if np.max(abs(H-H.T))>1e-10*max(1,np.linalg.norm(H)):
        raise ValueError('Real symmetric Hessian required')
    w=np.linalg.eigvalsh(H)
    if np.min(w)<=0:raise ValueError('Strictly positive massive scalar Hessian required')
    return float(np.sum(w*w*(np.log(w/mu**2)-1.5))/(64*np.pi**2))


def scalar_CW_gradient(H,derivatives,mu=1.):
    scalar_CW(H,mu)
    H=np.asarray(H,float);dH=np.asarray(derivatives,float)
    if dH.ndim!=3 or dH.shape[1:]!=H.shape or not np.all(np.isfinite(dH)):
        raise ValueError('Matching finite Hessian derivatives required')
    w,U=np.linalg.eigh(H);W=(U*(w*(np.log(w/mu**2)-1)))@U.T
    return np.einsum('ij,kji->k',W,dH)/(32*np.pi**2)


def spectral_log_derivative(values,mu=1.):
    """Divided differences of x[log(x/mu^2)-1], including degeneracies."""
    x=np.asarray(values,float)
    if np.any(x<=0) or mu<=0:raise ValueError('Positive spectral arguments required')
    out=np.empty((len(x),len(x)))
    for i,a in enumerate(x):
        for j,b in enumerate(x):
            t=(a-b)/b
            if abs(t)<1e-5:out[i,j]=np.log(b/mu**2)+t/2-t*t/6+t**3/12
            else:out[i,j]=(a*(np.log(a/mu**2)-1)-b*(np.log(b/mu**2)-1))/(a-b)
    return (out+out.T)/2


class SingletScalarModel:
    def __init__(self,benchmark,non_gaussian=True):
        from valentiner_adjoint_quartics import quartic_projectors
        from develop_valentiner_nonet_joint import hessian
        self.hessian=hessian;self.P=np.array(quartic_projectors()[0]);self.z=np.array(benchmark['source_coordinates'])
        self.c=np.array(benchmark['source_coefficients']);self.portals=np.array(benchmark['Higgs_portals']);self.mu2=benchmark['Higgs_mu2'];self.M=benchmark['mediator_mass']
        self.plan=mediation_plan(self.c,self.P,self.M,finite_only=True,sector_ratios=(1.1,.8,1.3))
        self.g=np.array(benchmark['singlet_source_current_coefficients']);self.h=np.array([.06,-.04]);self.bare=np.array([1.,.9])
        self.k=np.array([.03,.04,.005,.02,.035,.045,.004,.025,.05]);self.r3=.07 if non_gaussian else 0.;self.r4=.09 if non_gaussian else 0.
        if not non_gaussian:self.k*=0
        self.non_gaussian=non_gaussian
        self.Q=np.array([(self.current(np.eye(21)[j])[1]-self.current(-np.eye(21)[j])[1])/2 for j in range(21)]).transpose(1,2,0)
        self.KQ=np.column_stack([(self.invariants(np.eye(21)[j])[1].T@self.k-self.invariants(-np.eye(21)[j])[1].T@self.k)/2 for j in range(21)])
        J,_=self.current(self.z);self.vac=np.r_[self.z,-J/self.M**2];self.K0=float(self.k@self.invariants(self.z)[0])

    def invariants(self,z):
        q,g=operators(z[:20],self.P);values=np.r_[q[:8],z[20]**2/2];D=np.zeros((9,21));D[:8,:20]=g[:8];D[8,20]=z[20]
        return values,D

    def current(self,z):
        J,D=currents(z[:20],self.plan,self.P);D=np.column_stack([D,np.zeros(len(D))]);q,dq=self.invariants(z)
        return np.r_[J,self.g@q],np.vstack([D,self.g@dq])

    def source(self,z):return joint_higgs(z,self.c,self.P,self.portals,self.mu2)

    def potential(self,X):
        z=X[:21];sigma=X[21:];J,D=self.current(z);F=sigma+J/self.M**2;t=sigma[-1]-self.vac[-1];q,dq=self.invariants(z);K=self.k@q-self.K0;dK=self.k@dq
        v,g=self.source(z)
        value=v+self.M**2*(F@F)/2+self.r3*t**3/3+self.r4*t**4/4+t*t*K/2
        return float(value),np.r_[g+D.T@F+t*t*dK/2,self.M**2*F+np.r_[np.zeros(len(sigma)-1),self.r3*t*t+self.r4*t**3+t*K]]

    def full_hessian(self,X):
        z=X[:21];J,D=self.current(z);sigma=X[21:];F=sigma+J/self.M**2;t=sigma[-1]-self.vac[-1];q,dq=self.invariants(z)
        H=self.hessian(self.source,z);HV=completed_hessian(H,D,self.M);HV[:21,:21]+=np.einsum('i,ijk->jk',F,self.Q)
        HV[:21,:21]+=t*t*self.KQ/2;HV[:21,-1]+=t*(self.k@dq);HV[-1,:21]+=t*(self.k@dq)
        HV[-1,-1]+=2*self.r3*t+3*self.r4*t*t+self.k@q-self.K0
        return (HV+HV.T)/2

    def hessian_derivatives(self,X):
        z=X[:21];_,D=self.current(z);n=len(self.vac);out=np.zeros((n,n,n));t=X[-1]-self.vac[-1]
        # Source Hessian is quadratic in canonical fields: this central
        # difference differentiates that polynomial, rather than loop energies.
        for k in range(21):
            e=np.eye(21)[k]*.02;dH=(self.hessian(self.source,z+e)-self.hessian(self.source,z-e))/.04;dD=self.Q[:,:,k]
            out[k,:21,:21]=dH+(dD.T@D+D.T@dD)/self.M**2+np.einsum('i,ijk->jk',D[:,k]/self.M**2,self.Q)
            out[k,:21,21:]=dD.T;out[k,21:,:21]=dD
        out[21:,:21,:21]=self.Q
        dK=self.k@self.invariants(z)[1];out[:21,-1,-1]+=dK;out[-1,:21,-1]+=dK;out[-1,-1,:21]+=dK;out[-1,-1,-1]+=2*self.r3+6*self.r4*t
        out[:21,:21,-1]+=t*self.KQ.T;out[:21,-1,:21]+=t*self.KQ.T;out[-1,:21,:21]+=t*self.KQ
        return out

    def vacuum_derivatives(self):return self.hessian_derivatives(self.vac)

    def fermions(self,X=None):
        from develop_valentiner_mediator_closure import scalar_vertices
        X=self.vac if X is None else X;z=X[:21]
        spectra=[];vertices=[]
        for f,(eta,t,A) in enumerate(nonet_fields(z[:20])):
            spectrum=block_spectrum((.1*eta+.7*t)*np.eye(3)+.8*A,[1.2,.57][f],self.bare[f]+self.h[f]*X[-1],z[20]/np.sqrt(2))
            G=scalar_vertices(len(self.vac),f);G[-1,3:,3:]=self.h[f]*np.eye(3);spectra.append(spectrum);vertices.append(G)
        return spectra,vertices

    def loop_gradient(self,X,mu=1.):
        H=self.full_hessian(X);g=scalar_CW_gradient(H,self.hessian_derivatives(X),mu);spectra,G=self.fermions(X)
        return g+sum((fermion_CW_gradient(s['mass_matrix'],v,mu) for s,v in zip(spectra,G)),np.zeros(len(H)))

    def loop_hessian(self,X,mu=1.):
        H=self.full_hessian(X);w,U=np.linalg.eigh(H)
        if w[0]<=0:raise ValueError('Positive scalar Hessian required')
        T=self.hessian_derivatives(X);E=np.einsum('ai,kab,bj->kij',U,T,U);L=spectral_log_derivative(w,mu)
        result=np.einsum('iab,ab,jba->ij',E,L,E)/(32*np.pi**2)
        W=(U*(w*(np.log(w/mu**2)-1)))@U.T
        # Quartic fourth derivatives are fully symmetric. Polarization
        # contracts W with that tensor using 22 eigen-directions, without
        # storing a four-index tensor or sampling displaced loop spectra.
        active=[*range(21),len(X)-1];weights,directions=np.linalg.eigh(W[np.ix_(active,active)])
        zero=np.zeros(len(X));H0=self.full_hessian(zero);contraction=np.zeros_like(H)
        for weight,direction in zip(weights,directions.T):
            v=zero.copy();v[active]=direction
            contraction+=weight*(self.full_hessian(v)+self.full_hessian(-v)-2*H0)
        result+=contraction/(32*np.pi**2)
        spectra,G=self.fermions(X)
        for spectrum,vertices in zip(spectra,G):
            D=spectrum['mass_matrix'];Z=D.conj().T@D;lam,F=np.linalg.eigh(Z);WF=(F*(lam*(np.log(lam/mu**2)-1)))@F.conj().T
            dZ=np.array([v.conj().T@D+D.conj().T@v for v in vertices]);eZ=np.einsum('ai,kab,bj->kij',F.conj(),dZ,F)
            term=np.einsum('iab,ab,jba->ij',eZ,spectral_log_derivative(lam,mu),eZ)
            for i,v in enumerate(vertices):
                for j,u in enumerate(vertices):term[i,j]+=np.trace(WF@(v.conj().T@u+u.conj().T@v))
            result-=3*term.real/(8*np.pi**2)
        return result

    def angular_tangents(self):
        from valentiner_adjoint_quartics import BASIS
        T=[]
        for f,(_,_,A) in enumerate(nonet_fields(self.z[:20])):
            velocities=np.array([np.einsum('aij,ji->a',BASIS,1j*(B@A-A@B)).real for B in BASIS]).T
            U,s,_=np.linalg.svd(velocities);assert s[5]>1e-8 and s[6]<1e-10
            block=np.zeros((21,6));block[10*f+2:10*f+10]=U[:,:6];T.append(block)
        return np.column_stack(T)


def weak_continuation_certificate():
    import sympy as s
    r=s.Symbol('r',positive=True)
    # V_r(X)=V(sqrt(r) X)/r, D_r(X)=D(sqrt(r) X).
    assert s.simplify(s.sqrt(r)*s.sqrt(r)-r)==0
    return {'action':'V_r(X)=V_1(sqrt(r) X)/r; D_r(X)=D_1(sqrt(r) X)',
            'vacuum':'X_r=X_1/sqrt(r)','scalar_Hessian':'H_r(X_r)=H_1(X_1)',
            'fermion_mass_matrices':'D_r(X_r)=D_1(X_1)',
            'degree_d_scalar_coefficients':'r^(d/2-1) times the original degree-d coefficient, including centered-contact expansions',
            'all_dimensionless_Yukawas':'sqrt(r) times original; bare fermion masses unchanged',
            'scalar_and_fermion_CW_gradient':'sqrt(r) times the original gradient at unchanged MS scale',
            'first_order_vacuum_shift':'sqrt(r) times the original shift',
            'relative_vacuum_shift':'r times the original relative shift',
            'neutral_scalar_fermion_mass_correction':'r times original one-loop matrix correction',
            'physical_masses_mixing_and_tree_pole_residues':'Exactly unchanged',
            'singlet_mass_coefficient_row_ratio':'Unchanged; matching-current coefficients scale sqrt(r)',
            'gauge_extension':'Gauge masses and gauge-loop scaling share these identities only if gauge couplings also scale sqrt(r). Fixed measured gauge couplings are not held by this construction.',
            'scope':'Constructive weak-coupling family, not an observed-SM fit, quantum stationary-point proof, all-loop CP cancellation or golden relation.'}


def neutral_loop_stationary_branch(model,r=1e-6,mu=1.):
    if not np.isfinite(r) or not 0<r<=1e-6:raise ValueError('Declared local positive-spectrum range 0<r<=1e-6 required')
    X=model.vac.copy();history=[]
    for iteration in range(12):
        value,g=model.potential(X);F=g+r*model.loop_gradient(X,mu);residual=float(np.max(abs(F)))
        history.append({'iteration':iteration,'maximum_tadpole_residual':residual})
        if residual<2e-10:break
        X-=np.linalg.solve(model.full_hessian(X),F)
    else:raise RuntimeError('Local loop tadpole iteration did not converge')
    loopH=model.loop_hessian(X,mu)
    antisym=float(np.max(abs(loopH-loopH.T)));effective=model.full_hessian(X)+r*(loopH+loopH.T)/2;w=np.linalg.eigvalsh(effective)
    spectra,vertices=model.fermions(X);V=spectra[0]['doublet_frame'].conj().T@spectra[1]['doublet_frame'];J=float(np.imag(V[0,0]*V[1,1]*V[0,1].conjugate()*V[1,0].conjugate()))
    corrections=[scalar_threshold(s['mass_matrix'],np.sqrt(r)*v,model.full_hessian(X),mu) for s,v in zip(spectra,vertices)]
    return {'r':r,'MS_scale':mu,'rescaled_coordinates_Y':X.tolist(),'iteration_history':history,
            'maximum_tadpole_residual':residual,'minimum_neutral_loop_Hessian_eigenvalue':float(w[0]),'loop_Hessian_antisymmetric_residual':antisym,
            'relative_shift_over_full_background':float(np.linalg.norm(X-model.vac)/np.linalg.norm(model.vac)),
            'relative_shift_over_source_background':float(np.linalg.norm(X[:21]-model.z)/np.linalg.norm(model.z)),
            'conditional_canonical_tree_quartet_at_loop_vacuum':J,'conditional_canonical_Dirac_masses':[s['masses'].tolist() for s in spectra],
            'first_order_neutral_scalar_phases_at_loop_background':[c['delta_theta'] for c in corrections],
            'neutral_scalar_relative_mass_correction_norms_at_loop_background':[c['relative_correction_norm'] for c in corrections],
            'scope':'Numerically solved local stationary point of Vtree(Y)+r[V_CW,49 neutral+V_CW,quarks](Y). Positive spectral/polynomial curvature, not an interval proof. Gauge graphs and Goldstone resummation are absent; masses/current are canonical tree quantities at this loop-selected background, not fully matched loop observables.'}
