"""Fixed-coupling Landau-MS vector feedback and tadpole-calibrated hard branch.

One-loop Goldstones are omitted in the anti-resummation organization. Curvatures
are effective-potential curvatures, not pole masses or gauge-invariant observables.
"""
import numpy as np


def vector_CW(h,g=.65,gprime=.36,mu=1.):
    """W+, W- and Z: multiplicities 6,3; MS vector subtraction 5/6."""
    if not np.all(np.isfinite([h,g,gprime,mu])) or mu<=0 or g<0 or gprime<0:
        raise ValueError('Finite background, nonnegative couplings and positive scale required')
    if h==0:return (0.,0.,0.)
    a=np.array([g*g/4,(g*g+gprime*gprime)/4]);n=np.array([6.,3.]);active=a>0;a=a[active];n=n[active]
    x=a*h*h;L=np.log(x/mu**2)
    value=np.sum(n*x*x*(L-5/6))/(64*np.pi**2)
    gradient=np.sum(n*a*a*h**3*(L-1/3))/(16*np.pi**2)
    curvature=np.sum(n*a*a*h*h*(3*L+1))/(16*np.pi**2)
    return float(value),float(gradient),float(curvature)


def pulled_vector_CW(h,r=1e-6,g=.65,gprime=.36,mu=1.):
    """r Vvector(h/sqrt(r)); derivatives in Y=sqrt(r)X coordinates."""
    if not np.isfinite(r) or r<=0:raise ValueError('Positive finite continuation parameter required')
    v,d,k=vector_CW(h/np.sqrt(r),g,gprime,mu)
    return r*v,np.sqrt(r)*d,k


def calibrated_vector_CW(h,h0,r=1e-6,g=.65,gprime=.36,mu=1.):
    """Add only -delta_mu2 h^2/2, delta_mu2=Vvector'(h0)/h0.

    The Higgs reference radius is an input. No curvature or frame fit is made.
    Log-ratio evaluation avoids subtracting large nearly equal tadpoles.
    """
    if not np.all(np.isfinite([h0,h])) or h0<=0 or h<=0:raise ValueError('Finite positive reference and background Higgs radii required')
    _,d0,_=pulled_vector_CW(h0,r,g,gprime,mu);delta=d0/h0
    a=np.array([g*g/4,(g*g+gprime*gprime)/4]);n=np.array([6.,3.]);active=a>0;a=a[active];n=n[active]
    L0=np.log(a*h0*h0/(r*mu**2));t=(h-h0)/h0;logratio=2*np.log1p(t)
    pref=n*a*a/(16*np.pi**2*r)
    grad=np.sum(pref*h*((h-h0)*(h+h0)*(L0-1/3)+h*h*logratio))
    curv=np.sum(pref*(h*h*(3*(L0+logratio)+1)-h0*h0*(L0-1/3)))
    # Value relative to h0, with the calibrated quadratic contact included.
    x0=h0*h0;xh=h*h
    val=np.sum(pref/4*(xh*xh*logratio+(xh-x0)*(xh+x0)*(L0-5/6)-2*x0*(xh-x0)*(L0-1/3)))
    return float(val),float(grad),float(curv),float(delta)


def raw_fixed_gauge_diagnostic(model,r=1e-6,g=.65,gprime=.36,mu=1.):
    X=model.vac;v,d,k=pulled_vector_CW(X[20],r,g,gprime,mu);force=np.zeros(len(X));force[20]=d
    H=model.full_hessian(X);shift=-np.linalg.solve(H,force);T=model.angular_tangents()
    return {'r':r,'g':g,'gprime':gprime,'MS_scale':mu,'physical_Higgs_radius':float(X[20]/np.sqrt(r)),
            'W_squared_mass':float(g*g*X[20]**2/(4*r)),'Z_squared_mass':float((g*g+gprime*gprime)*X[20]**2/(4*r)),
            'pulled_vector_potential':v,'pulled_vector_Higgs_force':d,'pulled_vector_Higgs_curvature':k,
            'direct_isospectral_angular_force_norm':float(np.linalg.norm(T.T@force[:21])),
            'relative_linear_shift':float(np.linalg.norm(shift)/np.linalg.norm(X)),
            'linear_Higgs_shift_over_reference':float(shift[20]/X[20]),
            'linear_induced_isospectral_angular_shift_norm':float(np.linalg.norm(T.T@shift[:21])),
            'minimum_bare_Hessian_at_linear_displacement':float(np.linalg.eigvalsh(model.full_hessian(X+shift))[0]),
            'scope':'Raw first-order diagnostics only; large or negative-spectrum shifts are not solved vacua.'}


def calibrated_hard_branch(model,r=1e-6,g=.65,gprime=.36,mu=1.):
    """Solve a declared one-loop hard potential with a finite Higgs mass input.

    Counterterms are outside the tree propagators at this truncation order.
    Large radial corrections require separate power counting and matching.
    """
    if not np.isfinite(r) or not 0<r<=1e-6:raise ValueError('Declared positive-spectrum local continuation range required')
    X=model.vac.copy();h0=X[20];history=[]
    for iteration in range(12):
        _,tg=model.potential(X);lg=model.loop_gradient(X,mu)
        _,vg,vh,delta=calibrated_vector_CW(X[20],h0,r,g,gprime,mu)
        F=tg+r*lg;F[20]+=vg
        residual=float(np.max(abs(F)));history.append({'iteration':iteration,'maximum_tadpole_residual':residual})
        if residual<2e-10:break
        H=model.full_hessian(X);H[20,20]+=vh
        step=np.linalg.solve(H,F)
        for shrink in range(20):
            trial=X-step/(2**shrink)
            if trial[20]>0 and np.linalg.eigvalsh(model.full_hessian(trial))[0]>0:
                X=trial;break
        else:raise RuntimeError('Step leaves the positive neutral scalar domain')
    else:raise RuntimeError('Hard tadpole iteration did not converge')
    treeH=model.full_hessian(X);loopH=model.loop_hessian(X,mu);effective=treeH+r*(loopH+loopH.T)/2;effective[20,20]+=vh
    spectra,_=model.fermions(X);V=spectra[0]['doublet_frame'].conj().T@spectra[1]['doublet_frame'];J=float(np.imag(V[0,0]*V[1,1]*V[0,1].conjugate()*V[1,0].conjugate()))
    # Every scalar/fermion/vector hard term depends on the single doublet's
    # radius. Its angular O(4) Ward curvature is radial tadpole / h.
    Gtree=float(tg[20]/X[20]-delta)
    Ghard=float(r*lg[20]/X[20]+(vg+delta*X[20])/X[20])
    return {'r':r,'g':g,'gprime':gprime,'MS_scale':mu,'finite_Higgs_mass_adjustment':delta,
            'reference_Higgs_radius_is_input':float(h0/np.sqrt(r)),
            'rescaled_coordinates_Y':X.tolist(),'iteration_history':history,
            'maximum_tadpole_residual':residual,'minimum_bare_neutral_Hessian_eigenvalue':float(np.linalg.eigvalsh(treeH)[0]),
            'minimum_hard_potential_curvature_eigenvalue':float(np.linalg.eigvalsh(effective)[0]),
            'calibrated_vector_radial_curvature':vh,'vector_radial_curvature_over_reference_tree':float(vh/model.full_hessian(model.vac)[20,20]),
            'relative_vacuum_shift':float(np.linalg.norm(X-model.vac)/np.linalg.norm(model.vac)),
            'relative_Higgs_radius_shift':float(X[20]/h0-1),
            'conditional_canonical_tree_quartet':J,'conditional_canonical_Dirac_masses':[s['masses'].tolist() for s in spectra],
            'Goldstone_tree_plus_mass_adjustment_squared_mass':Gtree,'Goldstone_hard_Ward_correction':Ghard,
            'Goldstone_Ward_residual':float(F[20]/X[20]),
            'Goldstone_cancellation_roundoff_residual':float(Gtree+Ghard),
            'scope':'Local stationary point of the declared Landau-MS hard one-loop potential, with an explicit finite Higgs mass calibration. One-loop Goldstone graphs use the anti-resummation zero rule; the Ward residual is a tadpole identity, not a computed Goldstone pole self-energy. Gauge curvatures are not pole masses. Radial corrections dominate tree curvature; no uniformly small scalar expansion, complete running, gauge-independent matching, global minimum or golden prediction.'}


def exact_gauge_identities():
    """Symbolic fixed-coupling pullback, tadpole contact and radial curvature."""
    import sympy as s
    h,h0,a,r,mu,n=s.symbols('h h0 a r mu n',positive=True)
    v=n*a*a*h**4*(s.log(a*h*h/(r*mu*mu))-s.Rational(5,6))/(64*s.pi**2*r)
    d=s.diff(v,h);k=s.diff(d,h);delta=d.subs(h,h0)/h0
    expected=n*a*a*h0*h0*(s.log(a*h0*h0/(r*mu*mu))+s.Rational(2,3))/(8*s.pi**2*r)
    assert s.simplify(k.subs(h,h0)-delta-expected)==0
    assert s.simplify((d-delta*h).subs(h,h0))==0
    # The quadratic gauge-scale contact is not needed: scale variation is
    # a pure Higgs quartic, with fixed source labels and eigenframes absent.
    assert s.simplify(mu*s.diff(v,mu)+n*a*a*h**4/(32*s.pi**2*r))==0
    return {'pulled_vector_potential':'sum n a^2 h^4 [log(a h^2/(r mu^2))-5/6]/(64 pi^2 r)',
            'calibrated_radial_curvature':'sum n a^2 h0^2 [log(a h0^2/(r mu^2))+2/3]/(8 pi^2 r)',
            'log_scale_derivative':'-sum n a^2 h^4/(32 pi^2 r)',
            'fixed_coupling_weak_limit':'Generic fixed g,gprime: gauge force grows as log(1/r)/r in Y coordinates, not as r.',
            'orientation_theorem':'Vectors depend only on HdaggerH. All eight quadratic source Higgs portals depend only on eta,s,Tr(A^2). They are constant on each independent unitary adjoint orbit, since Tr(A[B,A])=0. Profiling the Higgs along a selected branch cannot generate relative-frame dependence from this gauge/portal subsystem alone.',
            'qualification':'Existing finite-family scalar interactions can couple radial and angular responses. This is a direct one-loop vector torque statement, not an all-loop electroweak no-go theorem.'}
