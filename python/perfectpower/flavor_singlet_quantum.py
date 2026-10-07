"""Fermion determinant counterterms and non-Gaussian singlet tree matching.

Box terms omit anomalous dimensions, gauge and scalar diagrams. Local tree
matching is not finite one-loop EFT matching or all-loop CP protection.
"""
import numpy as np


def exact_fermion_counterterms(colours=3):
    import sympy as s
    if not isinstance(colours, int) or colours < 1:
        raise ValueError('Positive integer colour multiplicity required')
    a, m = s.symbols('a m', real=True)
    r = s.symbols('r0:9', real=True)
    C = s.Matrix([[r[0], r[3]+s.I*r[4], r[5]+s.I*r[6]],
                  [r[3]-s.I*r[4], r[1], r[7]+s.I*r[8]],
                  [r[5]-s.I*r[6], r[7]-s.I*r[8], r[2]]])
    D = (a*s.eye(3)).row_join(s.zeros(3)).col_join(C.row_join(m*s.eye(3)))
    target = s.trace(C**4)+2*(a*a+m*m)*s.trace(C**2)+3*(a**4+m**4)
    assert s.expand(s.trace((D.H*D)**2)-target) == 0
    A=C-s.trace(C)*s.eye(3)/3
    assert s.expand(s.trace(A**4)-s.trace(A**2)**2/2)==0
    eta, t, N, T, H, sigma = s.symbols('eta trace N T H sigma', real=True)
    e, b, g, y, h, m0 = s.symbols('e b g y h m0', real=True)
    z = e*eta+b*t
    trace2 = 3*z*z+g*g*N
    trace4 = 3*z**4+6*z*z*g*g*N+4*z*g**3*T+g**4*N*N/2
    mass = m0+h*sigma
    polynomial = s.expand(-2*colours*(trace4+2*(y*y*H+mass*mass)*trace2
                                     +3*(y**4*H*H+mass**4)))
    variables = (eta,t,N,T,H,sigma)
    weights = (1,1,2,3,2,1)
    rows = []
    for powers, coefficient in s.Poly(polynomial,*variables).terms():
        rows.append({'powers':list(powers),'field_degree':sum(i*j for i,j in zip(powers,weights)),
                     'coefficient':str(s.factor(coefficient))})
    assert polynomial.coeff(sigma,2).coeff(H) == 0
    assert s.expand(polynomial.coeff(sigma,4)) == -6*colours*h**4
    return {'exact_general_Hermitian_block_trace_identity':True,
            'exact_traceless_three_by_three_fourth_trace_identity':True,
            'trace_identity':'Tr[(Ddagger D)^2] = Tr(C^4)+2(a^2+m^2)Tr(C^2)+3(a^4+m^4)',
            'colour_multiplicity':colours,'normalization':'16*pi^2 beta_box(V) = -2*Nc*sum_f Tr[(D_fdagger D_f)^2]',
            'variables':list(map(str,variables)),'field_weights':list(weights),'coefficient_parameters':list(map(str,(e,b,g,y,h,m0))),
            'polynomial':str(polynomial),'monomials':rows,
            'sigma_fourth_coefficient':str(-6*colours*h**4),
            'sigma_cubed_coefficient':str(-24*colours*m0*h**3),
            'sigma_squared_source_coefficient':'-4*Nc*h^2*[3(e eta+b trace)^2+g^2 N]',
            'sigma_source_coefficient':'-8*Nc*m0*h*[3(e eta+b trace)^2+g^2 N]',
            'sigma_squared_Higgs_box_coefficient':'0',
            'finite_channel_or_cross_sector_angular_box_coefficients':'0',
            'scope':'Complete fermion determinant/box contribution for the declared neutral-background Dirac blocks, including all field degrees. Scalar wavefunction terms, gauge/scalar loops and fermion vertex running are separate.'}


def exact_portal_regeneration(dimension=8):
    import sympy as s
    if not isinstance(dimension,int) or dimension < 1:
        raise ValueError('Positive source dimension required')
    sigma,H,kappa,rho = s.symbols('sigma H kappa rho',real=True)
    # H denotes Hdagger H, not its neutral real component.
    cross = dimension*(2*kappa*sigma*sigma)*(2*rho*H)
    return {'source_dimension':dimension,'input_operators':['kappa*sigma^2*sum(A_i^2)','rho*(Hdagger H)*sum(A_i^2)'],
            'scalar_beta_times_16pi_squared':str(s.expand(cross)),
            'generated_sigma_squared_Higgs_coefficient':4*dimension,
            'derivation':'Cross Hessian trace Tr(H_kappa H_rho) in beta V=Tr(H_V^2)/2; only the source-source diagonal block overlaps.',
            'scope':'This specified scalar-loop contribution, not the entire portal beta.'}


def non_gaussian_matching_certificate():
    import sympy as s
    J,K,M,r3,r4,epsilon = s.symbols('J K M r3 r4 epsilon',real=True,nonzero=True)
    trial = -epsilon*J/M**2+epsilon**2*(J*K/M**4-r3*J**2/M**6)
    residual = s.expand((M*M+epsilon*K)*trial+r3*trial**2+r4*trial**3+epsilon*J)
    assert residual.coeff(epsilon,1)==residual.coeff(epsilon,2)==0
    return {'stationary_equation':'(M^2+K(q))*sigma+r3*sigma^2+r4*sigma^3+J(q)=0',
            'branch_condition':'V_sigma_sigma > 0 at the selected isolated stationary branch',
            'source_expansion_through_q_squared':str(trial.subs(epsilon,1)),
            'exact_local_heavy_masses':'M_f(q)=[m_f+h_f*sigma_star(q)] I',
            'exact_response':'partial_i M_f = -h_f V_sigma_qi/V_sigma_sigma * I',
            'all_order_tree_functional_relation':'h_down*(M_up-m_up I)-h_up*(M_down-m_down I)=0',
            'four_fermion_Lagrangian':'(sum_f h_f F_f)^2/(2*V_sigma_sigma)',
            'induced_source_metric':'I + grad_x[sigma_star(q(x))] grad_x[sigma_star(q(x))]^T; x are canonical real source coordinates, not the invariant labels q',
            'metric_rank':'At most one additional positive semidefinite source kinetic direction',
            'scope':'General local classical singlet matching on a positive-curvature branch. Higher-derivative and multi-fermion terms follow from the same classical functional. Not a finite one-loop EFT matching statement.'}


def non_gaussian_vacuum_extension():
    """All singlet self/portal structures, with exactly unchanged local jets."""
    import sympy as s
    t=s.Symbol('t',real=True);q=s.symbols('q0:9',real=True);q0=s.symbols('v0:9',real=True)
    k=list(map(s.Rational,['.03','.04','.005','.02','.035','.045','.004','.025','.05']))
    r3,r4=s.Rational(7,100),s.Rational(9,100)
    extra=r3*t**3/3+r4*t**4/4+t*t*sum(c*(a-b) for c,a,b in zip(k,q,q0))/2
    point={t:0,**dict(zip(q,q0))};variables=(t,*q)
    assert extra.subs(point)==0
    assert all(s.diff(extra,a).subs(point)==0 for a in variables)
    assert all(s.diff(extra,a,b).subs(point)==0 for a in variables for b in variables)
    assert all(k[4*i]*k[4*i+1]-(k[4*i+2]/2)**2>0 for i in range(2))
    return {'centered_singlet_coordinate':'t=sigma-sigma_vacuum',
            'extension':str(extra),'portal_coefficients':list(map(str,k)),
            'cubic_coefficient':str(r3),'quartic_coefficient':str(r4),
            'all_nine_source_Higgs_sigma_squared_coefficients_nonzero':True,
            'value_gradient_and_Hessian_change_at_retained_vacuum':'Exactly zero',
            'same_full_49_scalar_poles_and_quark_vertices':True,
            'boundedness_reason':'K(q) is nonnegative: both eta/trace forms have positive determinant, both adjoint norms and Hdagger H have positive coefficient. The quartic t^4 coefficient is positive. The subtracted K(q_vacuum)t^2 and cubic are bounded below by this positive quartic; the prior Gaussian-square/source potential is bounded below.',
            'scope':'Explicit local renormalizable extension with every newly identified singlet self/portal structure present. Centered contact coefficients preserve the chosen local branch; they are benchmark choices, not a new RG-invariant tuning or global-vacuum selection.'}


def fermion_effective_potential(spectra,scale=1.,colours=3):
    if not np.isfinite(scale) or scale<=0 or not isinstance(colours,int) or colours<1:
        raise ValueError('Positive finite scale and positive integer colour multiplicity required')
    result=0.
    for spectrum in spectra:
        masses=np.asarray(spectrum['masses'],float)
        if masses.shape!=(6,) or np.any(masses<=0) or not np.all(np.isfinite(masses)):
            raise ValueError('Six finite positive Dirac masses required')
        x=masses*masses
        result-=colours*np.sum(x*x*(np.log(x/(scale*scale))-1.5))/(16*np.pi*np.pi)
    return float(result)


def fixed_spectrum_orbit_certificate(benchmark):
    """Executable unitary orbit of the complete singlet-matched quark blocks."""
    from scipy.linalg import expm
    from .flavor_hermitian import block_spectrum
    from .nonet_potential import nonet_fields,operators
    from valentiner_adjoint_quartics import BASIS,quartic_projectors
    z=np.array(benchmark['source_coordinates']);P=np.array(quartic_projectors()[0])
    base_current=np.array(benchmark['singlet_source_current_coefficients'])
    base_q=np.r_[operators(z[:20],P)[0][:8],z[20]**2/2]
    fields=nonet_fields(z[:20]);base=[]
    for f,(eta,t,A) in enumerate(fields):
        m=benchmark['sector_thresholds'][f]['matched_heavy_mass']
        base.append(block_spectrum((.1*eta+.7*t)*np.eye(3)+.8*A,[1.2,.57][f],m,z[20]/np.sqrt(2)))
    energy=fermion_effective_potential(base);rows=[]
    for generator in BASIS:
        U=expm(.04j*generator);zz=z.copy();A=U@fields[1][2]@U.conj().T
        zz[12:20]=np.einsum('aij,ji->a',BASIS,A).real
        eta,t=fields[1][:2];m=benchmark['sector_thresholds'][1]['matched_heavy_mass']
        down=block_spectrum((.1*eta+.7*t)*np.eye(3)+.8*A,.57,m,z[20]/np.sqrt(2))
        V=base[0]['doublet_frame'].conj().T@down['doublet_frame']
        q=np.r_[operators(zz[:20],P)[0][:8],zz[20]**2/2]
        rows.append({'maximum_Dirac_mass_change':float(np.max(abs(down['masses']-base[1]['masses']))),
                     'source_current_change':float(base_current@(q-base_q)),
                     'fermion_CW_change':fermion_effective_potential([base[0],down])-energy,
                     'physical_quartet':float(np.imag(V[0,0]*V[1,1]*V[0,1].conjugate()*V[1,0].conjugate())),
                     'charged_current_squared':(abs(V)**2).tolist()})
    return {'baseline_fermion_CW':energy,'unitary_orbits_checked':len(rows),'orbits':rows,
            'exact_reason':'D(C rotated)=diag(U,U) D(C) diag(Udagger,Udagger). All singular masses are unchanged. Every source current singlet is unchanged independently in both sectors.',
            'theorem':'The full one-loop fermion determinant has zero orientation torque along fixed-eigenvalue source orbits, including the singlet-matched heavy masses.',
            'scope':'These are isospectral quark/source orbits, not stationary points of one fixed finite-group scalar potential. Scalar-loop energies and two-loop mixed graphs can depend on orientation.'}
