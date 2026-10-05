"""Explicit scalar completions, exact operator obstructions and numerical matching.

Exact results concern declared polynomial/operator spaces. Numerical loop and
Yukawa studies are local, scheme-specified examples, not an established UV model.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import cos, sin, pi, sqrt, log, gcd
from . import polyalg as P
from .core import mul, subtract, evaluate
from .cyclotomic_vacuum import (phase_potential, real_cyclotomic_polynomial,
    cyclotomic_polynomial, cosine_polynomials, fourier_coefficients)


def selected_potential(lock=0, selector=1):
    lock, selector = Q(lock), Q(selector)
    if lock < 0 or selector <= 0:
        raise ValueError('nonnegative lock and positive selector required')
    p = real_cyclotomic_polynomial(60)
    return P.add(P.scale(mul(p, p), lock),
                 P.scale(phase_potential(60, (-1, 3, 0, -1)), selector))


def remainder_record(polynomial):
    p = real_cyclotomic_polynomial(60)
    rem = P.divmod_poly(polynomial, p)[1]
    common = P.gcd_poly(p, rem)
    return {'coefficients': list(map(str, rem)), 'zero': P.is_zero(rem),
            'common_root_degree': P.degree(common)}


def bezout_carrier(polynomial):
    """Exact rational witness a*Psi60+b*remainder=gcd, normalized monic."""
    modulus=real_cyclotomic_polynomial(60)
    rem=P.divmod_poly(polynomial,modulus)[1]
    r0,r1=modulus,rem
    a0,a1,b0,b1=P.ONE,P.ZERO,P.ZERO,P.ONE
    while not P.is_zero(r1):
        q,r=P.divmod_poly(r0,r1)
        r0,r1=r1,r
        a0,a1=a1,subtract(a0,mul(q,a1))
        b0,b1=b1,subtract(b0,mul(q,b1))
    scale=1/r0[-1]
    return {'gcd':list(map(str,P.scale(r0,scale))),
            'carrier_multiplier':list(map(str,P.scale(a0,scale))),
            'remainder_multiplier':list(map(str,P.scale(b0,scale)))}


def exact_lock_family(lock=1, selector=1):
    v = selected_potential(lock, selector)
    p = real_cyclotomic_polynomial(60)
    q = P.poly((-1, 3, 0, -1))
    target = mul(p, P.add(P.scale(P.derivative(p), 2*Q(lock)), P.scale(q, Q(selector))))
    if P.derivative(v) != target:
        raise AssertionError('lock family identity failed')
    return {'lock': str(Q(lock)), 'selector': str(Q(selector)),
            'potential': list(map(str, v)),
            'derivative_factor': list(map(str, P.exact_div(P.derivative(v), p))),
            'stationarity': remainder_record(P.derivative(v)),
            'global_selection_argument': 'For lock>=0 and selector>0 the added square is nonnegative and vanishes at the previously certified unique x winner; the global winner is unchanged.',
            'physical_origin_of_coefficients': 'not derived'}


def angular_curvature_polynomial(v):
    # d^2 V(2 cos theta)/dtheta^2, represented without square roots.
    d = P.poly((4, 0, -1))
    return subtract(mul(d, P.derivative(P.derivative(v))), mul(P.X, P.derivative(v)))


def scalar_counterterm(lock=0, kappa=None, f=1, g=1):
    """Exact derivative of Tr(M^4) along the tree valley, modulo Psi60.

    Lambda^8 is omitted. f and g are positive rational kinetic scales in one
    reference unit. kappa=None is the angular-only scalar model. With kappa>0
    both angular and real-coefficient scalar eigenmasses are included.
    """
    f, g = Q(f), Q(g)
    if f <= 0 or g <= 0:
        raise ValueError('positive kinetic scales required')
    v = selected_potential(lock)
    h = angular_curvature_polynomial(v)
    if kappa is None:
        t = P.scale(mul(h, h), 1/f**4)
    else:
        k = Q(kappa)
        if k <= 0:
            raise ValueError('positive portal kappa required')
        d = P.poly((4, 0, -1))
        c = subtract(P.ONE, cosine_polynomials(12)[12])
        cp2 = mul(P.derivative(c), P.derivative(c))
        hh = P.add(h, P.scale(mul(d, cp2), 2*k))
        t = P.add(P.scale(mul(hh, hh), 1/f**4),
            P.add(P.scale(mul(d, cp2), 8*k*k/(f*f*g*g)), P.poly((4*k*k/g**4,))))
    rec = remainder_record(P.derivative(t))
    return {'lock': str(Q(lock)), 'kappa': None if kappa is None else str(Q(kappa)),
            'f': str(f), 'g': str(g), 'trace_mass_fourth_polynomial': list(map(str, t)),
            'trace_degree': P.degree(t), 'valley_torque_remainder': rec,
            'stationary_family_closed_under_this_divergence': rec['zero'],
            'bezout_witness':bezout_carrier(P.derivative(t)),
            'scope': 'scalar-only EFT divergent counterterm; nonzero remainder requires additional running coefficients. It is not a no-go theorem for models with extra fermions or symmetries.'}


def cyclic_operator_basis(max_degree=12, rotation_order=1):
    """Every CP-even monomial Re(z^a conjugate(z)^b), a>=b, total<=D."""
    if type(max_degree) is not int or not 1 <= max_degree <= 24 or type(rotation_order) is not int or rotation_order < 1:
        raise ValueError('invalid finite operator domain')
    ss = cosine_polynomials(max_degree)
    rows = []
    for total in range(1, max_degree+1):
        for b in range(total//2+1):
            a = total-b; harmonic = a-b
            if harmonic % rotation_order:
                continue
            angular = P.ONE if harmonic == 0 else P.scale(ss[harmonic], Q(1,2))
            rem = remainder_record(P.derivative(angular))
            rows.append({'z_power': a, 'conjugate_power': b, 'degree': total,
                         'harmonic': harmonic, 'stationarity': rem})
    support = (2,3,5,8,9,12)
    allowed_target = all(n % rotation_order == 0 for n in support)
    return {'max_degree': max_degree, 'rotation_order': rotation_order,
            'count': len(rows), 'rows': rows, 'target_support_allowed': allowed_target,
            'dangerous_count': sum(not r['stationarity']['zero'] for r in rows),
            'target_support_gcd': gcd(*support),
            'scope': 'one unit-modulus complex scalar, CP plus cyclic rephasing only; radial dependence retained as operator labels, evaluated at unit radius'}


def supersymmetric_circuit():
    """Cubic Wess-Zumino circuit; z_n=Z_n/M, Z_1=Z, D_a have R=2."""
    phi = cyclotomic_polynomial(60)
    fields = [f'Z{n}' for n in range(1,17)]
    drivers = [f'D{n}' for n in range(2,17)] + ['Dstar']
    terms = []
    for n in range(2,17):
        terms.extend([{'coefficient': 1, 'M_power': 1, 'fields': [f'D{n}', f'Z{n}']},
                      {'coefficient': -1, 'M_power': 0, 'fields': [f'D{n}', 'Z1', f'Z{n-1}']}])
    for n, a in enumerate(phi):
        if a:
            terms.append({'coefficient': int(a), 'M_power': 2 if n == 0 else 1,
                          'fields': ['Dstar'] if n == 0 else ['Dstar', f'Z{n}']})
    allowed = []
    # Complete pure-singlet holomorphic superpotential through field degree 3.
    # R(W)=2, R(D)=2, R(Z)=0 forces exactly one driver.
    for driver in drivers:
        for count in range(3):
            for neutral in combinations_with_replacement(fields, count):
                allowed.append({'driver': driver, 'neutral_fields': list(neutral),
                                'field_degree': 1+count, 'coefficient_mass_dimension': 2-count})
    return {'fields': [{'name': n, 'R_charge': 0, 'CP': 'complex conjugation', 'gauge': 'singlet'} for n in fields]
                     + [{'name': n, 'R_charge': 2, 'CP': 'complex conjugation', 'gauge': 'singlet'} for n in drivers],
            'superpotential_terms': terms, 'chosen_term_count': len(terms),
            'allowed_superpotential_count': len(allowed), 'allowed_superpotential': allowed,
            'effective_equation': list(map(str, phi)),
            'simple_roots': P.degree(P.gcd_poly(phi, P.derivative(phi))) == 0,
            'canonical_Kahler': 'sum |Z_n|^2 + sum |D_a|^2',
            'allowed_CP_even_quadratic_Kahler_real_parameters': 2*16*17//2,
            'vacua': [{'root_power': k, 'phase_degrees': 6*k, 'D': 0} for k in range(1,60) if gcd(k,60)==1],
            'perturbative_protection': 'F-flat zeros of the chosen Wilsonian W persist with nonsingular positive Kahler metric and exact global supersymmetry; the non-renormalization theorem does not select the initial 37 coefficients.',
            'energy_selection': 'all sixteen F-flat vacua have zero energy; no preferred CP sign or 66-degree vacuum is obtained',
            'scope': 'explicit renormalizable gauge-singlet sector, not a matched supersymmetric Standard Model; gravitational and nonperturbative completions absent'}


def circuit_jacobian(z, golden=False):
    import numpy as np
    j = np.zeros((16,16),dtype=complex)
    for n in range(2,17):
        j[n-2,n-1] = 1
        j[n-2,0] -= z**(n-1)
        j[n-2,n-2] -= z
    for n,a in enumerate(cyclotomic_polynomial(60)):
        if n:
            j[-1,n-1] = float(a)
    if golden:
        extended=np.zeros((17,17),complex)
        extended[:16,:16]=j
        extended[-1,3]=1; extended[-1,5]=1; extended[-1,13]=-1; extended[-1,16]=1
        return extended
    return j


def circuit_spectrum(golden=False):
    import numpy as np
    phi = cyclotomic_polynomial(60)
    rows = []
    for k in range(1,60):
        if gcd(k,60)!=1:
            continue
        z=np.exp(2j*pi*k/60); j=circuit_jacobian(z,golden)
        # Singular values squared are masses^2/M^2; each appears for two chiral multiplets.
        m2=np.linalg.svd(j,compute_uv=False)**2
        dp=sum(n*float(a)*z**(n-1) for n,a in enumerate(phi) if n)
        rows.append({'root_power': k, 'phase_degrees': 6*k,
            'F_residual': float(abs(sum(float(a)*z**n for n,a in enumerate(phi)))),
            'mass_squared_over_M_squared': sorted(map(float,m2)),
            'jacobian_determinant_over_Phi_prime': [float((np.linalg.det(j)/dp).real),float((np.linalg.det(j)/dp).imag)],
            'supertrace_M_fourth': float(4*np.sum(m2*m2)-4*np.sum(m2*m2))})
    return {'rows':rows,'count':len(rows),'chiral_field_count':34 if golden else 32,
            'degree_of_freedom_cancellation': 'For each Jacobian singular value, two chiral multiplets give four real bosonic modes and four fermionic spin modes with equal mass. Cancellation is at F=0 with exact SUSY.',
            'spectrum_is_numerical': True}


def holomorphic_coefficient_extension():
    """Two additional chiral fields T,Dgold with T=1-z^12-z^-12.

    z^-12=z^48 on Phi60=0. Reduction gives a linear expression in existing
    circuit fields. This supplies a real golden value at the SUSY zeros,
    without using a nonholomorphic Re(Z12) in the superpotential. It does not
    enforce any Yukawa Wilson-coefficient relation or lift the vacuum energies.
    """
    phi=cyclotomic_polynomial(60)
    z12=P.poly([0]*12+[1]); z48=P.poly([0]*48+[1])
    c=P.divmod_poly(subtract(subtract(P.ONE,z12),z48),phi)[1]
    identity=P.divmod_poly(P.add(subtract(mul(c,c),P.scale(c,3)),P.ONE),phi)[1]
    terms=[{'coefficient':1,'M_power':1,'fields':['Dgold','T']}]
    for n,a in enumerate(c):
        if a:
            terms.append({'coefficient':str(-a),'M_power':2 if n==0 else 1,
                          'fields':['Dgold'] if n==0 else ['Dgold',f'Z{n}']})
    return {'coefficient_polynomial':list(map(str,c)),
            'golden_identity_remainder':list(map(str,identity)),
            'additional_fields':[{'name':'T','R_charge':0},{'name':'Dgold','R_charge':2}],
            'additional_superpotential_terms':terms,'extended_chiral_field_count':34,
            'extended_allowed_pure_singlet_W_count':17*(1+17+17*18//2),
            'operator_relation':'T=1-z^12-z^48 modulo Phi60; T^2-3T+1=0 at F-flat zeros',
            'scope':'explicit holomorphic extension with chosen coefficients; T is real at unbroken-SUSY vacua. A generic deformed solution need not keep T real.'}


def allowed_circuit_deformation(epsilon):
    """A real Dstar tadpole is allowed by the declared CP and R symmetries."""
    import numpy as np
    eps=float(epsilon)
    if not np.isfinite(eps) or abs(eps)>.05:
        raise ValueError('small finite deformation required')
    coefficients=np.array(list(map(float,cyclotomic_polynomial(60))))
    coefficients[0]+=eps
    roots=np.polynomial.polynomial.polyroots(coefficients)
    reference=np.exp(1j*11*pi/30)
    z=roots[np.argmin(abs(roots-reference))]
    dp=sum(n*float(a)*reference**(n-1) for n,a in enumerate(cyclotomic_polynomial(60)) if n)
    dz=-eps/dp
    return {'epsilon':eps,'phase_degrees':float(np.degrees(np.angle(z))),
            'radius':float(abs(z)), 'linear_phase_displacement_degrees':float(np.degrees((dz/reference).imag)),
            'allowed_by_declared_symmetries':True,
            'interpretation':'independent change of the initialized superpotential, not a perturbatively generated W correction'}


def softened_circuit(z, epsilon):
    """Eliminate 15 auxiliary complex scalars exactly by linear least squares.

    D=0 is a consistent stationary slice because W is linear in D and the
    chosen scalar tadpoles involve only Z. V/M^4=||F_D||^2 + epsilon*
    sum a_n Re(Z_n/M), with the six specified Fourier weights. This is a
    nonsupersymmetric scalar deformation; it does not inherit F-flat protection.
    """
    import numpy as np
    z=complex(z)
    if not np.isfinite(z) or not np.isfinite(epsilon):
        raise ValueError('finite complex coordinate and soft strength required')
    # Unknowns Z2..Z16; Z1 is fixed. Rows are F_D2..F_D16,F_Dstar.
    a=np.zeros((16,15),complex); r=np.zeros(16,complex)
    for n in range(2,17):
        a[n-2,n-2]=1
        if n==2:
            r[0]=-z*z
        else:
            a[n-2,n-3]=-z
    for n,c in enumerate(cyclotomic_polynomial(60)):
        if n>=2:
            a[-1,n-2]=float(c)
    r[-1]=1
    weights=np.zeros(15)
    for n,c in enumerate(fourier_coefficients(selected_potential())):
        if n>=2:
            weights[n-2]=float(c)
    # Stable augmented least-squares particular solution, followed by the
    # analytic linear-tadpole response. Normal equations for the small response.
    baseline=np.linalg.lstsq(a,-r,rcond=None)[0]
    fields=baseline-epsilon/2*np.linalg.solve(a.conj().T@a,weights)
    residual=a@fields+r
    energy=float(np.vdot(residual,residual).real+epsilon*np.real(weights@fields))
    # Envelope theorem: derivative at optimized auxiliary fields; soft term
    # has no explicit z dependence in these coordinates.
    dz=np.zeros_like(a); dr=np.zeros_like(r)
    dr[0]=-2*z
    for n in range(3,17):
        dz[n-2,n-3]=-1
    direction=dz@fields+dr
    complex_gradient=np.vdot(residual,direction)
    gradient=np.array([2*complex_gradient.real,-2*complex_gradient.imag])
    return energy,gradient,np.r_[z,fields],float(np.max(abs(a.conj().T@residual+epsilon*weights/2)))


def soft_circuit_branches(epsilon):
    """Local minima continued from all sixteen SUSY vacua; no global claim."""
    import numpy as np
    from scipy.optimize import root
    if not 0<epsilon<=1e-3:
        raise ValueError('positive soft strength at most 1e-3 required')
    weights=np.zeros(16)
    for n,c in enumerate(fourier_coefficients(selected_potential())):
        if n:
            weights[n-1]=float(c)
    rows=[]
    for k in range(1,60):
        if gcd(k,60)!=1:
            continue
        z0=np.exp(2j*pi*k/60); j=circuit_jacobian(z0)
        displacement=-epsilon/2*np.linalg.solve(j.conj().T@j,weights)
        start=z0+displacement[0]
        def equations(q):
            return softened_circuit(q[0]+1j*q[1],epsilon)[1]
        sol=root(equations,[start.real,start.imag],tol=1e-11)
        e,g,fields,aux=softened_circuit(sol.x[0]+1j*sol.x[1],epsilon)
        if max(abs(g))>1e-9 or abs(fields[0]-z0)>.03:
            raise ArithmeticError('soft branch continuation left local controlled domain')
        step=1e-5
        h=np.column_stack([(equations(sol.x+step*np.eye(2)[i])-equations(sol.x-step*np.eye(2)[i]))/(2*step) for i in range(2)])
        phase=float(np.angle(fields[0])); initial=float(np.angle(z0))
        delta=float(np.angle(fields[0]/z0))
        holomorphic=2-fields[3]-fields[5]+fields[13]
        rows.append({'root_power':k,'initial_phase_degrees':initial*180/pi,
            'phase_degrees':phase*180/pi,'phase_displacement_degrees':delta*180/pi,
            'linear_phase_displacement_degrees':float(np.degrees((displacement[0]/z0).imag)),
            'radius':float(abs(fields[0])),'energy_over_M_fourth':e,
            'coefficient_from_angle':float(1-2*cos(12*phase)),
            'coefficient_from_auxiliary_operator':float(1-2*fields[11].real),
            'holomorphic_T':[float(holomorphic.real),float(holomorphic.imag)],
            'holomorphic_T_magnitude':float(abs(holomorphic)),
            'holomorphic_T_phase_degrees':float(np.degrees(np.angle(holomorphic))),
            'auxiliary_stationarity_residual':aux,'z_stationarity_residual':float(max(abs(g))),
            'positive_reduced_hessian':bool(np.linalg.eigvalsh((h+h.T)/2).min()>0)})
    # CP partners have equal energies within floating-point tolerance.
    best=min(r['energy_over_M_fourth'] for r in rows)
    winners=[r['root_power'] for r in rows if r['energy_over_M_fourth']<=best+max(1e-13,epsilon*1e-9)]
    return {'epsilon':epsilon,'branches':rows,'lowest_continued_branch_root_powers':winners,
            'scope':'explicit cubic circuit with selected linear scalar tadpoles; auxiliary fields minimized, both radial and phase shifts retained. These are local branch minima, not a global or loop-corrected SUSY-breaking vacuum census.'}


def circuit_field_tensors(fields, golden=True):
    """F_D, J=dF_D/dZ and quadratic-constraint Hessians at D=0."""
    import numpy as np
    fields=np.asarray(fields,dtype=complex)
    count=17 if golden else 16
    if fields.shape!=(count,) or not np.all(np.isfinite(fields)):
        raise ValueError('finite circuit coordinate vector required')
    f=np.zeros(count,complex); j=np.zeros((count,count),complex)
    h=np.zeros((count,count,count),complex)
    for n in range(2,17):
        row=n-2
        f[row]=fields[n-1]-fields[0]*fields[n-2]
        j[row,n-1]=1; j[row,0]-=fields[n-2]; j[row,n-2]-=fields[0]
        h[row,0,n-2]-=1; h[row,n-2,0]-=1
    f[15]=1
    for n,a in enumerate(cyclotomic_polynomial(60)):
        if n:
            f[15]+=float(a)*fields[n-1]; j[15,n-1]=float(a)
    if golden:
        f[-1]=fields[16]-2+fields[3]+fields[5]-fields[13]
        j[-1,16]=1; j[-1,3]=1; j[-1,5]=1; j[-1,13]=-1
    return f,j,h


def real_scalar_mass_matrix(a,b):
    """Canonical sqrt(2) Re/Im fields; a hermitian, b complex symmetric."""
    import numpy as np
    return np.block([[(a+b).real,-a.imag-b.imag],[a.imag-b.imag,(a-b).real]])


def circuit_loop(fields, coupling=.3, mu_squared=None, golden=True):
    """Full D=0 circuit one-loop potential and gradient in DRbar.

    The D scalar masses cancel half of the Weyl contributions. The retained
    trace is therefore sum over 2n Z real scalars minus twice sum over n
    eigenvalues of J^dagger J. This includes all 4n real scalars and 2n Weyl
    fields of the full circuit. Gauge fields are absent in this singlet sector.
    """
    import numpy as np
    if not 0<coupling<=1:
        raise ValueError('positive common superpotential coupling at most one required')
    f,j,tensors=circuit_field_tensors(fields,golden)
    a=j.conj().T@j; b=np.einsum('k,kij->ij',f.conj(),tensors)
    real=real_scalar_mass_matrix(a,b)
    av,aq=np.linalg.eigh(a); bv,bq=np.linalg.eigh(real)
    if min(av.min(),bv.min())<=0:
        raise ValueError('positive-mass local circuit patch required')
    g2=coupling**2
    if mu_squared is None:
        mu_squared=g2*float(np.exp(np.mean(np.log(av))))
    alog=np.log(g2*av/mu_squared); blog=np.log(g2*bv/mu_squared)
    value=float(g2*g2*(np.sum(bv*bv*(blog-1.5))-2*np.sum(av*av*(alog-1.5)))/(64*pi*pi))
    gradients=[]
    for direction in (1.,1j):
        for i in range(len(f)):
            dj=direction*tensors[:,:,i]
            df=direction*j[:,i]
            da=dj.conj().T@j+j.conj().T@dj
            db=np.einsum('k,kij->ij',df.conj(),tensors)
            dr=real_scalar_mass_matrix(da,db)
            ad=np.real(np.diag(aq.conj().T@da@aq))
            bd=np.real(np.diag(bq.T@dr@bq))
            gradients.append(float(g2*g2*(np.sum(bv*bd*(blog-1))-2*np.sum(av*ad*(alog-1)))/(32*pi*pi)))
    return value,np.array(gradients),real,g2*av,g2*bv,float(mu_squared)


def circuit_full_loop_value(fields,drivers,coupling,mu_squared):
    """Independent full 68-scalar / 34-Weyl expression, including D!=0."""
    import numpy as np
    f,j,tensors=circuit_field_tensors(fields)
    drivers=np.asarray(drivers,dtype=complex)
    if drivers.shape!=(17,):
        raise ValueError('seventeen driver coordinates required')
    fz=j.T@drivers
    zz=np.einsum('k,kij->ij',drivers,tensors)
    zero=np.zeros_like(j)
    fermion=np.block([[zz,j.T],[j,zero]])
    a=fermion.conj().T@fermion
    bzz=np.einsum('k,kij->ij',f.conj(),tensors)
    bzd=np.einsum('j,kji->ik',fz.conj(),tensors)
    b=np.block([[bzz,bzd],[bzd.T,zero]])
    bosons=np.linalg.eigvalsh(real_scalar_mass_matrix(a,b))
    fermions=np.linalg.eigvalsh(a)
    if min(bosons.min(),fermions.min())<=0:
        raise ValueError('full circuit positive-mass patch required')
    g2=coupling**2
    return float(g2*g2*(np.sum(bosons*bosons*(np.log(g2*bosons/mu_squared)-1.5))
                       -2*np.sum(fermions*fermions*(np.log(g2*fermions/mu_squared)-1.5)))/(64*pi*pi))


def driver_quantum_hessian(fields,coupling,mu_squared,step=2e-4):
    """Complete driver block by energy differences and its unbroken R symmetry.

    At D=0 the common driver phase rotation forces a hermitian quadratic form,
    equal real/imaginary diagonal blocks, and an antisymmetric cross block.
    Cross terms between neutral and driver fields vanish by the same symmetry.
    """
    import numpy as np
    zero=np.zeros(17,complex)
    baseline=circuit_full_loop_value(fields,zero,coupling,mu_squared)
    xx=np.zeros((17,17)); xy=np.zeros((17,17))
    basis=np.eye(17,dtype=complex)*step
    def energy(d):return circuit_full_loop_value(fields,d,coupling,mu_squared)
    for i in range(17):
        xx[i,i]=2*(energy(basis[i])-baseline)/step**2
        for k in range(i+1,17):
            xx[i,k]=xx[k,i]=(energy(basis[i]+basis[k])-energy(basis[i]-basis[k]))/(2*step**2)
            xy[i,k]=(energy(basis[i]+1j*basis[k])-energy(basis[i]-1j*basis[k]))/(2*step**2)
            xy[k,i]=-xy[i,k]
    _,j,_=circuit_field_tensors(fields)
    ad=j.conj()@j.T
    tree=2*coupling**2*real_scalar_mass_matrix(ad,np.zeros_like(ad))
    correction=np.block([[xx,xy],[-xy,xx]])
    return tree+correction,correction


def circuit_quantum_minimum(epsilon,coupling=.3):
    """One-loop local continuation of the selected +66-degree circuit branch."""
    import numpy as np
    from scipy.optimize import root
    branch=soft_circuit_branches(epsilon)
    classical=next(r for r in branch['branches'] if r['root_power']==11)
    z=classical['radius']*np.exp(1j*classical['phase_degrees']*pi/180)
    _,_,fields,_=softened_circuit(z,epsilon)
    t=2-fields[3]-fields[5]+fields[13]
    fields=np.r_[fields,t]
    weights=np.zeros(17)
    for n,a in enumerate(fourier_coefficients(selected_potential())):
        if n:
            weights[n-1]=float(a)
    def pack(q):return np.r_[q.real,q.imag]
    def unpack(q):return q[:17]+1j*q[17:]
    def tree_gradient(q):
        f,j,_=circuit_field_tensors(q)
        gradient=j.conj().T@f+epsilon*weights/2
        return coupling**2*np.r_[2*gradient.real,2*gradient.imag]
    value,loop_gradient,real,av,bv,mu2=circuit_loop(fields,coupling)
    linear=-np.linalg.solve(2*coupling**2*real,loop_gradient)
    def equations(q):
        complex_fields=unpack(q)
        return tree_gradient(complex_fields)+circuit_loop(complex_fields,coupling,mu2)[1]
    sol=root(equations,pack(fields)+linear,tol=1e-10)
    residual=float(np.max(abs(equations(sol.x))))
    if residual>1e-8 or np.max(abs(sol.x-pack(fields)))>.03:
        raise ArithmeticError('full-circuit one-loop continuation not controlled')
    corrected=unpack(sol.x)
    final_loop,_,_,af,bf,_=circuit_loop(corrected,coupling,mu2)
    step=2e-5
    quantum_hessian=np.column_stack([(equations(sol.x+step*np.eye(34)[i])-equations(sol.x-step*np.eye(34)[i]))/(2*step) for i in range(34)])
    quantum_eigenvalues=np.linalg.eigvalsh((quantum_hessian+quantum_hessian.T)/2)
    if quantum_eigenvalues.min()<=0:
        raise ArithmeticError('corrected Z-sector stationary point is not a local minimum')
    driver_hessian,driver_correction=driver_quantum_hessian(corrected,coupling,mu2)
    driver_eigenvalues=np.linalg.eigvalsh(driver_hessian)
    if driver_eigenvalues.min()<=0:
        raise ArithmeticError('corrected driver sector is not a local minimum')
    phase=float(np.degrees(np.angle(corrected[0])))
    phi_shift=float(np.degrees(np.angle(corrected[0]/fields[0])))
    # Linear one-loop energy evaluated at each classical root is enough to
    # compare the leading perturbative energy corrections among all branches.
    energies=[]
    for row in branch['branches']:
        zr=row['radius']*np.exp(1j*row['phase_degrees']*pi/180)
        _,_,q,_=softened_circuit(zr,epsilon)
        q=np.r_[q,2-q[3]-q[5]+q[13]]
        lv=circuit_loop(q,coupling,mu2)[0]
        energies.append({'root_power':row['root_power'],'tree_plus_one_loop_energy':coupling**2*row['energy_over_M_fourth']+lv})
    best=min(x['tree_plus_one_loop_energy'] for x in energies)
    winners=[x['root_power'] for x in energies if x['tree_plus_one_loop_energy']<=best+max(1e-13,coupling**2*epsilon*1e-8)]
    return {'epsilon':epsilon,'common_W_coupling':coupling,'chiral_fields':34,
        'real_scalar_modes':68,'Weyl_fermion_modes':34,'mu_squared_over_M_squared':mu2,
        'classical_phase_degrees':classical['phase_degrees'],'corrected_phase_degrees':phase,
        'quantum_phase_displacement_degrees':phi_shift,
        'classical_T':[float(t.real),float(t.imag)],
        'corrected_T':[float(corrected[-1].real),float(corrected[-1].imag)],
        'corrected_T_magnitude':float(abs(corrected[-1])),
        'corrected_T_phase_degrees':float(np.degrees(np.angle(corrected[-1]))),
        'linear_field_displacement_max':float(max(abs(linear))),
        'actual_field_displacement_max':float(max(abs(sol.x-pack(fields)))),
        'tree_plus_one_loop_stationarity_residual':residual,
        'all_tree_scalar_masses_positive_at_corrected_point':bool(bf.min()>0),
        'corrected_Z_sector_hessian_minimum':float(quantum_eigenvalues.min()),
        'quantum_hessian_symmetry_residual':float(np.max(abs(quantum_hessian-quantum_hessian.T))),
        'corrected_driver_hessian_minimum':float(driver_eigenvalues.min()),
        'driver_quantum_hessian_difference_step':2e-4,
        'driver_quantum_correction_operator_norm':float(np.linalg.norm(driver_correction,2)),
        'full_local_quantum_hessian_positive':True,
        'one_loop_value_at_classical_minimum':value,'one_loop_value_at_corrected_minimum':final_loop,
        'leading_branch_energy_comparison':energies,'lowest_leading_branch_root_powers':winners,
        'scope':'all singlet scalar/fermion modes in a local one-loop DRbar calculation; canonical renormalized Kahler metric and chosen scalar tadpoles at the stated scale. Neutral and driver quantum Hessians are numerically positive; their cross block vanishes by the declared unbroken R symmetry. Global minimization and quark/gauge thresholds are not established.'}


def angular_derivatives(theta, lock=0, max_order=4):
    f=fourier_coefficients(selected_potential(str(lock)))
    return [sum(float(a)*n**r*cos(n*theta+r*pi/2) for n,a in enumerate(f)
                if r==0 or n) for r in range(max_order+1)]


def scalar_loop(theta, ratio, mu_factor=1, lock=0):
    """MSbar scalar-only one-loop correction divided by Lambda^4; f=1.

    mu=mu_factor*m_tree(theta0), Lambda/f=ratio; finite extra Wilson
    coefficients are set to zero at this mu. Only positive-curvature patches.
    """
    if ratio<=0 or mu_factor<=0:
        raise ValueError('positive scale ratios required')
    u=angular_derivatives(theta,lock)
    h0=angular_derivatives(11*pi/30,lock)[2]
    if u[2]<=0 or h0<=0:
        raise ValueError('local positive-mass patch required')
    logarithm=log(u[2]/(h0*mu_factor**2))
    a=ratio**4/(64*pi*pi)
    value=a*u[2]**2*(logarithm-1.5)
    gradient=2*a*u[2]*u[3]*(logarithm-1)
    curvature=2*a*((u[3]**2+u[2]*u[4])*(logarithm-1)+u[3]**2)
    return value,gradient,curvature


def scalar_loop_minimum(ratio,mu_factor=1,lock=0):
    from scipy.optimize import root_scalar
    theta0=11*pi/30
    h=angular_derivatives(theta0,lock)[2]
    slope=scalar_loop(theta0,ratio,mu_factor,lock)[1]
    linear=-slope/h
    sol=root_scalar(lambda t: angular_derivatives(t,lock)[1]+scalar_loop(t,ratio,mu_factor,lock)[1],
                    x0=theta0,x1=theta0+1e-5,xtol=1e-13)
    if not sol.converged or abs(sol.root-theta0)>.1:
        raise ArithmeticError('local loop minimum not controlled')
    c0=1-2*cos(12*theta0); c=1-2*cos(12*sol.root)
    curvature=angular_derivatives(sol.root,lock)[2]+scalar_loop(sol.root,ratio,mu_factor,lock)[2]
    return {'Lambda_over_f':ratio,'mu_over_tree_mass':mu_factor,'lock':float(lock),
            'phase_degrees':sol.root*180/pi, 'linear_displacement_degrees':linear*180/pi,
            'actual_displacement_degrees':(sol.root-theta0)*180/pi,
            'coefficient':c,'relative_coefficient_change':(c-c0)/c0,
            'loop_corrected_angular_curvature':curvature,
            'local_stationarity_residual':angular_derivatives(sol.root,lock)[1]+scalar_loop(sol.root,ratio,mu_factor,lock)[1],
            'scope':'local positive-mass scalar-only MSbar example with zero finite extra coefficients at stated mu; changing mu with this boundary reset changes the theory, not a physical scale dependence'}


def joint_tree(theta,coefficient,kappa,lock=0):
    import numpy as np
    u=angular_derivatives(theta,lock)
    c=1-2*cos(12*theta); c1=24*sin(12*theta); c2=288*cos(12*theta); c3=-3456*sin(12*theta)
    r=coefficient-c; k=float(kappa)
    gradient=np.array([u[1]-2*k*r*c1,2*k*r])
    h=np.array([[u[2]+2*k*c1*c1-2*k*r*c2,-2*k*c1],[-2*k*c1,2*k]])
    dh=np.array([[[u[3]+6*k*c1*c2-2*k*r*c3,-2*k*c2],[-2*k*c2,0]],
                  [[-2*k*c2,0],[0,0]]])
    return u[0]+k*r*r,gradient,h,dh


def joint_loop(theta,coefficient,ratio,kappa,g_over_f=1,mu_squared=None,lock=0):
    import numpy as np
    if min(ratio,kappa,g_over_f)<=0:
        raise ValueError('positive model parameters required')
    value,gradient,h,dh=joint_tree(theta,coefficient,kappa,lock)
    metric=np.diag([1.,1./g_over_f])
    m=ratio**4*metric@h@metric
    masses,vectors=np.linalg.eigh(m)
    if np.any(masses<=0):
        raise ValueError('joint positive-mass patch required')
    if mu_squared is None:
        mu_squared=float(np.sqrt(np.prod(masses)))
    logarithms=np.log(masses/mu_squared)
    loop_value=float(np.sum(masses*masses*(logarithms-1.5))/(64*pi*pi*ratio**4))
    loop_gradient=[]
    for derivative in dh:
        dm=ratio**4*metric@derivative@metric
        eigen_derivative=np.real(np.diag(vectors.conj().T@dm@vectors))
        loop_gradient.append(float(np.sum(masses*eigen_derivative*(logarithms-1))/(32*pi*pi*ratio**4)))
    return loop_value,np.array(loop_gradient),masses,float(mu_squared)


def joint_loop_minimum(ratio,kappa,g_over_f=1,lock=0):
    import numpy as np
    from scipy.optimize import root
    t0=11*pi/30; c0=1-2*cos(12*t0)
    h=joint_tree(t0,c0,kappa,lock)[2]
    _,gradient,masses,mu2=joint_loop(t0,c0,ratio,kappa,g_over_f,lock=lock)
    linear=-np.linalg.solve(h,gradient)
    def equations(q):
        return joint_tree(q[0],q[1],kappa,lock)[1]+joint_loop(q[0],q[1],ratio,kappa,g_over_f,mu2,lock)[1]
    sol=root(equations,np.array([t0,c0])+linear,tol=1e-11)
    residual=float(np.max(abs(equations(sol.x))))
    if residual>1e-9 or abs(sol.x[0]-t0)>.1 or abs(sol.x[1]-c0)>.2:
        raise ArithmeticError('joint local minimum not controlled')
    step=1e-5
    jac=np.column_stack([(equations(sol.x+step*np.eye(2)[i])-equations(sol.x-step*np.eye(2)[i]))/(2*step) for i in range(2)])
    return {'Lambda_over_f':ratio,'kappa':kappa,'g_over_f':g_over_f,'lock':lock,
            'mu_squared_over_f_squared':mu2,'tree_mass_squared_over_f_squared':list(map(float,masses)),
            'phase_degrees':float(sol.x[0]*180/pi),'coefficient':float(sol.x[1]),
            'linear_displacements':[float(linear[0]),float(linear[1])],
            'relative_coefficient_change':float((sol.x[1]-c0)/c0),
            'departure_from_tree_coefficient_portal':float(sol.x[1]-1+2*cos(12*sol.x[0])),
            'positive_local_hessian':bool(np.linalg.eigvalsh((jac+jac.T)/2).min()>0),
            'stationarity_residual':residual,
            'scope':'both scalar loops in a local MSbar EFT with declared kinetic scales and boundary coefficients; excludes circuit multiplets and quark loops; no global loop minimum claim'}


FLAVOR_CHARGES=((1,1),(0,1),(0,0))


def yukawa_operator_basis(max_extra_fields=3,neutral_fields=16):
    """Complete Q_i H f^c_j holomorphic sector to W field degree 3+budget.

    q(Q_i)=q_i, q(f^c_i)=-q_i, A=(-1,0), B=(0,-1),
    all Z_n neutral. R(Q)=R(f^c)=1, R(H,A,B,Z)=0.
    Up and down sectors have independent real CP-even Wilson coefficients.
    Does not enumerate other gauge sectors, lepton interactions or higher K.
    """
    if type(max_extra_fields) is not int or not 0<=max_extra_fields<=3 or type(neutral_fields) is not int or not 1<=neutral_fields<=17:
        raise ValueError('invalid finite operator domain')
    out=[]
    neutrals=[f'Z{n}' for n in range(1,min(neutral_fields,16)+1)]+(['T'] if neutral_fields==17 else [])
    for species in ('up','down'):
        for i,qi in enumerate(FLAVOR_CHARGES):
            for j,qj in enumerate(FLAVOR_CHARGES):
                a,b=(qi[k]-qj[k] for k in range(2))
                if min(a,b)<0 or a+b>max_extra_fields:
                    continue
                for count in range(max_extra_fields-a-b+1):
                    for zs in combinations_with_replacement(neutrals,count):
                        out.append({'sector':species,'row':i+1,'column':j+1,
                            'A_power':a,'B_power':b,'neutral_fields':list(zs),
                            'superpotential_field_degree':3+a+b+count,
                            'independent_CP_even_coefficient':True})
    return {'max_superpotential_field_degree':3+max_extra_fields,'neutral_field_count':neutral_fields,
            'count':len(out),'operators':out,'charges':{'Q':list(FLAVOR_CHARGES),'u_c_and_d_c':[[-a,-b] for a,b in FLAVOR_CHARGES],'A':[-1,0],'B':[0,-1],'Z_n':[0,0]},
            'golden_relation_enforced':False,
            'counterexample':'The coefficients of Q1 H d3^c A B, Q1 H d2^c A and Q2 H d3^c B are independent. Neutral Z insertions are also allowed in both sectors.',
            'leading_allowed_Kahler_counterexamples':['Q1_dagger Q2 A_dagger / M + h.c.','Q2_dagger Q3 B_dagger / M + h.c.','Q1_dagger Q3 A_dagger B_dagger / M^2 + h.c.'],
            'scope':'complete specified Yukawa operator sector; flavor charges are formal global selection rules, not an anomaly-free gauged flavor model. A and B magnitudes remain free background/modulus inputs.'}


def triangular_yukawas(a,b,c,phase,up_spectrum=(1e-5,.003,.9),down_spectrum=(2e-5,4e-4,.02)):
    import numpy as np
    u=np.asarray(up_spectrum,dtype=float); d=np.asarray(down_spectrum,dtype=float)
    if u.shape!=(3,) or d.shape!=(3,) or np.any(u<=0) or np.any(d<=0) or min(a,b,c)<0 or not np.all(np.isfinite([a,b,c,phase])):
        raise ValueError('positive spectra and finite nonnegative texture inputs required')
    y=np.diag(d).astype(complex)
    y[0,1]=a*d[1]; y[1,2]=b*d[2]; y[0,2]=c*a*b*np.exp(-1j*phase)*d[2]
    return np.diag(u).astype(complex),y


def ckm_from_yukawas(yu,yd):
    import numpy as np
    matrices=[]; spectra=[]
    for y in (yu,yd):
        y=np.asarray(y,dtype=complex)
        if y.shape!=(3,3) or not np.all(np.isfinite(y)):
            raise ValueError('finite 3x3 Yukawa matrices required')
        values,u=np.linalg.eigh(y@y.conj().T)
        if np.min(np.diff(values))<=1e-18:
            raise ValueError('distinct ordered masses required')
        matrices.append(u); spectra.append(np.sqrt(np.maximum(values,0)))
    return matrices[0].conj().T@matrices[1],spectra


def physical_chart(V):
    import numpy as np
    from .flavor_prediction import observables
    v=np.asarray(V,dtype=complex)
    if v.shape!=(3,3) or np.max(abs(v@v.conj().T-np.eye(3)))>1e-9:
        raise ValueError('unitary CKM required')
    u,b,w=map(float,(abs(v[0,1]),abs(v[1,2]),abs(v[0,2])))
    c13=sqrt(1-w*w); s12=u/c13; s23=b/c13
    c12=sqrt(1-s12*s12); c23=sqrt(1-s23*s23)
    j=float(observables(v)['J'])
    if min(w,s12,s23)<=1e-14:
        delta=None
    else:
        cosd=(s12*s12*s23*s23+c12*c12*c23*c23*w*w-abs(v[2,0])**2)/(2*s12*s23*c12*c23*w)
        sind=j/(c12*c23*c13*c13*s12*s23*w)
        delta=float(np.degrees(np.arctan2(sind,np.clip(cosd,-1,1))))
    obs={k:float(x) for k,x in observables(v).items()}
    obs.update({'Vus':u,'Vcb':b,'depth':w*(1-w*w)/(u*b),'delta_degrees':delta})
    return obs


def matched_texture(c,vus,vcb,phase=11*pi/30):
    import numpy as np
    from scipy.optimize import root
    def objective(p):
        a,b=np.exp(p)
        v,_=ckm_from_yukawas(*triangular_yukawas(a,b,c,phase))
        return [abs(v[0,1])-vus,abs(v[1,2])-vcb]
    sol=root(objective,np.log([vus/sqrt(1-vus*vus),vcb]),tol=1e-11)
    if np.max(np.abs(objective(sol.x)))>1e-10:
        raise ArithmeticError('anchor matching failed')
    a,b=np.exp(sol.x); yu,yd=triangular_yukawas(a,b,c,phase)
    v,spectra=ckm_from_yukawas(yu,yd)
    return {'independent_13_coefficient':float(c),'a':float(a),'b':float(b),
            'observables':physical_chart(v),'singular_values':[list(map(float,s)) for s in spectra],
            'anchor_residual':list(map(float,objective(sol.x))),
            'scope':'selected allowed triangular Yukawa texture; up off-diagonal and most neutral insertions initialized to zero, not forbidden; only a,b are matched to Vus,Vcb; no fit to Vub or CP observables'}


def sm_one_loop(yu,yd,ye,gauge):
    """dY/dln(mu), left-row convention; g1 has SU(5) normalization."""
    import numpy as np
    yu,yd,ye=map(lambda x:np.asarray(x,dtype=complex),(yu,yd,ye))
    gauge=np.asarray(gauge,dtype=float)
    if any(y.shape!=(3,3) or not np.all(np.isfinite(y)) for y in (yu,yd,ye)) or gauge.shape!=(3,) or np.any(gauge<0):
        raise ValueError('three finite Yukawa matrices and nonnegative gauge couplings required')
    hu,hd,he=(y@y.conj().T for y in (yu,yd,ye))
    tr=float(np.trace(3*hu+3*hd+he).real)
    g1,g2,g3=gauge
    alpha=(tr-17/20*g1*g1-9/4*g2*g2-8*g3*g3,
           tr-1/4*g1*g1-9/4*g2*g2-8*g3*g3,
           tr-9/4*g1*g1-9/4*g2*g2)
    betas=((1.5*(hu-hd)+alpha[0]*np.eye(3))@yu,
           (1.5*(hd-hu)+alpha[1]*np.eye(3))@yd,
           (1.5*he+alpha[2]*np.eye(3))@ye)
    return tuple(b/(16*pi*pi) for b in betas),np.array([41/10,-19/6,-7])*gauge**3/(16*pi*pi)


def sm_running_example(vus,vcb):
    import numpy as np
    from scipy.integrate import solve_ivp
    from .flavor_prediction import ckm_from_depth
    c=(3-sqrt(5))/2
    v=ckm_from_depth(c,11*pi/30,vus,vcb)
    spectra=((1e-5,.003,.9),(2e-5,4e-4,.02),(3e-6,.0006,.01))
    matrices=[np.diag(spectra[0]).astype(complex),v@np.diag(spectra[1]),np.diag(spectra[2]).astype(complex)]
    gauge=np.array([.46,.65,1.17])
    def pack(ys,gs):
        flat=np.concatenate([y.ravel() for y in ys])
        return np.r_[flat.real,flat.imag,gs]
    def unpack(state):
        return [(state[:27]+1j*state[27:54])[i*9:(i+1)*9].reshape(3,3) for i in range(3)],state[54:]
    def rhs(t,state):
        ys,gs=unpack(state); bs,bg=sm_one_loop(*ys,gs)
        return pack(bs,bg)
    ratios=np.array([1.,10.,1e2,1e4,1e6,1e8])
    times=np.log(ratios)
    sol=solve_ivp(rhs,(0,float(times[-1])),pack(matrices,gauge),t_eval=times,rtol=2e-10,atol=1e-13)
    if not sol.success:
        raise ArithmeticError(sol.message)
    rows=[]
    for scale,state in zip(ratios,sol.y.T):
        ys,gs=unpack(state); vk,ss=ckm_from_yukawas(*ys[:2]); obs=physical_chart(vk)
        rows.append({'mu_over_mu0':float(scale),'gauge_couplings':list(map(float,gs)),
                     'observables':obs,'relative_depth_change':float(obs['depth']/c-1),
                     'phase_displacement_degrees':float(obs['delta_degrees']-66),
                     'singular_values':[list(map(float,s)) for s in ss]})
    return {'initial_spectra':[list(s) for s in spectra],'initial_gauge':list(map(float,gauge)),
            'rows':rows,'function_evaluations':sol.nfev,
            'scope':'illustrative unbroken-SM one-loop running from prescribed initial matrices; not measured inputs, threshold-matched data or RG of the 32-field SUSY circuit. No physical matching scale is supplied.'}
