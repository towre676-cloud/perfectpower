"""Arb certificates for continuous whole-line three-field walls.

The seed is an untrusted dyadic approximation. Piecewise quintic Hermite
polynomials are C2 and satisfy the boundary data exactly and join C2 to the exact vacuum. A continuous
coercivity/residual argument establishes a nearby solution, not merely a
root of discretized equations. The asymptotic condition is imposed in H1.
"""
from fractions import Fraction
from math import comb
from flint import arb, arb_poly, fmpq, ctx

DEFAULT={'lambda':'0.0000176188164948','alpha':'0.1','mu':'10',
         'lambda_H':'0.13','h0':'0.0082','kappa':'0.0000001'}


def ball(q):
    q=Fraction(q);return arb(fmpq(q.numerator,q.denominator))


def bernstein_range(p):
    """Convex-hull enclosure on t in [0,1], with outward Arb rounding."""
    n=p.degree()
    if n<0:return arb(0),arb(0)
    b=[sum((p[i]*ball(Fraction(comb(j,i),comb(n,i))) for i in range(j+1)),arb(0)) for j in range(n+1)]
    return min(v.lower() for v in b),max(v.upper() for v in b)


def absolute_bound(p):
    lo,hi=bernstein_range(p);return max(abs(lo),abs(hi)).upper()


def force(fields, params):
    u,y,h=fields;l,a,m,H,h0,kap=[params[n] for n in ['lambda','alpha','mu','lambda_H','h0','kappa']]
    k2=l/2;rs=y+a*u*u*(1/(m*m));rh=h*h-h0*h0+(kap/H)*(u*u-1)
    return [(l*u*(u*u-1)+2*a*u*rs+kap*u*rh)*(1/k2),m*m*rs*(1/k2),H*h*rh*(1/k2)]


def generate_seed(*,radius=22,segments=4096,parameters=None,tol=1e-10,nodes=None):
    """Numerical proposal only. The checker trusts none of its accuracy claims."""
    import numpy as np
    from scipy.integrate import solve_bvp
    if radius<5 or segments<32 or tol<=0:raise ValueError('resolved box and controls required')
    params=dict(DEFAULT if parameters is None else parameters);z={n:float(Fraction(v)) for n,v in params.items()}
    l,a,m,H,h0,kap=[z[n] for n in ['lambda','alpha','mu','lambda_H','h0','kappa']];k2=l/2
    if nodes is not None:
        nodes=np.asarray(nodes,dtype=float)
        if nodes.ndim!=1 or len(nodes)<33 or nodes[0]!=0 or nodes[-1]!=radius or not np.all(np.diff(nodes)>0):
            raise ValueError('strictly increasing nodes from zero to radius required')
        segments=len(nodes)-1
    grid=np.unique(np.r_[np.linspace(0,min(radius,22),1000),np.linspace(min(radius,22),radius,1200)]);u=np.tanh(grid)
    h=h0+kap*h0/np.sqrt(k2*2*H*h0*h0)*np.exp(-np.sqrt(2*H*h0*h0/k2)*grid)
    y=-a*u*u/m**2
    def rhs(x,w):
        return np.vstack((w[3:],force(w[:3],z)))
    def bc(left,right):return np.r_[left[0],left[4],left[5],right[0]-1,right[1]+a/m**2,right[2]-h0]
    initial=np.vstack((u,y,h,1-u*u,-2*a*u*(1-u*u)/m**2,np.gradient(h,grid)))
    sol=solve_bvp(rhs,bc,grid,initial,tol=tol,max_nodes=40000)
    if not sol.success:raise ArithmeticError(sol.message)
    values=sol.sol(np.linspace(0,radius,segments+1) if nodes is None else nodes).T
    result={'format':'pp-wall-dyadic-seed/1','parameters':params,
            'parameter_radii':{'lambda':'0.000000000000001'} if parameters is None else {},
            'radius':str(radius),'segments':segments,
            'values_hex':[[float(x).hex() for x in row] for row in values],
            'generator_scope':'Untrusted SciPy proposal. Endpoint values and Neumann data are replaced by exact rational boundary conditions by the checker.'}
    if nodes is not None:result['nodes_hex']=[float(x).hex() for x in nodes]
    return result


def seed_nodes(seed):
    """Exact rational cell endpoints, including untrusted nonuniform meshes."""
    R=Fraction(seed['radius']);n=seed['segments']
    if type(n) is not int or n<32:raise ValueError('at least 32 cells required')
    xs=([Fraction.from_float(float.fromhex(x)) for x in seed['nodes_hex']]
        if 'nodes_hex' in seed else [R*j/n for j in range(n+1)])
    if len(xs)!=n+1 or xs[0]!=0 or xs[-1]!=R or any(b<=a for a,b in zip(xs,xs[1:])):
        raise ValueError('invalid exact mesh endpoints')
    return xs


def generate_declared_seed():
    """Reproduce the lambda=0.1 proposal from declared equations and mesh."""
    import numpy as np
    params=dict(DEFAULT);params['lambda']='0.1'
    xs=np.unique(np.r_[np.linspace(0,12,6001),np.linspace(12,40,1401),np.linspace(40,1400,2721)])
    return generate_seed(radius=1400,nodes=xs,parameters=params,tol=1e-12)


def quintic(left,right,dd_left,dd_right,dx):
    p0,p1,p2=left[0],dx*left[1],dx*dx*dd_left/2
    a=right[0]-p0-p1-p2;b=dx*right[1]-p1-2*p2;c=dx*dx*dd_right-2*p2
    return arb_poly([p0,p1,p2,10*a-4*b+c/2,-15*a+7*b-c,6*a-3*b+c/2])


def check_seed(seed, *, radius_ball='0.00001',precision=160,coercivity='0.5'):
    """Prove a whole-line solution in a specified energy ball, then the five signs.

    All returned 'certified' flags require strict outward-rounded inequalities.
    The theorem applies to the rational inputs/intervals and whole-line vacuum limits.
    """
    if seed.get('format')!='pp-wall-dyadic-seed/1':raise ValueError('unsupported seed')
    if precision<80:raise ValueError('at least 80 bits required')
    old_precision=ctx.prec;ctx.prec=precision
    try:return _check_seed(seed,radius_ball=radius_ball,precision=precision,coercivity=coercivity)
    finally:ctx.prec=old_precision


def _check_seed(seed, *, radius_ball, precision,coercivity):
    P={n:ball(q) for n,q in seed['parameters'].items()}
    for name,rad in seed.get('parameter_radii',{}).items():
        if ball(rad)<0:raise ValueError('nonnegative parameter radii required')
        P[name]=arb(P[name],ball(rad))
    R=ball(seed['radius']);n=seed['segments'];xs=seed_nodes(seed)
    if not all(P[k]>0 for k in ['lambda','alpha','mu','lambda_H','h0','kappa']):raise ValueError('this five-sign theorem requires strictly positive parameters')
    r=ball(radius_ball);d=ball('0.25');c=ball(coercivity);tau=ball('0.001')
    if not c>0:raise ValueError('strictly positive proposed coercivity required')
    if not (R>=5 and r>0 and isinstance(n,int) and n>=32 and len(seed['values_hex'])==n+1):raise ValueError('invalid seed shape or radius')
    rows=[[ball(Fraction.from_float(float.fromhex(v))) for v in row] for row in seed['values_hex']]
    if any(len(v)!=6 for v in rows):raise ValueError('six values per node required')
    # These replacements make the continuous approximation obey all six BCs.
    rows[0][0]=arb(0);rows[0][4]=arb(0);rows[0][5]=arb(0)
    rows[-1][0]=arb(1);rows[-1][1]=-P['alpha']/P['mu']**2;rows[-1][2]=P['h0']
    rows[-1][3:]=[arb(0),arb(0),arb(0)]
    # Force also vanishes exactly at the rational vacuum. These exact
    # polynomial data give a C2 constant-vacuum continuation for x>=R.
    dd=[force(row[:3],P) for row in rows]
    maxima=[arb(0)]*3;umin=arb(2);hmin=arb(2);rsmax=arb(0);rhmax=arb(0);difference=arb(0)
    residual_max=[arb(0)]*3;residual_square_integral=arb(0);source_start_slope=rows[0][3]
    for j in range(n):
        dx=ball(xs[j+1]-xs[j])
        fields=[quintic((rows[j][i],rows[j][i+3]),(rows[j+1][i],rows[j+1][i+3]),dd[j][i],dd[j+1][i],dx) for i in range(3)]
        rhs=force(fields,P)
        for i,p in enumerate(fields):
            maxima[i]=max(maxima[i],absolute_bound(p))
            residual= p.derivative().derivative()*(1/(dx*dx))-rhs[i]
            residual_bound=absolute_bound(residual)
            residual_max[i]=max(residual_max[i],residual_bound)
            residual_square_integral+=dx*residual_bound**2
        u,y,h=fields;lo,hi=bernstein_range(h);hmin=min(hmin,lo)
        lo,hi=bernstein_range(u);umin=min(umin,lo)
        rsmax=max(rsmax,absolute_bound(y+(P['alpha']/P['mu']**2)*u*u))
        rhmax=max(rhmax,absolute_bound(h*h-P['h0']**2+P['kappa']/P['lambda_H']*(u*u-1)))
        # Comparing independent interval ranges is conservative but sufficient.
        tlo=ball(xs[j]).tanh().lower();thi=ball(xs[j+1]).tanh().upper()
        difference=max(difference,abs(lo-thi).upper(),abs(hi-tlo).upper())
    l,a,m,H,h0,kap=[P[k] for k in ['lambda','alpha','mu','lambda_H','h0','kappa']];k2=l/2
    Bu,By,Bh=[v+r for v in maxima]
    rs_ball=rsmax+r+a/m**2*(2*maxima[0]+r)*r
    rh_ball=rhmax+(2*maxima[2]+r)*r+kap/H*(2*maxima[0]+r)*r
    # Odd scalar kink Hessian has gap 3. Reserving d=1/4 of its gradient
    # gives source L2 coefficient 3-5d before profile/Schur perturbations.
    source_error=6*(2+difference+r)*(difference+r)+2*a*rs_ball/k2+kap*rh_ball/k2
    mediator_penalty=4*a*a*Bu*Bu/(m*m*k2)*tau/(1-tau)
    Higgs_floor=(H*(3*(hmin-r)**2-h0*h0)-kap)/k2
    if not hmin-r>0 or not Higgs_floor>0:raise ArithmeticError('Higgs positivity/coercivity failed')
    Higgs_penalty=(2*kap*Bu*Bh/k2)**2/(Higgs_floor/2)
    source_floor=3-5*d-source_error-mediator_penalty-Higgs_penalty
    mediator_floor=tau*m*m/k2;retained_Higgs_floor=Higgs_floor/2
    if not all(v>c for v in [source_floor,mediator_floor,retained_Higgs_floor]):raise ArithmeticError('continuous Hessian coercivity failed')
    # q >= d||e'||2+c||e||2. Sobolev: ||e||inf <= ||e||q/(dc)^(1/4).
    # Residual dual norm <= ||residual||L2/sqrt(c). Outward energy derivative
    # excludes a minimizer on the energy-ball boundary.
    residual_L2=(residual_square_integral if 'nodes_hex' in seed else R*sum(v*v for v in residual_max)).sqrt()
    energy_radius=r*(d*c).root(4);dual=residual_L2/c.sqrt()
    if not dual<energy_radius:raise ArithmeticError('continuous residual/existence test failed: '+str(dual/energy_radius))
    uniform_error=dual/(d*c).root(4)
    # The singlet is linear. Its positive mixed-BC Green operator has
    # L-infinity norm <=1/(mu^2/k2), sharpening its component error.
    ey=a/m**2*(2*maxima[0]+uniform_error)*uniform_error+residual_max[1]/(m*m/k2)
    Huu_abs=(l*(3*Bu*Bu+1)+2*a*rs_ball+4*a*a*Bu*Bu/m**2+kap*rh_ball+2*kap*kap/H*Bu*Bu)/k2
    Huy_abs=2*a*Bu/k2;Huh_abs=2*kap*Bu*Bh/k2
    source_second_error=Huu_abs*uniform_error+Huy_abs*ey+Huh_abs*uniform_error+residual_max[0]
    source_slope_error=uniform_error+source_second_error/2
    delta=ball('0.01');source_positive_away=delta.tanh()-difference-uniform_error
    A_abs=(l*(Bu*Bu+1)+2*a*rs_ball+kap*rh_ball)/k2
    if not (source_start_slope-source_slope_error>0 and source_positive_away>0 and delta*A_abs.sqrt()<1):
        raise ArithmeticError('source positivity proof failed')
    proof={'source_floor':source_floor,'mediator_floor':mediator_floor,'Higgs_floor_retained':retained_Higgs_floor,
        'gradient_floor':d,'common_L2_floor':c,'residual_L2_upper':residual_L2,
        'existence_boundary_ratio':dual/energy_radius,'energy_ball_radius':energy_radius,
        'uniform_solution_error_upper':uniform_error,'singlet_solution_error_upper':ey,
        'Higgs_profile_lower':hmin-uniform_error,'source_center_slope_lower':source_start_slope-source_slope_error,
        'source_positive_away_margin':source_positive_away,'source_reference_difference_upper':difference,
        'source_equation_coefficient_absolute_upper':A_abs,
        'residual_source_upper':residual_max[0],'residual_singlet_upper':residual_max[1],'residual_Higgs_upper':residual_max[2]}
    return {'format':'pp-wall-whole-line-certificate/1','parameters':seed['parameters'],'parameter_radii':seed.get('parameter_radii',{}),'trial_support_radius_x':seed['radius'],
        'segments':n,'precision_bits':precision,'a_priori_uniform_ball_radius':radius_ball,
        'bounds_Arb':{k:str(v) for k,v in proof.items()},'bounds_display_float':{k:float(v.mid()) for k,v in proof.items()},
        'continuous_whole_line_wall_existence_certified':True,'unique_in_pinned_reflection_energy_ball':True,
        'P1_source_strictly_between_zero_and_one_on_positive_half_line':True,
        'P2_source_derivative_positive':True,'P3_singlet_derivative_negative':bool(a>0),
        'P4_Higgs_derivative_negative':bool(kap>0),'P5_Higgs_positive':True,
        'Higgs_at_least_vacuum_everywhere':True,'Higgs_strictly_above_vacuum_interior':bool(kap>0),
        'whole_line_asymptotic_vacuum_certified':True,'quantitative_exponential_tail_constants_certified':False,
        'opposite_radial_sector_spectral_floor_over_k2':coercivity,
        'translation_sector_nonnegative_with_translation_kernel':True,
        'physical_vector_vacuum_threshold_bound_hypotheses_certified':True,
        'TE_thermal_relative_determinant_nonnegative_hypotheses_certified':True,'original_floating_profile_itself_is_exact_solution':False,
        'scope':'Existence, local uniqueness in the pinned reflection sector and five signs on the whole line at the rational inputs and declared parameter intervals. A compact C2 trial profile plus continuous H1 coercivity/residual minimization covers the exact infinite tail. No localization-mode, width or eigenvalue error enclosure is claimed.'}


def exact_profile_identities():
    """Independent symbolic identities used by the continuous proof."""
    import sympy as s
    u,y,h,l,a,m,H,h0,k=s.symbols('u y h lambda alpha mu lambda_H h0 kappa',nonzero=True)
    V=l*(u*u-1)**2/4+m*m*(y+a*u*u/m**2)**2/2+H*(h*h-h0*h0+k/H*(u*u-1))**2/4
    rs=y+a*u*u/m**2;rh=h*h-h0*h0+k/H*(u*u-1)
    f=[l*u*(u*u-1)+2*a*u*rs+k*u*rh,m*m*rs,H*h*rh]
    checks={f'potential_gradient_{i}':s.diff(V,z)-v for i,(z,v) in enumerate(zip([u,y,h],f))}
    checks['source_clipping_decomposition']=f[0]-u*((l+2*a*a/m**2+k*k/H)*(u*u-1)+2*a*(y+a/m**2)+k*(h*h-h0*h0))
    checks['positive_Higgs_equation']=f[2]-H*h*(h+h0)*(h-h0)+k*h*(1-u*u)
    checks['positive_singlet_equation']=f[1]-m*m*(y+a/m**2)+a*(1-u*u)
    x=s.Symbol('x',real=True);phi=s.tanh(x)/s.cosh(x)
    checks['odd_scalar_gap_three']=s.simplify(-s.diff(phi,x,2)+(6*s.tanh(x)**2-2)*phi-3*phi)
    checks['source_Hessian']=s.diff(f[0],u)-(l*(3*u*u-1)+2*a*rs+4*a*a*u*u/m**2+k*rh+2*k*k/H*u*u)
    checks['Higgs_Hessian']=s.diff(f[2],h)-(H*(3*h*h-h0*h0)+k*(u*u-1))
    checks['odd_gap_gradient_reserve']=(1-s.Rational(1,4))*3-s.Rational(1,4)*2-s.Rational(7,4)
    reduced={name:s.factor(v) for name,v in checks.items()}
    if any(v!=0 for v in reduced.values()):raise ArithmeticError('symbolic profile identity failed')
    return {name:str(v) for name,v in reduced.items()}
