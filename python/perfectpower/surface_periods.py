"""Numerical periods along actual tree/cotree cycles of hyperelliptic curves.

The integral homology transform is exact. Chart locations, polynomial roots,
and analytic quadrature are numerical and are not certified error bounds.
"""
import cmath
import math
from .analytic_surface import AnalyticSurface,evaluate,pair
from .symplectic_surface import surface_basis,normalize_periods


class CycleIntegrator:
    def __init__(self,mesh,tolerance=1e-10,center_weights=(1/3,1/3,1/3)):
        import numpy as np
        if not math.isfinite(tolerance) or not 0<tolerance<1:raise ValueError('tolerance must lie in (0,1)')
        if 'face_inverse_chart' not in mesh:raise ValueError('mesh requires recorded analytic face charts; regenerate it')
        if len(center_weights)!=3 or any(not math.isfinite(w) or w<=0 for w in center_weights) or abs(sum(center_weights)-1)>1e-12:raise ValueError('positive center weights summing to one required')
        self.mesh=mesh;self.surface=AnalyticSurface(mesh['coefficients'],2);self.tolerance=tolerance
        self.coords=[None if z is None else complex(*z) for z in mesh['base_coordinates']]
        self.labels=mesh['vertex_chart_labels'];self.caps=mesh['face_inverse_chart']
        self.roots=[a for a,e in self.surface.roots]
        self.centers=[];self.logs=[]
        for tri,cap in zip(mesh['triangles'],self.caps):
            vertices=[self.coords[self.labels[v][0]] for v in tri]
            if cap:
                w=sum(weight*(0j if z is None else 1/z) for weight,z in zip(center_weights,vertices))
                if abs(w)<1e-12:raise ValueError('face center is at infinity')
                center=1/w
            else:center=sum(weight*z for weight,z in zip(center_weights,vertices))
            seed=next((v for v in tri if self.coords[self.labels[v][0]] is not None and
                      min(abs(self.coords[self.labels[v][0]]-r) for r in self.roots)>1e-7),None)
            if seed is None:raise ValueError('face has no regular finite anchor')
            base,sheet=self.labels[seed];z=self.coords[base]
            log=cmath.log(evaluate(self.surface.r,z))+2j*math.pi*sheet
            self.centers.append(center);self.logs.append(log+self.increment(z,center,cap,1.))
        self.zero=np.zeros(len(self.surface.forms),complex)
        self.cache={}

    def increment(self,a,b,cap,t):
        if cap:
            wa,wb=1/a,1/b;w=wa+t*(wb-wa)
            if abs(w)<1e-12:raise ValueError('inverse-chart segment crosses infinity')
            return sum(cmath.log((1-r*w)/(1-r*wa))-cmath.log(w/wa) for r in self.roots)
        x=a+t*(b-a)
        return sum(cmath.log((x-r)/(a-r)) for r in self.roots)

    def segment(self,a,b,cap,log):
        import numpy as np
        from scipy.integrate import quad_vec
        # Straight chart segments must miss roots and the inverse-chart origin.
        ca,cb=(1/a,1/b) if cap else (a,b)
        obstacle=[1/r for r in self.roots if r] if cap else self.roots
        if cap:obstacle=obstacle+[0j]
        delta=cb-ca
        clearance=min((abs(ca+max(0.,min(1.,((r-ca)*delta.conjugate()).real/abs(delta)**2))*delta-r)
                       for r in obstacle),default=1.) if delta else 1.
        if clearance<1e-10*max(1.,abs(ca),abs(cb)):raise ValueError('integration segment touches a chart singularity')
        def fn(t):
            z=ca+t*delta
            x=1/z if cap else z;dx=-delta/z**2 if cap else delta
            l=log+self.increment(a,b,cap,t)
            return np.array([evaluate(f['numerator'],x)*cmath.exp(-f['character_j']*l/2)*dx for f in self.surface.forms],complex)
        values,error=quad_vec(fn,0.,1.,epsabs=self.tolerance,epsrel=self.tolerance,limit=500)
        return values,float(error),log+self.increment(a,b,cap,1.),clearance

    def crossing(self,source,target,edge):
        # Reverse crossings are exact negatives of the cached forward values.
        key=(min(source,target),max(source,target),tuple(sorted(edge)))
        if key in self.cache:
            values,error,clearance=self.cache[key]
            return (values if source<target else -values),error,clearance
        a,b=[self.coords[self.labels[v][0]] for v in edge]
        if a is None or b is None:
            finite=b if a is None else a;mid=2*finite
        else:mid=(a+b)/2
        start=self.centers[source];end=self.centers[target];log=self.logs[source]
        v1,e1,log,c1=self.segment(start,mid,self.caps[source],log)
        v2,e2,log,c2=self.segment(mid,end,self.caps[target],log)
        # Check that the continued point lands on the actual target lift.
        residual=abs(cmath.exp((log-self.logs[target])/2)-1)
        if residual>1e-6:raise ValueError('continued crossing lands on the wrong mesh sheet')
        values=v1+v2;error=e1+e2;clearance=min(c1,c2)
        self.cache[key]=(values if source<target else -values,error,clearance)
        return values,error,clearance

    def cycle(self,walk):
        if not walk or walk[0][0]!=walk[-1][1] or any(x[1]!=y[0] for x,y in zip(walk,walk[1:])):
            raise ValueError('closed consecutive dual walk required')
        value=self.zero.copy();error=0.;clearance=float('inf')
        for a,b,edge in walk:
            if not set(edge)<=set(self.mesh['triangles'][a]) or not set(edge)<=set(self.mesh['triangles'][b]):
                raise ValueError('crossing edge is not shared by its faces')
            v,e,c=self.crossing(a,b,edge);value+=v;error+=e;clearance=min(clearance,c)
        return {'period_vector':[pair(z) for z in value],'quadrature_error_estimate':error,
                'minimum_chart_clearance':clearance,'sheet_transport_checked':True,
                'certified_error_bound':False}


def symplectic_period_matrix(mesh,tolerance=1e-10,center_weights=(1/3,1/3,1/3)):
    import numpy as np
    basis=surface_basis(mesh);integrator=CycleIntegrator(mesh,tolerance,center_weights)
    # Match the surface orientation to the holomorphic chart orientation.
    first=mesh['triangles'][0];cap=mesh['face_inverse_chart'][0]
    points=[integrator.coords[integrator.labels[v][0]] for v in first]
    points=[0j if z is None else 1/z for z in points] if cap else points
    orient=((points[1]-points[0]).conjugate()*(points[2]-points[0])).imag
    if orient*mesh['face_orientation_signs'][0]<=0:
        oriented=dict(mesh);oriented['face_orientation_signs']=[-s for s in mesh['face_orientation_signs']]
        basis=surface_basis(oriented)
    cycles=[integrator.cycle(w) for w in basis['dual_generator_cycles']]
    p=np.array([[complex(*z) for z in c['period_vector']] for c in cycles]).T
    normalized=normalize_periods(p,basis)
    if normalized['symmetry_residual']>1e-7 or not normalized['positive_imaginary_part']:raise ValueError('numerical Riemann period checks failed')
    basis['analytic_periods_computed']=True
    # First bilinear relation in the unreduced basis (independent of A inverse).
    omega=np.array(basis['intersection_matrix'],float)
    bilinear=p@np.linalg.solve(omega,p.T)
    hermitian=-1j*p@np.linalg.solve(omega,p.conjugate().T)
    scale=max(1.,float(np.linalg.norm(p)**2))
    return {'schema':'pp-analytic-symplectic-periods/1','coefficients':mesh['coefficients'],'genus':basis['genus'],
            'mesh_resolution':mesh['resolution'],'mesh_ring_count':mesh['ring_count'],
            'component_equation':integrator.surface.packet['component_equation'],'forms':integrator.surface.forms,
            'basis':basis,'cycles':cycles,'generator_periods':[[pair(z) for z in row] for row in p],
            **normalized,'first_bilinear_relative_residual':float(np.max(np.abs(bilinear))/scale),
            'second_bilinear_eigenvalues':list(map(float,np.linalg.eigvalsh((hermitian+hermitian.conjugate().T)/2))),
            'A_condition_number':float(np.linalg.cond(np.array([[complex(*z) for z in row] for row in normalized['A']]))),
            'tolerance':tolerance,'face_center_weights':list(center_weights),'root_diagnostics':integrator.surface.root_diagnostics,
            'integration_method':'continued analytic logarithms across finite and inverse charts along recorded dual-face cycles',
            'scope':'Original-curve numerical analytic integrals in an integral symplectic basis; neither root errors nor quadrature bounds are certified.'}


def integrate_path(coefficients,d,points,charts=None,sheet=0,tolerance=1e-10):
    """Integrate all basis forms along a finite, nonsingular continued-sheet path.

    Supports the normalized cyclic component, including repeated multiplicities.
    Explicit infinity endpoints and paths through ramification points are rejected.
    """
    import numpy as np
    from scipy.integrate import quad_vec
    s=AnalyticSurface(coefficients,d)
    if not math.isfinite(tolerance) or not 0<tolerance<1:raise ValueError('positive tolerance below one required')
    if type(sheet) is not int or not 0<=sheet<s.n:raise ValueError('component sheet index required')
    points=[complex(*z) if isinstance(z,(tuple,list)) else complex(z) for z in points]
    if len(points)<2 or any(not math.isfinite(z.real) or not math.isfinite(z.imag) for z in points):raise ValueError('at least two finite points required')
    charts=['x']*(len(points)-1) if charts is None else charts
    if len(charts)!=len(points)-1 or any(c not in ('x','inverse') for c in charts):raise ValueError('one x or inverse chart per segment required')
    if any(min(abs(z-r) for r,e in s.roots)<1e-10 for z in points):raise ValueError('path endpoint at a branch point')
    log=cmath.log(evaluate(s.r,points[0]))+2j*math.pi*sheet
    value=np.zeros(len(s.forms),complex);error=0.;clearance=float('inf')
    for a,b,chart in zip(points,points[1:],charts):
        cap=chart=='inverse'
        if cap and (a==0 or b==0):raise ValueError('inverse chart excludes x zero')
        ca,cb=(1/a,1/b) if cap else (a,b);delta=cb-ca
        if delta==0:continue
        obstacles=([1/r for r,e in s.roots if r]+[0j]) if cap else [r for r,e in s.roots]
        margin=min(abs(ca+max(0.,min(1.,((r-ca)*delta.conjugate()).real/abs(delta)**2))*delta-r) for r in obstacles)
        if margin<1e-10*max(1.,abs(ca),abs(cb)):raise ValueError('path segment meets a singularity')
        clearance=min(clearance,margin)
        def increment(t):
            z=ca+t*delta
            if cap:return sum(e*(cmath.log((1-r*z)/(1-r*ca))-cmath.log(z/ca)) for r,e in s.roots)
            return sum(e*cmath.log((z-r)/(a-r)) for r,e in s.roots)
        def fn(t):
            z=ca+t*delta;x=1/z if cap else z;dx=-delta/z**2 if cap else delta
            l=log+increment(t)
            return np.array([evaluate(f['numerator'],x)*cmath.exp(-f['character_j']*l/s.n)*dx for f in s.forms],complex)
        if s.forms:
            v,e=quad_vec(fn,0.,1.,epsabs=tolerance,epsrel=tolerance,limit=500);value+=v;error+=float(e)
        log+=increment(1.)
    principal=cmath.log(evaluate(s.r,points[-1]));winding=round((log-principal).imag/(2*math.pi))
    residual=abs(log-principal-2j*math.pi*winding)
    if residual>1e-6:raise ValueError('continuation residual exceeds tolerance')
    return {'period_vector':[pair(z) for z in value],'start_sheet':sheet,'end_sheet':winding%s.n,
            'endpoint':pair(points[-1]),'endpoint_log_polynomial':pair(log),
            'closed_lift':points[0]==points[-1] and winding%s.n==sheet,
            'quadrature_error_estimate':error,'continuation_residual':residual,
            'minimum_chart_clearance':None if math.isinf(clearance) else clearance,
            'root_diagnostics':s.root_diagnostics,'certified_error_bound':False,
            'component_equation':s.packet['component_equation'],'forms':s.forms}


def bergman_metric(periods,x):
    """Canonical density sum (Im tau)^-1_ij eta_i conjugate(eta_j).

    eta=A^-1 omega; area is genus with the usual (i/2) dz wedge dbarz convention.
    This evaluates the metric in a regular finite x chart, numerically.
    """
    import numpy as np
    from .analytic_surface import derivative
    s=AnalyticSurface(periods['coefficients'],2);x=complex(x)
    a=np.array([[complex(*z) for z in row] for row in periods['A']])
    tau=np.array([[complex(*z) for z in row] for row in periods['tau']]);y=tau.imag
    if np.max(np.abs(y-y.T))>1e-7 or np.min(np.linalg.eigvalsh((y+y.T)/2))<=0:raise ValueError('positive symmetric imaginary period matrix required')
    h=np.array(s.coefficients(x));r=evaluate(s.r,x);rp=evaluate(derivative(s.r),x);root=cmath.exp(cmath.log(r)/2)
    dh=np.array([evaluate(derivative(f['numerator']),x)/root**f['character_j']-f['character_j']*rp/(2*r)*v for f,v in zip(s.forms,h)])
    eta=np.linalg.solve(a,h);deta=np.linalg.solve(a,dh)
    inner=lambda u,v:np.vdot(u,np.linalg.solve(y,v))
    rho=float(inner(eta,eta).real);dd=float(inner(deta,deta).real);cross=inner(eta,deta)
    numerator=rho*dd-abs(cross)**2
    return {'x':pair(x),'density_in_x_chart':rho,'curvature':float(-2*max(0.,numerator)/rho**3),
            'curvature_numerator_roundoff':float(numerator),'normalized_differential_values':[pair(z) for z in eta],
            'total_area_theorem':s.packet['dimension_per_component'],
            'normalization':'canonical Bergman metric eta* (Im tau)^-1 eta; area g',
            'numerically_evaluated':True,'certified_error_bound':False}


def jacobian_coordinates(periods,path_integral):
    """Normalize an Abel integral and reduce in a lattice parallelepiped.

    Reduction is by lattice coefficients, not a closest-point computation.
    Caller must use the same curve, form ordering and component normalization.
    """
    import numpy as np
    a=np.array([[complex(*z) for z in row] for row in periods['A']])
    tau=np.array([[complex(*z) for z in row] for row in periods['tau']])
    values=np.array([complex(*z) for z in path_integral['period_vector']])
    if values.shape!=(periods['genus'],) or not np.isfinite(values).all():raise ValueError('matching finite form vector required')
    u=np.linalg.solve(a,values);b=np.linalg.solve(tau.imag,u.imag);aa=u.real-tau.real@b
    if not np.isfinite(aa).all() or not np.isfinite(b).all() or max(np.max(np.abs(aa)),np.max(np.abs(b)))>2**52:raise ValueError('lattice coefficients exceed reliable floating reduction range')
    integer_a=np.floor(aa).astype(int);integer_b=np.floor(b).astype(int)
    reduced=u-integer_a-tau@integer_b
    return {'normalized_integral':[pair(z) for z in u],'reduced_coordinates':[pair(z) for z in reduced],
            'removed_integer_A':list(map(int,integer_a)),'removed_integer_B':list(map(int,integer_b)),
            'real_lattice_coefficients':list(map(float,aa)),'imaginary_lattice_coefficients':list(map(float,b)),
            'reduction':'lattice parallelepiped, not nearest lattice vector','certified_error_bound':False}
