"""Numerical analytic periods and smooth conformal metrics on cyclic curves.

Optional numpy/scipy backend. Exact basis/normalization data remain independent.
Continuation uses analytic logarithms on circles, never pointwise root selection.
General quadrature/root error estimates are not rigorous interval certificates.
"""
import cmath,math
from fractions import Fraction as Q
from .holomorphic_basis import differential_basis


def pair(z):return [float(z.real),float(z.imag)]
def evaluate(coeff,x):
    result=0j
    for a in reversed(coeff):result=result*x+complex(float(Q(a)))
    return result

def derivative(coeff):return [str(Q(a)*i) for i,a in enumerate(coeff) if i]

class AnalyticSurface:
    def __init__(self,coefficients,d):
        import numpy as np
        self.packet=differential_basis(coefficients,d)
        self.n=self.packet['component_equation']['power']
        self.r=self.packet['component_equation']['monic_polynomial']
        self.forms=self.packet['forms_per_component']
        self.roots=[]
        for block in self.packet['geometry']['multiplicity_blocks']:
            f=block['monic_factor'];e=block['multiplicity']//self.packet['geometry']['components']
            values=np.roots([float(Q(a)) for a in reversed(f)])
            for z in values:self.roots.append((complex(z),e))
        self.roots.sort(key=lambda r:(round(r[0].real,12),round(r[0].imag,12)))
        sep=min((abs(a[0]-b[0]) for i,a in enumerate(self.roots) for b in self.roots[i+1:]),default=1.)
        residual=max((abs(evaluate(self.r,a)) for a,e in self.roots),default=0.)
        if sep<1e-7:raise ValueError('numerical distinct-root separation too small for this backend')
        self.root_diagnostics={'minimum_separation':sep,'polynomial_root_residual':residual,
                              'certified':False}

    def coefficients(self,x):
        r=evaluate(self.r,x)
        if abs(r)<1e-14:raise ValueError('use a branch-point local chart at a root')
        z=cmath.exp(cmath.log(r)/self.n)
        return [evaluate(f['numerator'],x)/z**f['character_j'] for f in self.forms]

    def metric(self,x):
        if not self.forms:raise ValueError('genus zero needs a separate rational/spherical chart')
        x=complex(x);r=evaluate(self.r,x);rp=evaluate(derivative(self.r),x)
        hs=self.coefficients(x);ds=[]
        z=cmath.exp(cmath.log(r)/self.n)
        for f,h in zip(self.forms,hs):
            ds.append(evaluate(derivative(f['numerator']),x)/z**f['character_j']-f['character_j']*rp/(self.n*r)*h)
        rho=sum(abs(h)**2 for h in hs)
        dh=sum(abs(a)**2 for a in ds);cross=sum(h.conjugate()*a for h,a in zip(hs,ds))
        numerator=rho*dh-abs(cross)**2
        curvature=-2*max(0.,numerator)/rho**3
        return {'x':pair(x),'density_in_x_chart':rho,'curvature':curvature,
                'curvature_numerator_roundoff':numerator,
                'metric':'sum |omega_i|^2 on one normalized complex component',
                'conformal_to_original_component':True,'numerically_evaluated':True,
                'normalization':'explicit monic component basis, not period-normalized Bergman metric'}

    def branch_metric(self,index):
        if not self.forms:raise ValueError('no positive differential metric in genus zero')
        a,e=self.roots[index];h=math.gcd(self.n,e);ram=self.n//h
        unit=1j**0
        for k,(b,r) in enumerate(self.roots):
            if k!=index:unit*=(a-b)**r
        rho=0.;orders=[]
        # Divide the exact numerator polynomial by (x-a)^k numerically. The
        # valuation formula fixes k; residuals from numerical a are diagnostics.
        import numpy as np
        for f in self.forms:
            j=f['character_j'];k=j*e//self.n
            if a==0j and Q(self.r[0])==0:k+=f['x_power']
            poly=np.array([complex(float(Q(v))) for v in reversed(f['numerator'])])
            for _ in range(k):poly,_=np.polydiv(poly,np.array([1.,-a]))
            order=(self.n*(j*e//self.n)+self.n-j*e)//h-1
            if a==0j and Q(self.r[0])==0:order+=ram*f['x_power']
            orders.append(order)
            if order==0:rho+=abs(ram*np.polyval(poly,a))**2/abs(unit)**(2*j/self.n)
        if rho<=0:raise AssertionError('basis metric should be positive in the branch chart')
        return {'root_index':index,'root':pair(a),'chart':'x=a+t^(n/gcd(n,e))',
                'density_at_t_zero':rho,'differential_orders':orders,'places':h}

    def infinity_metric(self):
        if not self.forms:raise ValueError('genus zero has no positive differential metric')
        delta=self.packet['geometry']['points_at_infinity_per_component'];scale=self.n/delta
        rho=sum(scale**2 for f in self.forms if f['order_at_each_infinity']==0)
        if rho<=0:raise AssertionError('metric not positive at infinity')
        return {'chart':'x=t^(-n/delta)','density_at_t_zero':rho,'places':delta,
                'orders':[f['order_at_each_infinity'] for f in self.forms]}

    def circle_period(self,center,radius,sheet=0,tolerance=1e-10):
        import numpy as np
        from scipy.integrate import quad_vec
        center=complex(center);radius=float(radius)
        if not math.isfinite(radius) or radius<=0 or type(sheet) is not int or not 0<=sheet<self.n:
            raise ValueError('positive finite radius and a component sheet index required')
        if not 0<tolerance<1:raise ValueError('tolerance must lie in (0,1)')
        inside=[];outside=[];margin=float('inf')
        for a,e in self.roots:
            dist=abs(center-a);margin=min(margin,abs(dist-radius))
            (inside if dist<radius else outside).append((a,e))
        if margin<1e-6*max(1.,radius):raise ValueError('contour touches or nearly touches a root')
        winding=sum(e for a,e in inside);turns=self.n//math.gcd(self.n,winding)
        def integrand(t):
            phase=cmath.exp(1j*t);x=center+radius*phase
            log_r=sum(e*(math.log(radius)+1j*t+cmath.log(1+(center-a)/radius/phase)) for a,e in inside)
            log_r+=sum(e*(cmath.log(center-a)+cmath.log(1+radius/(center-a)*phase)) for a,e in outside)
            log_z=log_r/self.n+2j*math.pi*sheet/self.n
            dx=1j*radius*phase
            return np.array([evaluate(f['numerator'],x)*cmath.exp(-f['character_j']*log_z)*dx for f in self.forms],dtype=complex)
        if self.forms:
            result,error=quad_vec(integrand,0.,2*math.pi*turns,epsabs=tolerance,epsrel=tolerance,limit=2000)
        else:result,error=[],0.
        return {'center':pair(center),'radius':radius,'sheet':sheet,'inside_multiplicity':winding,
                'turns_to_close_lift':turns,'closure_label':(turns*winding)%self.n,
                'period_vector':[pair(z) for z in result],'quadrature_error_estimate':float(error),
                'minimum_root_margin':margin,'root_diagnostics':self.root_diagnostics,
                'certified_error_bound':False,'symplectic_basis_claim':False,
                'scope':'periods of explicitly closed lifted circular contours; vectors may be redundant or zero'}

    def pair_periods(self,tolerance=1e-10):
        results=[]
        for i,(a,_) in enumerate(self.roots):
            for j,(b,_) in enumerate(self.roots[i+1:],i+1):
                c=(a+b)/2;r=abs(a-b)/2
                for factor in (1.07,1.13,1.21,1.31):
                    try:p=self.circle_period(c,r*factor,tolerance=tolerance);break
                    except ValueError:continue
                else:continue
                p['selected_pair']=[i,j];results.append(p)
        return results

    def word_period(self,word,tolerance=1e-10):
        """Closed lifted lollipop word; indices are signed ONE-BASED generators.

Commutators work even when no subset circle closes before n full turns.
Straight stems and local circles have explicit continuous logarithms.
"""
        import numpy as np
        from scipy.integrate import quad_vec
        if not self.roots:raise ValueError('nonconstant component required')
        if not word or any(type(k) is not int or not 1<=abs(k)<=len(self.roots) for k in word):
            raise ValueError('nonempty signed one-based root word required')
        winding=sum((1 if k>0 else -1)*self.roots[abs(k)-1][1] for k in word)
        if winding%self.n:raise ValueError('word does not close on the chosen component sheet')
        scale=max(1.,max(abs(a) for a,e in self.roots));base=complex(3*scale,4*scale)
        logs=[cmath.log(base-a) for a,e in self.roots];values=np.zeros(len(self.forms),complex);error=0.
        def form_value(x,ls,dx):
            logz=sum(e*l for (_,e),l in zip(self.roots,ls))/self.n
            return np.array([evaluate(f['numerator'],x)*cmath.exp(-f['character_j']*logz)*dx for f in self.forms],complex)
        def segment(a,b):
            nonlocal logs,values,error
            for root,e in self.roots:
                t=max(0.,min(1.,((root-a)/(b-a)).real));margin=abs(a+t*(b-a)-root)
                if margin<1e-7*scale:raise ValueError('stem crosses or nearly touches a root')
            initial=list(logs)
            def fn(t):
                x=a+t*(b-a);ls=[l+cmath.log((x-r)/(a-r)) for (r,e),l in zip(self.roots,initial)]
                return form_value(x,ls,b-a)
            if self.forms:
                v,err=quad_vec(fn,0,1,epsabs=tolerance,epsrel=tolerance,limit=1000);values+=v;error+=err
            logs=[l+cmath.log((b-r)/(a-r)) for (r,e),l in zip(self.roots,initial)]
        for entry in word:
            index=abs(entry)-1;direction=1 if entry>0 else -1;root,_=self.roots[index]
            separation=min((abs(root-a) for k,(a,e) in enumerate(self.roots) if k!=index),default=scale)
            radius=.18*separation;start=root+radius;segment(base,start)
            initial=list(logs)
            def local_log(k,t):
                a,e=self.roots[k];phase=cmath.exp(1j*t)
                if k==index:return math.log(radius)+1j*t
                return cmath.log(root-a)+cmath.log(1+radius/(root-a)*phase)
            offsets=[l-local_log(k,0) for k,l in enumerate(initial)]
            def circle_fn(t):
                phase=cmath.exp(1j*t);ls=[offsets[k]+local_log(k,t) for k in range(len(self.roots))]
                return form_value(root+radius*phase,ls,1j*radius*phase)
            end=direction*2*math.pi
            if self.forms:
                v,err=quad_vec(circle_fn,0,end,epsabs=tolerance,epsrel=tolerance,limit=1000);values+=v;error+=err
            logs=[offsets[k]+local_log(k,end) for k in range(len(self.roots))]
            segment(start,base)
        return {'word':list(word),'basepoint':pair(base),'period_vector':[pair(v) for v in values],
                'closure_label':winding%self.n,'quadrature_error_estimate':float(error),
                'certified_error_bound':False,'root_diagnostics':self.root_diagnostics,
                'symplectic_basis_claim':False,'scope':'explicit closed lifted root-loop word; analytic continuation throughout'}
