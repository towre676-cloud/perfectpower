"""Exact conformal geometry: N/sqrt(D), connections, flows and domain bridges.

Symbolic compilation and source validation use SymPy; evaluation arithmetic and
rational interval operations use the standard library. Chart domains are never inferred from
cancellation of a coordinate pole. Continuous-flow existence uses the classical
Picard contraction theorem; its full analytic implementation is not Lean proved.
"""
from fractions import Fraction as Q
from math import isqrt
from hashlib import sha256
import json
from . import bernstein_boxes as B
from .euclid_geometry import rational
from .divisor_square import WorkLimit


def digest(obj):return sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def _poly(terms):
    rows=list(terms.items()) if isinstance(terms,dict) else list(terms)
    if isinstance(terms,dict):rows=[(i,j,c) for (i,j),c in rows]
    return B.poly([(i,j,rational(c)) for i,j,c in rows])

def _sp():
    import sympy as s
    return s,s.symbols('x y',real=True)

def _expr(p,s,x,y):return sum((s.Rational(c.numerator,c.denominator)*x**i*y**j for (i,j),c in p.items()),s.S.Zero)

def _encode_expr(expr,s,x,y):
    poly=s.Poly(s.expand(expr),x,y,domain=s.QQ)
    if len(poly.terms())>4096:raise WorkLimit('symbolic monomial limit')
    return B.encode({ij:Q(str(c)) for ij,c in poly.terms()})

def _rf(expr,s,x,y):
    n,d=s.fraction(s.cancel(expr));return {'numerator':_encode_expr(n,s,x,y),'denominator':_encode_expr(d,s,x,y)}

def _rf_expr(r,s,x,y):return _expr(_poly(r['numerator']),s,x,y)/_expr(_poly(r['denominator']),s,x,y)

def _eval(r,x,y):
    den=B.evaluate(_poly(r['denominator']),x,y)
    if not den:raise ValueError('rational expression pole')
    return B.evaluate(_poly(r['numerator']),x,y)/den

def compile_metric(numerator,denominator_squared,*,provenance=None):
    N,D=_poly(numerator),_poly(denominator_squared)
    if not N or not D:raise ValueError('nonzero metric numerator and squared denominator required')
    if any(i+j>64 for i,j in set(N)|set(D)):raise WorkLimit('input total degree exceeds 64')
    s,(x,y)=_sp();n,d=_expr(N,s,x,y),_expr(D,s,x,y)
    square=s.cancel(n*n/d)
    grad=[s.cancel(s.diff(square,z)/(2*square)) for z in (x,y)]
    hessian=[[s.cancel(s.diff(g,z)) for z in (x,y)] for g in grad]
    lap=s.cancel(hessian[0][0]+hessian[1][1])
    # C[k][i][j] in the usual convention: q''=-C(q',q').
    C=[[[s.cancel(((grad[i] if k==j else 0)+(grad[j] if k==i else 0)-(grad[k] if i==j else 0))/2)
          for j in range(2)] for i in range(2)] for k in range(2)]
    return {'schema':'pp-conformal-dynamics/1','numerator':B.encode(N),'denominator_squared':B.encode(D),
            'density':'N/sqrt(D), admitted only where N>0 and D>0',
            'log_gradient':[_rf(g,s,x,y) for g in grad],
            'log_hessian':[[_rf(h,s,x,y) for h in row] for row in hessian],
            'connection':[[[_rf(c,s,x,y) for c in row] for row in plane] for plane in C],
            'curvature_times_density':_rf(-lap/2,s,x,y),'density_squared':_rf(square,s,x,y),
            'provenance':provenance,'kernel_checked':False,
            'scope':'exact rational connection, geodesic acceleration and linearized flow for the supplied positive conformal chart; no automatic global chart or trajectory claim'}

def hyperelliptic_metric(coefficients,chart='finite',branch=None):
    from .metric_boxes import chart_density
    data=chart_density([rational(c) for c in coefficients],chart,branch)
    return compile_metric(data['numerator'],data['denominator_modulus_squared'],provenance=data)

def check_metric(packet):
    expected=compile_metric(packet['numerator'],packet['denominator_squared'],provenance=packet['provenance'])
    if packet!=expected:raise ValueError('metric compilation mismatch')
    if packet['provenance'] is not None:
        p=packet['provenance']
        if p.get('coefficients') is not None:
            from .metric_boxes import chart_density
            if p!=chart_density(p['coefficients'],p['chart'],p['branch']):raise ValueError('curve chart source mismatch')
    return True

def _point_data(packet,p):
    if len(p)!=2:raise ValueError('two chart coordinates required')
    x,y=map(rational,p);N=B.evaluate(_poly(packet['numerator']),x,y);D=B.evaluate(_poly(packet['denominator_squared']),x,y)
    if N<=0 or D<=0:raise ValueError('point outside positive metric domain')
    g=[_eval(r,x,y) for r in packet['log_gradient']]
    h=[[_eval(r,x,y) for r in row] for row in packet['log_hessian']]
    return x,y,N,D,g,h

def sqrt_interval(value,bits=64):
    value=rational(value)
    if value<0 or type(bits) is not int or not 1<=bits<=256:raise ValueError('nonnegative value and precision 1..256 required')
    n,d=isqrt(value.numerator),isqrt(value.denominator)
    if n*n==value.numerator and d*d==value.denominator:return Q(n,d),Q(n,d)
    scale=1<<bits;k=isqrt(value.numerator*scale*scale//value.denominator)
    lo=Q(k,scale);hi=lo if lo*lo==value else Q(k+1,scale)
    return lo,hi

def evaluate_metric(packet,p,*,bits=64):
    check_metric(packet)
    x,y,N,D,g,h=_point_data(packet,p);lo,hi=sqrt_interval(D,bits)
    if not lo:raise WorkLimit('precision too low for reciprocal square root')
    rho=(N/hi,N/lo);krho=_eval(packet['curvature_times_density'],x,y)
    K=IDiv((krho,krho),rho)
    return {'point':[str(x),str(y)],'density_interval':list(map(str,rho)),
            'curvature_interval':list(map(str,K)),'curvature_times_density':str(krho),
            'log_gradient':list(map(str,g)),'log_hessian':[list(map(str,row)) for row in h],
            'scope':'exact rational/dyadic enclosures at one admitted chart point','kernel_checked':False}

def acceleration(packet,p,velocity):
    _,_,_,_,g,_=_point_data(packet,p);u,v=map(rational,velocity);gx,gy=g
    return ((v*v-u*u)*gx/2-u*v*gy,(u*u-v*v)*gy/2-u*v*gx)

def connection_action(packet,p,v,z):
    _,_,_,_,g,_=_point_data(packet,p);v,z=list(map(rational,v)),list(map(rational,z))
    if len(v)!=2 or len(z)!=2:raise ValueError('two-vector arguments required')
    dot=lambda a,b:sum((x*y for x,y in zip(a,b)),Q(0))
    return tuple((dot(g,v)*z[i]+dot(g,z)*v[i]-dot(v,z)*g[i])/2 for i in range(2))

def geodesic_jacobian(packet,p,velocity):
    _,_,_,_,g,h=_point_data(packet,p);u,v=map(rational,velocity);gx,gy=g
    return [[Q(0),Q(0),Q(1),Q(0)],[Q(0),Q(0),Q(0),Q(1)],
            [(v*v-u*u)*h[0][i]/2-u*v*h[1][i] for i in range(2)]+[-u*gx-v*gy,v*gx-u*gy],
            [(u*u-v*v)*h[1][i]/2-u*v*h[0][i] for i in range(2)]+[u*gy-v*gx,-v*gy-u*gx]]

def dynamics(packet,p,velocity,*,transport=None,variation=None,momentum=None,bits=64):
    u,v=map(rational,velocity);a=acceleration(packet,p,(u,v));jac=geodesic_jacobian(packet,p,(u,v))
    result={'metric':evaluate_metric(packet,p,bits=bits),'geodesic_acceleration':list(map(str,a)),
            'flow_jacobian':[list(map(str,row)) for row in jac],
            'geodesic_energy_rate_divided_by_density':'0','kernel_checked':False}
    if transport is not None:
        z=list(map(rational,transport));rate=tuple(-q for q in connection_action(packet,p,(u,v),z))
        result['parallel_transport_rate']=list(map(str,rate));result['transport_norm_rate_divided_by_density']='0'
    if variation is not None:
        if len(variation)!=4:raise ValueError('position/velocity variation requires four entries')
        eta=list(map(rational,variation));result['variation_rate']=[str(sum((a*b for a,b in zip(row,eta)),Q(0))) for row in jac]
    if momentum is not None:
        if len(momentum)!=2:raise ValueError('two momentum coordinates required')
        pvec=list(map(rational,momentum));rho=tuple(map(Q,result['metric']['density_interval']));inv=IDiv((Q(1),Q(1)),rho)
        _,_,_,_,grad,_=_point_data(packet,p);norm=sum(q*q for q in pvec)
        result['hamiltonian_interval']=list(map(str,IMul((norm/2,norm/2),inv)))
        result['hamiltonian_position_rates']=[list(map(str,IMul((q,q),inv))) for q in pvec]
        result['hamiltonian_momentum_rates']=[list(map(str,IMul((norm*g/2,norm*g/2),inv))) for g in grad]
    return result

# Exact outward rational interval operations.
def IAdd(a,b):return a[0]+b[0],a[1]+b[1]
def INeg(a):return -a[1],-a[0]
def IMul(a,b):
    v=[x*y for x in a for y in b];return min(v),max(v)
def IDiv(a,b):
    if b[0]<=0<=b[1]:raise ValueError('interval denominator crosses zero')
    return IMul(a,(1/b[1],1/b[0]))
def IPow(a,n):
    if n==0:return Q(1),Q(1)
    if n%2:return a[0]**n,a[1]**n
    v=(a[0]**n,a[1]**n);return (Q(0) if a[0]<=0<=a[1] else min(v),max(v))
def _interval_poly(p,box):
    out=(Q(0),Q(0))
    for (i,j),c in _poly(p).items():out=IAdd(out,IMul((c,c),IMul(IPow(box[0],i),IPow(box[1],j))))
    return out

def _interval_rf(r,box):return IDiv(_interval_poly(r['numerator'],box),_interval_poly(r['denominator'],box))

def _ode_interval(packet,box):
    g=[_interval_rf(r,box) for r in packet['log_gradient']];h=[[_interval_rf(r,box) for r in row] for row in packet['log_hessian']]
    u,v=box[2:];u2,v2=IPow(u,2),IPow(v,2);uv=IMul(u,v);half=(Q(1,2),Q(1,2))
    diff=IAdd(v2,INeg(u2));opp=INeg(diff)
    ax=IAdd(IMul(half,IMul(diff,g[0])),INeg(IMul(uv,g[1])))
    ay=IAdd(IMul(half,IMul(opp,g[1])),INeg(IMul(uv,g[0])))
    jac=[[(Q(0),Q(0)),(Q(0),Q(0)),(Q(1),Q(1)),(Q(0),Q(0))],
         [(Q(0),Q(0)),(Q(0),Q(0)),(Q(0),Q(0)),(Q(1),Q(1))]]
    jac.append([IAdd(IMul(half,IMul(diff,h[0][i])),INeg(IMul(uv,h[1][i]))) for i in range(2)]+
               [INeg(IAdd(IMul(u,g[0]),IMul(v,g[1]))),IAdd(IMul(v,g[0]),INeg(IMul(u,g[1])))])
    jac.append([IAdd(IMul(half,IMul(opp,h[1][i])),INeg(IMul(uv,h[0][i]))) for i in range(2)]+
               [IAdd(IMul(u,g[1]),INeg(IMul(v,g[0]))),INeg(IAdd(IMul(v,g[1]),IMul(u,g[0])))])
    return [u,v,ax,ay],jac

def certify_flow_tube(packet,initial_box,tube_box,time,*,iterations=4):
    """Picard self-mapping and contraction on a supplied convex four-state tube.

    Produces a whole-time enclosure and a tighter endpoint enclosure. The
    analytic Picard theorem is used mathematically, not claimed as new Lean code.
    """
    check_metric(packet);time=rational(time)
    if time<=0 or type(iterations) is not int or not 0<=iterations<=32:raise ValueError('positive time and iteration count 0..32 required')
    def boxes(data):
        if len(data)!=4:raise ValueError('four state intervals required')
        rows=[tuple(map(rational,row)) for row in data]
        if any(len(row)!=2 or row[0]>row[1] for row in rows):raise ValueError('ordered intervals required')
        return rows
    initial,tube=map(boxes,(initial_box,tube_box))
    if any(not b[0]<=a[0]<=a[1]<=b[1] for a,b in zip(initial,tube)):raise ValueError('initial state outside tube')
    pos=tube[:2];N=_interval_poly(packet['numerator'],pos);D=_interval_poly(packet['denominator_squared'],pos)
    if N[0]<=0 or D[0]<=0:raise ValueError('tube metric positivity not established')
    field,jac=_ode_interval(packet,tube)
    L=max(sum(max(abs(a),abs(b)) for a,b in row) for row in jac)
    if time*L>=1:raise ValueError('Picard contraction factor must be below one')
    def advance(bounds,span):return [IAdd(a,IMul(span,f)) for a,f in zip(initial,bounds)]
    whole=advance(field,(Q(0),time))
    if any(not b[0]<=a[0]<=a[1]<=b[1] for a,b in zip(whole,tube)):raise ValueError('Picard image leaves tube')
    for _ in range(iterations):
        field,_=_ode_interval(packet,whole);candidate=advance(field,(Q(0),time))
        whole=[(max(a[0],b[0]),min(a[1],b[1])) for a,b in zip(whole,candidate)]
    field,_=_ode_interval(packet,whole);endpoint=advance(field,(time,time))
    enc=lambda rows:[list(map(str,row)) for row in rows]
    return {'schema':'pp-conformal-picard-tube/1','metric_sha256':digest(packet),'initial_box':enc(initial),
            'tube_box':enc(tube),'time':str(time),'iterations':iterations,'lipschitz_bound':str(L),
            'contraction_factor':str(time*L),'whole_time_box':enc(whole),'endpoint_box':enc(endpoint),
            'metric_numerator_interval':list(map(str,N)),'metric_denominator_squared_interval':list(map(str,D)),
            'kernel_checked':False,'scope':'rational interval Picard self-mapping/contraction; analytic existence/uniqueness relies on classical Picard theory, not a formal Lean ODE proof'}

def check_flow_tube(packet,certificate):
    expected=certify_flow_tube(packet,certificate['initial_box'],certificate['tube_box'],certificate['time'],iterations=certificate['iterations'])
    if expected!=certificate:raise ValueError('flow tube does not replay')
    return True


def certify_domain(packet,box,lower_scale,upper_scale,*,depth=4,node_limit=10000):
    """Continuous distance comparison for paths restricted to this convex chart.

    The map is the identity on the admitted rectangle; both distances use the
    same nonempty family of piecewise-smooth contained paths. No mesh/surface
    correspondence or unrestricted compact-curve distance is inferred.
    """
    check_metric(packet);box=[rational(v) for v in box];l,u=map(rational,(lower_scale,upper_scale))
    if not 0<l<=u:raise ValueError('positive ordered scales required')
    N,D=_poly(packet['numerator']),_poly(packet['denominator_squared'])
    gaps={'numerator_positive':N,'denominator_positive':D,
          'lower_gap':B.add(B.power(N,2),B.scale(D,-l**4)),
          'upper_gap':B.add(B.scale(D,u**4),B.scale(B.power(N,2),-1))}
    witnesses={k:B.certify(p,box,depth=depth,node_limit=node_limit) for k,p in gaps.items()}
    if not all(v['complete'] for v in witnesses.values()):raise WorkLimit('metric box comparison unresolved')
    return {'schema':'pp-contained-smooth-distance-bridge/1','metric_sha256':digest(packet),
            'box':list(map(str,B.rectangle(box))),'lower_scale':str(l),'upper_scale':str(u),
            'witnesses':witnesses,'complete':True,'kernel_checked':False,
            'comparison_domain':'intrinsic distance among piecewise-smooth paths contained in this rectangle',
            'unrestricted_curve_comparison':False,
            'scope':'proved pointwise chart bounds plus common-path length/infimum comparison; reference distance is Euclidean because the rectangle is convex; analytic tensor-to-speed interpretation uses classical conformal geometry'}

def check_domain(packet,bridge):
    if bridge.get('schema')=='pp-global-smooth-plane-bridge/1':
        expected_metric,expected_bridge=bounded_plane_bridge()
        if packet!=expected_metric or bridge!=expected_bridge:raise ValueError('whole-plane bridge does not match its proved metric')
        return True
    if bridge.get('schema')!='pp-contained-smooth-distance-bridge/1' or bridge['metric_sha256']!=digest(packet):raise ValueError('bridge source mismatch')
    check_metric(packet);l,u=map(rational,(bridge['lower_scale'],bridge['upper_scale']))
    if not 0<l<=u or bridge['complete'] is not True or bridge['unrestricted_curve_comparison'] is not False:raise ValueError('invalid bridge scope')
    N,D=_poly(packet['numerator']),_poly(packet['denominator_squared'])
    gaps={'numerator_positive':N,'denominator_positive':D,
          'lower_gap':B.add(B.power(N,2),B.scale(D,-l**4)),
          'upper_gap':B.add(B.scale(D,u**4),B.scale(B.power(N,2),-1))}
    if set(bridge['witnesses'])!=set(gaps):raise ValueError('bridge witness set mismatch')
    for name,p in gaps.items():
        cert=bridge['witnesses'][name]
        if not B.verify(cert) or not cert['complete'] or cert['sign']!=1 or cert['box']!=bridge['box'] or _poly(cert['polynomial'])!=p:
            raise ValueError('invalid metric comparison witness')
    return True

def bridge_distances(packet,bridge,p,q,*,bits=64):
    check_domain(packet,bridge)
    p,q=[list(map(rational,v)) for v in (p,q)]
    if any(len(v)!=2 for v in (p,q)):raise ValueError('two distance coordinates required')
    if bridge['box'] is not None:
        a,b,c,d=map(Q,bridge['box'])
        if any(not(a<=v[0]<=b and c<=v[1]<=d) for v in (p,q)):raise ValueError('distance endpoint outside bridge')
    distance2=sum((x-y)**2 for x,y in zip(p,q));l,u=map(Q,(bridge['lower_scale'],bridge['upper_scale']))
    lo,hi=sqrt_interval(distance2,bits)
    return {'start':list(map(str,p)),'end':list(map(str,q)),
            'distance_interval':[str(l*lo),str(u*hi)],'squared_distance_interval':[str(l*l*distance2),str(u*u*distance2)],
            'domain':bridge['comparison_domain'],'kernel_checked':False}

def bridge_winner(packet,bridge,center,sites,site,radius,*,bits=64):
    """Strict winner on a disk intersected with the certified rectangle."""
    radius=rational(radius)
    if radius<0 or site not in sites:raise ValueError('nonnegative radius and supplied site required')
    distances={k:bridge_distances(packet,bridge,center,p,bits=bits) for k,p in sites.items()}
    u=Q(bridge['upper_scale']);upper=Q(distances[site]['distance_interval'][1])
    margins={k:Q(v['distance_interval'][0])-upper-2*u*radius for k,v in distances.items() if k!=site}
    return {'site':site,'strict_winner':all(v>0 for v in margins.values()),'margins':{k:str(v) for k,v in margins.items()},
            'radius':str(radius),'patch':'Euclidean closed disk' if bridge['box'] is None else 'Euclidean closed disk intersected with the certified rectangle',
            'scope':'all supplied sites use the bridge domain and its path family; unresolved margins do not imply a tie','kernel_checked':False}


def pullback_metric(packet,coordinate_map):
    """Exact conformal rational chart pullback, including reversing charts.

    The original map poles and zero Jacobian are retained as domain exclusions
    even when the resulting density simplifies to a regular expression.
    """
    check_metric(packet);s,(x,y)=_sp()
    if len(coordinate_map)!=2:raise ValueError('two rational coordinate functions required')
    f=[_rf_expr(r,s,x,y) for r in coordinate_map];J=s.Matrix([[s.diff(v,z) for z in (x,y)] for v in f])
    gram=(J.T*J).applyfunc(s.cancel);factor=gram[0,0]
    if s.cancel(gram[0,1])!=0 or s.cancel(gram[1,0])!=0 or s.cancel(gram[1,1]-factor)!=0 or factor==0:
        raise ValueError('nonconstant conformal rational coordinate map required')
    square=_rf_expr(packet['density_squared'],s,x,y).subs({x:f[0],y:f[1]},simultaneous=True)
    transformed=s.cancel(square*factor**2);p,q=s.fraction(transformed)
    # pq/sqrt(pq^3)=sqrt(p/q) on every positive squared-density domain,
    # independently of the signs of p and q before denominator clearing.
    N=s.expand(p*q);D=s.expand(p*q**3)
    result=compile_metric(_encode_expr(N,s,x,y),_encode_expr(D,s,x,y))
    determinant=s.cancel(J.det())
    g=[_rf_expr(r,s,x,y) for r in packet['log_gradient']]
    gp=[_rf_expr(r,s,x,y) for r in result['log_gradient']]
    u,v=s.symbols('u v',real=True);velocity=s.Matrix([u,v]);image_velocity=J*velocity
    def acc(gradient,v):
        a,b=v;gx,gy=gradient
        return s.Matrix([(b*b-a*a)*gx/2-a*b*gy,(a*a-b*b)*gy/2-a*b*gx])
    source_acc=acc([r.subs({x:f[0],y:f[1]},simultaneous=True) for r in g],image_velocity)
    pulled_acc=acc(gp,velocity)
    extra=s.Matrix([(velocity.T*s.hessian(expr,(x,y))*velocity)[0] for expr in f])
    residual=[s.cancel(r) for r in J*pulled_acc+extra-source_acc]
    if any(r!=0 for r in residual):raise AssertionError('geodesic chart transport identity failed')
    domain={'map_denominators':[r['denominator'] for r in coordinate_map],
            'jacobian_determinant':_rf(determinant,s,x,y),
            'mapped_numerator':_rf(_expr(_poly(packet['numerator']),s,x,y).subs({x:f[0],y:f[1]},simultaneous=True),s,x,y),
            'mapped_denominator_squared':_rf(_expr(_poly(packet['denominator_squared']),s,x,y).subs({x:f[0],y:f[1]},simultaneous=True),s,x,y)}
    return {'schema':'pp-conformal-chart-transport/1','source_metric_sha256':digest(packet),
            'coordinate_map':coordinate_map,'metric':result,'jacobian':[[ _rf(c,s,x,y) for c in row] for row in J.tolist()],
            'conformal_factor':_rf(factor,s,x,y),'domain_exclusions':domain,
            'geodesic_transport_residual':['0','0'],'kernel_checked':False,
            'scope':'symbolically exact chart pullback and geodesic chain rule on regular map points; injectivity, branch-sheet identity and global chart coverage are not inferred'}

def check_transport(source,transport):
    if transport!=pullback_metric(source,transport['coordinate_map']):raise ValueError('chart transport does not replay')
    return True

def transport_point(source,transport,p,velocity):
    check_transport(source,transport)
    if transport['source_metric_sha256']!=digest(source):raise ValueError('chart transport source mismatch')
    if len(p)!=2 or len(velocity)!=2:raise ValueError('two coordinates and velocities required')
    x,y=map(rational,p);v=list(map(rational,velocity));domain=transport['domain_exclusions']
    if any(B.evaluate(_poly(d),x,y)==0 for d in domain['map_denominators']):raise ValueError('original chart-map pole')
    if _eval(domain['jacobian_determinant'],x,y)==0:raise ValueError('critical chart-map point')
    q=[_eval(r,x,y) for r in transport['coordinate_map']];_point_data(source,q);_point_data(transport['metric'],(x,y))
    J=[[_eval(r,x,y) for r in row] for row in transport['jacobian']]
    return {'point':list(map(str,q)),'velocity':[str(sum(a*b for a,b in zip(row,v))) for row in J],
            'density_squared_pullback':str(_eval(transport['metric']['density_squared'],x,y)),
            'jacobian_determinant':str(_eval(domain['jacobian_determinant'],x,y))}


def trace_geodesic(packet,initial,time,steps,*,transport=(1,0),variation=(0,0,0,1)):
    """RK4 demonstration including parallel transport and linearized flow.

    This trajectory is numerical. Use certify_flow_tube for rational enclosures.
    """
    check_metric(packet)
    if len(initial)!=4 or len(transport)!=2 or len(variation)!=4 or type(steps) is not int or not 1<=steps<=10000:
        raise ValueError('four initial coordinates, two transport entries, four variation entries, and steps 1..10000 required')
    import math
    time=float(rational(time))
    if not 0<time or not math.isfinite(time):raise ValueError('positive finite time required')
    state=list(map(lambda v:float(rational(v)),list(initial)+list(transport)+list(variation)))
    def poly(p,x,y):return sum(float(c)*x**i*y**j for (i,j),c in _poly(p).items())
    def rf(r,x,y):
        d=poly(r['denominator'],x,y)
        if d==0:raise ValueError('numerical chart pole')
        return poly(r['numerator'],x,y)/d
    def rates(z):
        x,y,u,v,zx,zy,*eta=z
        if not all(math.isfinite(q) for q in z):raise ValueError('nonfinite numerical state')
        if poly(packet['numerator'],x,y)<=0 or poly(packet['denominator_squared'],x,y)<=0:raise ValueError('numerical path left positive metric domain')
        gx,gy=[rf(r,x,y) for r in packet['log_gradient']];h=[[rf(r,x,y) for r in row] for row in packet['log_hessian']]
        a=[(v*v-u*u)*gx/2-u*v*gy,(u*u-v*v)*gy/2-u*v*gx]
        gv=gx*u+gy*v;gz=gx*zx+gy*zy;vz=u*zx+v*zy
        zd=[-(gv*w+gz*t-vz*g)/2 for w,t,g in zip((zx,zy),(u,v),(gx,gy))]
        jac=[[0,0,1,0],[0,0,0,1],[(v*v-u*u)*h[0][i]/2-u*v*h[1][i] for i in range(2)]+[-u*gx-v*gy,v*gx-u*gy],
             [(u*u-v*v)*h[1][i]/2-u*v*h[0][i] for i in range(2)]+[u*gy-v*gx,-v*gy-u*gx]]
        return [u,v,*a,*zd,*[sum(a*b for a,b in zip(row,eta)) for row in jac]]
    def record(t,z):
        x,y,u,v,zx,zy,*eta=z;rho=poly(packet['numerator'],x,y)/math.sqrt(poly(packet['denominator_squared'],x,y))
        return {'time':t,'position':z[:2],'velocity':z[2:4],'transport':z[4:6],'variation':eta,
                'energy':rho*(u*u+v*v)/2,'transport_norm_squared':rho*(zx*zx+zy*zy)}
    rows=[record(0,state)];h=time/steps
    for i in range(steps):
        k1=rates(state);k2=rates([z+h*k/2 for z,k in zip(state,k1)]);k3=rates([z+h*k/2 for z,k in zip(state,k2)]);k4=rates([z+h*k for z,k in zip(state,k3)])
        state=[z+h*(a+2*b+2*c+d)/6 for z,a,b,c,d in zip(state,k1,k2,k3,k4)];rates(state);rows.append(record((i+1)*h,state))
    return {'schema':'pp-conformal-geodesic-trace/1','metric_sha256':digest(packet),'samples':rows,
            'maximum_energy_drift':max(abs(r['energy']-rows[0]['energy']) for r in rows),
            'maximum_transport_norm_drift':max(abs(r['transport_norm_squared']-rows[0]['transport_norm_squared']) for r in rows),
            'certified_trajectory':False,'kernel_checked':False,'scope':'numerical RK4 chart trajectory, parallel transport and coordinate Jacobi variation; no global shortest-path or error-bound claim'}


def sphere_embedding(p,*,north_chart=False):
    if len(p)!=2 or type(north_chart) is not bool:raise ValueError('two coordinates and a chart boolean required')
    x,y=map(rational,p);r2=x*x+y*y;den=1+r2
    return [str(2*x/den),str(2*y/den),str((1-r2 if north_chart else r2-1)/den)]


def bounded_plane_bridge():
    metric=compile_metric([[0,0,1],[2,0,2],[0,2,2]],[[0,0,1],[2,0,2],[0,2,2],[4,0,1],[2,2,2],[0,4,1]])
    bridge={'schema':'pp-global-smooth-plane-bridge/1','metric_sha256':digest(metric),
            'box':None,'lower_scale':'1','upper_scale':'3/2','complete':True,'kernel_checked':False,
            'comparison_domain':'all piecewise-smooth paths in the entire coordinate plane',
            'unrestricted_curve_comparison':False,'global_distance_comparison':True,
            'pointwise_density_bounds':['1','2'],
            'scope':'explicit smooth plane metric (1+2r^2)/(1+r^2); identity map and whole-plane path family, not a mesh-to-compact-curve identification'}
    return metric,bridge
