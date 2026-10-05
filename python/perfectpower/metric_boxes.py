"""Exact hyperelliptic chart densities and rational tensor comparisons.

The metric is the sum of squared norms of the explicit forms x^j dx/y. It is
not the period-normalized Bergman metric. Comparisons are local chart statements;
they are not global geodesic comparisons across unspecified chart transitions.
"""
from fractions import Fraction as Q
from . import bernstein_boxes as B
from . import polyalg as P

ZERO={};ONE={(0,0):Q(1)};X={(1,0):Q(1)};Y={(0,1):Q(1)}

def cmul(a,b):
    return (B.add(B.mul(a[0],b[0]),B.scale(B.mul(a[1],b[1]),-1)),
            B.add(B.mul(a[0],b[1]),B.mul(a[1],b[0])))

def ceval(coeff,z):
    out=(ZERO,ZERO)
    for c in reversed(coeff):out=cmul(out,z);out=(B.add(out[0],{(0,0):Q(c)}),out[1])
    return out

def modsq(z):return B.add(B.power(z[0],2),B.power(z[1],2))

def chart_density(coeff,chart,branch=None):
    coeff=list(map(Q,coeff))
    while coeff and not coeff[-1]:coeff.pop()
    m=len(coeff)-1
    if not 3<=m<=9:raise ValueError('hyperelliptic degree 3..9')
    polynomial=P.poly(coeff)
    if P.degree(P.gcd_poly(polynomial,P.derivative(polynomial))) != 0:
        raise ValueError('smooth hyperelliptic polynomial must be squarefree')
    g=(m-1)//2;t=(X,Y)
    if chart=='finite':
        z=t;den=ceval(coeff,z);num={}
        for j in range(g):num=B.add(num,B.power(modsq(z),j))
    elif chart=='branch':
        if branch is None:raise ValueError('rational branch root required')
        b=Q(branch)
        if sum(c*b**i for i,c in enumerate(coeff)):raise ValueError('not a polynomial root')
        # Exact division by x-b, with ascending coefficients.
        quotient=[Q(0)]*m;quotient[-1]=coeff[-1]
        for i in range(m-1,0,-1):quotient[i-1]=coeff[i]+b*quotient[i]
        if not sum(c*b**i for i,c in enumerate(quotient)):raise ValueError('branch root must be simple')
        z=cmul(t,t);z=(B.add(z[0],{(0,0):b}),z[1]);den=ceval(quotient,z);num={}
        for j in range(g):num=B.add(num,B.power(modsq(z),j))
        num=B.scale(num,4)
    elif chart=='infinity':
        z=cmul(t,t) if m%2 else t
        den=ceval(list(reversed(coeff)),z);num={}
        for k in range(g):num=B.add(num,B.power(modsq(t),2*k if m%2 else k))
        if m%2:num=B.scale(num,4)
    else:raise ValueError('chart finite, branch or infinity')
    return {'coefficients':list(map(str,coeff)),'genus':g,'chart':chart,
            'branch':None if branch is None else str(Q(branch)),
            'numerator':B.encode(num),'denominator_modulus_squared':B.encode(modsq(den)),
            'density':'numerator / sqrt(denominator_modulus_squared)',
            'metric':'sum_j |x^j dx/y|^2, j=0..g-1','period_normalized':False}


def compare(coeff,chart,box,lower_scale,upper_scale,reference_density=1,branch=None,**options):
    data=chart_density(coeff,chart,branch);N=B.poly(data['numerator']);D=B.poly(data['denominator_modulus_squared'])
    l,u,r=Q(lower_scale),Q(upper_scale),Q(reference_density)
    if not 0<l<=u or r<=0:raise ValueError('positive comparison scales/density')
    gaps={'numerator_positive':N,'denominator_positive':D,
          'lower_gap':B.add(B.power(N,2),B.scale(D,-l**4*r*r)),
          'upper_gap':B.add(B.scale(D,u**4*r*r),B.scale(B.power(N,2),-1))}
    witnesses={name:B.certify(p,box,**options) for name,p in gaps.items()}
    return {'schema':'pp-hyperelliptic-metric-box/1','chart_data':data,'box':list(map(str,B.rectangle(box))),
            'lower_scale':str(l),'upper_scale':str(u),'reference_density':str(r),'witnesses':witnesses,
            'complete':all(p['complete'] for p in witnesses.values()),'kernel_checked':False,
            'global_distance_comparison':False,'claim':'Pointwise tangent metric comparison on this chart rectangle.'}


def verify(packet):
    try:
        if packet['schema']!='pp-hyperelliptic-metric-box/1' or packet['kernel_checked'] is not False or packet['global_distance_comparison'] is not False:return False
        data=packet['chart_data'];expected=chart_density(data['coefficients'],data['chart'],data['branch'])
        if data!=expected:return False
        N=B.poly(data['numerator']);D=B.poly(data['denominator_modulus_squared'])
        l,u,r=Q(packet['lower_scale']),Q(packet['upper_scale']),Q(packet['reference_density'])
        if not 0<l<=u or r<=0:return False
        gaps={'numerator_positive':N,'denominator_positive':D,
              'lower_gap':B.add(B.power(N,2),B.scale(D,-l**4*r*r)),
              'upper_gap':B.add(B.scale(D,u**4*r*r),B.scale(B.power(N,2),-1))}
        if set(packet['witnesses'])!=set(gaps):return False
        for name,p in gaps.items():
            cert=packet['witnesses'][name]
            if not B.verify(cert) or cert['sign']!=1 or cert['box']!=packet['box'] or B.poly(cert['polynomial'])!=p:return False
        return packet['complete'] is all(p['complete'] for p in packet['witnesses'].values())
    except (KeyError,ValueError,TypeError,IndexError,ZeroDivisionError):return False


class MetricBoxSpace:
    """Reuse a validated local comparison for point and contained segment queries."""
    def __init__(self,packet):
        if not verify(packet) or not packet['complete']:raise ValueError('complete metric certificate required')
        self._N=B.poly(packet['chart_data']['numerator']);self._D=B.poly(packet['chart_data']['denominator_modulus_squared'])
        self._box=B.rectangle(packet['box']);self._l=Q(packet['lower_scale']);self._u=Q(packet['upper_scale']);self._r=Q(packet['reference_density'])
        self._queries=0

    def _inside(self,point):
        if len(point)!=2:raise ValueError('two chart coordinates')
        x,y=map(Q,point);a,b,c,d=self._box
        if not a<=x<=b or not c<=y<=d:raise ValueError('point outside certified chart box')
        return x,y

    def point(self,point,bits=48):
        from math import isqrt
        x,y=self._inside(point)
        if type(bits) is not int or not 1<=bits<=256:raise ValueError('precision 1..256 bits')
        N=B.evaluate(self._N,x,y);D=B.evaluate(self._D,x,y);scale=1<<bits
        k=isqrt(D.numerator*scale*scale//D.denominator)
        sqrtlo=Q(k,scale);sqrthi=sqrtlo if sqrtlo*sqrtlo==D else Q(k+1,scale)
        lo=max(self._l**2*self._r,N/sqrthi)
        hi=min(self._u**2*self._r,N/sqrtlo) if sqrtlo else self._u**2*self._r
        self._queries+=1
        return {'schema':'pp-metric-point/1','point':list(map(str,(x,y))),
                'density_interval':[str(lo),str(hi)],'kernel_checked':False,
                'global_distance_comparison':False}

    def segment(self,start,end):
        a,b=self._inside(start);c,d=self._inside(end)
        length2=(a-c)**2+(b-d)**2
        self._queries+=1
        return {'schema':'pp-contained-chart-segment/1','start':list(map(str,(a,b))),'end':list(map(str,(c,d))),
                'squared_path_length_interval':[str(self._l**2*self._r*length2),str(self._u**2*self._r*length2)],
                'claim':'Length bounds for the straight path in this certified chart; not unrestricted geodesic distance.',
                'global_distance_comparison':False,'kernel_checked':False}

    def statistics(self):return {'certificate_checks':1,'queries':self._queries}
