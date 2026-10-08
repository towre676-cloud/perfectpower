"""Exact rational chart transport and bounded denominator-box cover searches.

Analytic or bounded search is discovery only; exact positive point identities
are what can contribute to a witnessed lower rank bound. No negative rank
or global emptiness assertion follows from these searches.
"""
from math import gcd
import json,subprocess
from . import polyalg as P
from .elliptic_arithmetic import q,EllipticCurve,encode_point
from .elliptic_two_descent import quartic_map,gp_executable,lift_quartic_point


def _matrix(matrix):
    if type(matrix) is not list or len(matrix)!=2 or any(type(row) is not list or len(row)!=2 for row in matrix):raise ValueError('two by two integer matrix required')
    if any(type(v) is not int or abs(v)>1000000 for row in matrix for v in row):raise ValueError('bounded literal integer entries required')
    (a,b),(c,d)=matrix
    if a*d-b*c==0:raise ValueError('invertible rational chart required')
    return a,b,c,d


def _binary(values,degree,a,b,c,d):
    U,V=P.poly((b,a)),P.poly((d,c));out=P.ZERO
    for i,v in enumerate(values):out=P.add(out,P.scale(P.mul(P.power(U,i),P.power(V,degree-i)),q(v)))
    return out


def chart_cover(k,cover,matrix,ordinate_scale=1):
    """t=(as+b)/(cs+d), z=e*w/(cs+d)^2; all map denominators retained."""
    quartic_map(k,cover);a,b,c,d=_matrix(matrix);e=ordinate_scale
    if type(e) is not int or not 1<=e<=1000000:raise ValueError('bounded positive ordinate scale required')
    result={key:[str(v) for v in P.scale(_binary(cover[key],degree,a,b,c,d),q(1)/e**weight)]
            for key,degree,weight in [('quartic',4,2),('x_numerator',4,2),('y_numerator',6,3)]}
    if any(q(v).denominator!=1 for v in result['quartic']):raise ValueError('transformed quartic must be integral')
    quartic_map(k,result)
    return dict(schema='pp-mordell-cover-chart/1',k=k,source_cover=cover,matrix=matrix,
                ordinate_scale=e,cover=result,determinant=a*d-b*c,
                source_height_factor=max(abs(a)+abs(b),abs(c)+abs(d)),
                inverse_height_factor=max(abs(d)+abs(b),abs(c)+abs(a)),
                execution_verified=False)


def projective_cover_lift(k,cover,coordinates):
    """Original homogeneous cover point, including its finite-ordinate infinity chart."""
    quartic_map(k,cover)
    if type(coordinates) not in (list,tuple) or len(coordinates)!=3 or any(type(x) is not int for x in coordinates):raise ValueError('three homogeneous integers required')
    u,v,w=coordinates
    if v<0 or gcd(u,v)!=1 or (v==0 and u!=1) or not w:raise ValueError('canonical primitive abscissa and nonzero ordinate required')
    def hom(values,n):return sum(q(a)*u**i*v**(n-i) for i,a in enumerate(values))
    if hom(cover['quartic'],4)!=w*w:raise ValueError('homogeneous cover point equation failed')
    x,y=hom(cover['x_numerator'],4)/w**2,hom(cover['y_numerator'],6)/w**3
    point=encode_point(EllipticCurve([0,k]).checked([x,y]))
    return dict(source_coordinates=[u,v,w],mordell_point=point,
                target_integral=x.denominator==y.denominator==1)


def lift_chart_point(chart,point):
    """Lift via both the transformed map and the canonical source projective chart."""
    rebuilt=chart_cover(chart['k'],chart['source_cover'],chart['matrix'],chart['ordinate_scale'])
    if chart!=rebuilt:raise ValueError('chart data mismatch')
    if type(point) not in (list,tuple) or len(point)!=2:raise ValueError('affine chart point required')
    s,z=map(q,point);k=chart['k'];target=lift_quartic_point(k,chart['cover'],[s,z])
    a,b,c,d=_matrix(chart['matrix']);u,v=s.numerator,s.denominator
    W=chart['ordinate_scale']*z*v*v
    if W.denominator!=1:raise ValueError('nonintegral weighted ordinate')
    U,V=a*u+b*v,c*u+d*v;g=gcd(U,V)
    if not g:raise ValueError('zero projective abscissa')
    U,V,W=U//g,V//g,W/(g*g)
    if W.denominator!=1:raise ValueError('source ordinate does not normalize integrally')
    if V<0 or (V==0 and U<0):U,V=-U,-V
    result=projective_cover_lift(k,chart['source_cover'],[U,V,int(W)])
    if result['mordell_point']!=target:raise ArithmeticError('chart transport identity failed')
    return dict(chart_point=[str(s),str(z)],source_affine_point=[str(q(U)/V),str(q(int(W))/V**2)] if V else None,
                source_pole=V==0,**result)


def search_cover_box(k,cover,*,matrix=None,numerator_bound=1000000,
                     denominator_min=1,denominator_max=1000,timeout=5,gp=None):
    """Rectangular or denominator-window search; timeout is a separate outcome."""
    matrix=[[1,0],[0,1]] if matrix is None else matrix
    for value in (numerator_bound,denominator_min,denominator_max):
        if type(value) is not int or not 1<=value<=10**9:raise ValueError('positive search bounds at most 10^9 required')
    if not denominator_min<=denominator_max<=numerator_bound:raise ValueError('ordered denominator bounds required')
    if type(timeout) not in (int,float) or not 0<timeout<=60:raise ValueError('timeout in (0,60] required')
    chart=chart_cover(k,cover,matrix)
    height=f'[{numerator_bound},{denominator_max}]' if denominator_min==1 else f'[{numerator_bound},[{denominator_min},{denominator_max}]]'
    f='+'.join(f'({q(v)})*x^{j}' for j,v in enumerate(chart['cover']['quartic']))
    script='default(parisize,128000000);\n'+f'R={f};H=hyperellratpoints(R,{height},1);print("PP_BOX_POINTS:",vector(#H,i,vector(2,j,Str(H[i][j]))));quit\n'
    result=dict(schema='pp-mordell-cover-box/1',k=k,chart=chart,
                numerator_bound=numerator_bound,denominator_min=denominator_min,
                denominator_max=denominator_max,timeout=timeout,lifts=[],
                global_empty_proof=False,integral_point_completeness=False,execution_verified=False)
    try:
        run=subprocess.run([gp_executable(gp),'-fq'],input=script,text=True,capture_output=True,timeout=timeout,check=True)
    except subprocess.TimeoutExpired:return dict(result,status='timeout')
    lines=[s.split(':',1)[1] for s in run.stdout.splitlines() if s.startswith('PP_BOX_POINTS:')]
    warning='***   Warning: new stack size = 128000000 (122.070 Mbytes).'
    if len(lines)!=1 or '***' in run.stderr.replace(warning,''):raise RuntimeError('PARI denominator-box search failed')
    found=json.loads(lines[0])
    if type(found) is not list or len(found)>1:raise ArithmeticError('invalid first-point result')
    for point in found:
        x,z=map(q,point)
        if not abs(x.numerator)<=numerator_bound or not denominator_min<=x.denominator<=denominator_max:raise ArithmeticError('point outside requested box')
        if not z:return dict(result,status='exceptional_zero_ordinate')
        result['lifts'].append(lift_chart_point(chart,point))
    return dict(result,status='point_returned' if result['lifts'] else 'no_point_returned')
