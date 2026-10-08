"""Exact rational 3-isogenies and an alternate Mordell witness route.

Discovery on a partner curve never establishes emptiness on the original.
The dual map has finite kernel; its positively checked images can contribute
to the existing original-curve independence certificates.
"""
import copy
import json
import subprocess
from . import polyalg as P
from .elliptic_arithmetic import EllipticCurve, encode_point, q
from .elliptic_two_descent import gp_executable, quartic_map
from .mordell_cover_charts import projective_cover_lift


def three_isogeny(k):
    if type(k) is not int or not k or abs(k)>10**12:
        raise ValueError('nonzero bounded integer Mordell coefficient required')
    x3=P.poly([0,0,0,1]);plus=P.add(x3,P.poly([k]))
    nx=P.add(x3,P.poly([4*k]));ny=P.add(x3,P.poly([-8*k]))
    identity=P.subtract(P.mul(plus,P.power(ny,2)),P.power(nx,3))
    if identity != P.poly([0,0,0,0,0,0,-27*k]):
        raise ArithmeticError('three-isogeny polynomial identity failed')
    return dict(schema='pp-mordell-three-isogeny/1',k=k,partner_k=-27*k,
        degree=3,forward_x='(x^3+4k)/x^2',forward_y='y*(x^3-8k)/x^3',
        dual_x='(u^3-108k)/(9u^2)',dual_y='v*(u^3+216k)/(27u^3)',
        forward_differential_factor=1,dual_differential_factor=3,
        kernel_abscissa=0,composition_scalar=3,identity_checked=True)


def isogeny_point(k, point, *, dual=False):
    three_isogeny(k)
    source=EllipticCurve([0,-27*k if dual else k]);target=EllipticCurve([0,k if dual else -27*k])
    p=source.checked(point)
    if p is None or p[0]==0:return None
    x,y=p
    image=((x**3-108*k)/(9*x*x),y*(x**3+216*k)/(27*x**3)) if dual else ((x**3+4*k)/(x*x),y*(x**3-8*k)/(x**3))
    return encode_point(target.checked(image))


def compose_isogeny_cover(k, cover):
    """Compile a partner quartic directly to the original Mordell equation.

    X=x_numerator/x_denominator; Y=y_numerator/(y_denominator*z),
    with z^2=R. All exceptional denominators are explicit.
    """
    three_isogeny(k);quartic_map(-27*k,cover)
    R,A,B=(P.poly(map(q,cover[key])) for key in ('quartic','x_numerator','y_numerator'))
    A3,R3=P.power(A,3),P.power(R,3)
    nx=P.subtract(A3,P.scale(R3,108*k));dx=P.scale(P.mul(P.power(A,2),R),9)
    ny=P.mul(B,P.add(A3,P.scale(R3,216*k)));dy=P.scale(P.mul(A3,R),27)
    # Denominator-cleared equation in Q[t,z]/(z^2-R).
    identity=P.subtract(P.mul(P.power(ny,2),P.power(dx,3)),
        P.mul(P.add(P.power(nx,3),P.scale(P.power(dx,3),k)),P.mul(P.power(dy,2),R)))
    if not P.is_zero(identity):raise ArithmeticError('composed cover-to-Mordell identity failed')
    return dict(schema='pp-isogeny-composed-cover/1',k=k,partner_k=-27*k,
        quartic=[str(v) for v in R],x_numerator=[str(v) for v in nx],
        x_denominator=[str(v) for v in dx],y_numerator=[str(v) for v in ny],
        y_denominator=[str(v) for v in dy],y_ordinate_factor='z',
        nonzero_polynomials=[[str(v) for v in R],[str(v) for v in A]],
        identity_checked=True,integral_point_completeness=False)


def partner_covers(k, *, timeout=30, gp=None):
    """External cover discovery, retaining exact maps but no new rank assertion."""
    three_isogeny(k)
    if type(timeout) not in (int,float) or not 0<timeout<=60:raise ValueError('timeout from zero through sixty')
    script=f'''default(parisize,128000000);
E=ellinit([0,{-27*k}]);C=ell2cover(E);
cv=vector(#C,i,[vector(5,j,Str(polcoef(C[i][1],j-1))),vector(5,j,Str(polcoef(C[i][2][1]*y^2,j-1,x))),vector(7,j,Str(polcoef(C[i][2][2]*y^3,j-1,x)))]);
print("PP_PARTNER_COVERS:",cv);quit
'''
    run=subprocess.run([gp_executable(gp),'-fq'],input=script,text=True,capture_output=True,timeout=timeout,check=True)
    lines=[line.split(':',1)[1] for line in run.stdout.splitlines() if line.startswith('PP_PARTNER_COVERS:')]
    warning='***   Warning: new stack size = 128000000 (122.070 Mbytes).'
    if len(lines)!=1 or '***' in run.stderr.replace(warning,''):raise RuntimeError('partner-cover discovery failed: '+run.stderr[:400])
    covers=[dict(quartic=c[0],x_numerator=c[1],y_numerator=c[2]) for c in json.loads(lines[0])]
    for cover in covers:quartic_map(-27*k,cover)
    return dict(schema='pp-mordell-isogeny-covers/1',k=k,partner_k=-27*k,covers=covers,
        completeness_claimed=False,rank_assertion=False)


def augment_isogeny_witnesses(descent, records):
    """Retain checked partner-cover points, dual images and original independence."""
    if descent.get('schema')!='pp-mordell-two-descent/1':raise ValueError('descent packet required')
    result=copy.deepcopy(descent);k=result['k'];three_isogeny(k);E=EllipticCurve([0,k])
    if E.specification!=result['curve']:raise ValueError('original Mordell model mismatch')
    points=[encode_point(E.checked(p)) for p in result['points']]
    accepted=[]
    for record in records:
        if record.get('source_kind')=='heegner_partner':
            partner_point=encode_point(EllipticCurve([0,-27*k]).checked(record['partner_point']))
            if partner_point!=record['partner_point']:raise ValueError('noncanonical partner point')
        else:
            partner=projective_cover_lift(-27*k,record['partner_cover'],record['partner_coordinates'])
            if partner['mordell_point']!=record['partner_point']:raise ValueError('partner point differs from retained cover')
        image=isogeny_point(k,record['partner_point'],dual=True)
        if image is None:continue
        if image!=record['mordell_point']:raise ValueError('dual-isogeny image mismatch')
        if image not in points:points.append(image)
        accepted.append(copy.deepcopy(record))
    if len(points)>64:raise ValueError('at most 64 retained witnesses')
    # A sufficient rank lower bound does not require making every retained
    # (possibly redundant) point independent. Avoid pointless large halving
    # computations once the existing upper bound has already been matched.
    certificate=E.independence(points,prime_bound=500,halving_limit=0)
    if certificate['rank_lower_bound']<result['rank_upper_bound']:
        from .divisor_square import WorkLimit
        try:certificate=E.independence(points,prime_bound=500,halving_limit=8)
        except WorkLimit:pass
    lower=certificate['rank_lower_bound'];upper=result['rank_upper_bound']
    if not result['witness_rank_lower_bound']<=lower<=upper:raise ArithmeticError('inconsistent witness bounds')
    result.update(points=points,independence=certificate,witness_rank_lower_bound=lower,rank_determined=lower==upper)
    retained=result.setdefault('isogeny_point_lifts',[])
    for record in accepted:
        if record not in retained:retained.append(record)
    return result
