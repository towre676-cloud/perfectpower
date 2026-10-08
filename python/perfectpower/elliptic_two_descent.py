"""General PARI two-descent with exact quartic maps and cubic-order arithmetic.

PARI's Selmer-space and Cassels-pairing completeness is an external algorithmic
result, not a Lean theorem. Polynomial maps, integral-order arithmetic and
point-witness lower bounds are checked using exact repository arithmetic.
"""
import json
import os
import shutil
import subprocess
from fractions import Fraction as Q
from . import polyalg as P
from .elliptic_arithmetic import EllipticCurve, encode_point, q


PARI_DOC = 'https://pari.math.u-bordeaux.fr/dochtml/html-stable/Elliptic_curves.html'
NUMBER_FIELD_DOC = 'https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html'


def gp_executable(path=None):
    executable = path or os.environ.get('PERFECTPOWER_GP') or shutil.which('gp')
    if not executable:
        raise RuntimeError('PARI/GP required: install pari-gp or set PERFECTPOWER_GP')
    return executable


def determinant(a):
    n = len(a); a = [[Q(x) for x in row] for row in a]; result = Q(1)
    for j in range(n):
        pivot = next((i for i in range(j,n) if a[i][j]), None)
        if pivot is None: return Q(0)
        if pivot != j: a[j], a[pivot] = a[pivot], a[j]; result = -result
        value = a[j][j]; result *= value
        for i in range(j+1,n):
            ratio = a[i][j]/value
            a[i] = [x-ratio*y for x,y in zip(a[i],a[j])]
    return result


def solve(a, b):
    n = len(b); a = [[Q(x) for x in row]+[Q(v)] for row,v in zip(a,b)]
    for j in range(n):
        pivot = next(i for i in range(j,n) if a[i][j])
        a[j],a[pivot] = a[pivot],a[j]
        v = a[j][j]; a[j] = [x/v for x in a[j]]
        for i in range(n):
            if i != j:
                v = a[i][j]; a[i] = [x-v*y for x,y in zip(a[i],a[j])]
    return [row[-1] for row in a]


def cubic_order(polynomial, basis, field_discriminant):
    """Check a cubic order and return its exact multiplication table."""
    f = P.poly(q(x) for x in polynomial)
    if len(f) != 4 or f[-1] != 1 or any(x.denominator != 1 for x in f):
        raise ValueError('monic integral cubic required')
    if type(basis) is not list or len(basis) != 3 or any(len(row) != 3 for row in basis):
        raise ValueError('three cubic basis rows required')
    rows = [[q(x) for x in row] for row in basis]
    d,c,b,_ = f
    disc = b*b*c*c-4*c**3-4*b**3*d-27*d*d+18*b*c*d
    det = determinant(rows)
    if not det or disc*det*det != field_discriminant:
        raise ValueError('integral-basis discriminant mismatch')
    index = 1/abs(det)
    if index.denominator != 1: raise ValueError('nonintegral power-order index')
    columns = [list(row) for row in zip(*rows)]
    table = []
    for left in rows:
        table.append([])
        for right in rows:
            value = list(P.mul(left,right))
            while len(value)>3:
                lead = value.pop(); offset = len(value)-3
                for i in range(3): value[offset+i] -= lead*f[i]
            value += [Q(0)]*(3-len(value))
            coordinates = solve(columns,value)
            if any(x.denominator != 1 for x in coordinates):
                raise ValueError('basis is not multiplicatively closed')
            table[-1].append([int(x) for x in coordinates])
    return dict(power_order_index=int(index), polynomial_discriminant=int(disc),
                multiplication_table=table)


def quartic_map(k, cover):
    """Check N_y^2=N_x^3+k R^3 for x_E=N_x/y^2, y_E=N_y/y^3."""
    r,x,y = (P.poly(q(a) for a in cover[key]) for key in ('quartic','x_numerator','y_numerator'))
    if r == P.ZERO or len(r)>5 or len(x)>5 or len(y)>7:
        raise ValueError('bounded quartic cover required')
    if P.power(y,2) != P.add(P.power(x,3),P.scale(P.power(r,3),k)):
        raise ValueError('quartic-to-Mordell polynomial identity failed')
    return True


def lift_quartic_point(k, cover, point):
    """Transport a rational cover point on the affine chart y!=0."""
    quartic_map(k, cover); t,z = map(q,point)
    if not z or z*z != P.evaluate(P.poly(map(q,cover['quartic'])),t):
        raise ValueError('rational cover point with nonzero ordinate required')
    x = P.evaluate(P.poly(map(q,cover['x_numerator'])),t)/(z*z)
    y = P.evaluate(P.poly(map(q,cover['y_numerator'])),t)/(z**3)
    return encode_point(EllipticCurve([0,k]).checked([x,y]))


def mordell_two_descent(k, points=(), *, gp=None, effort=0, timeout=30):
    if type(k) is not int or not k or abs(k)>10**9:
        raise ValueError('nonzero integer Mordell parameter of absolute value at most 10^9')
    if type(effort) is not int or not 0<=effort<=10:
        raise ValueError('effort zero through ten required')
    if type(timeout) not in (int,float) or not 0<timeout<=600:
        raise ValueError('timeout zero through 600 seconds required')
    E = EllipticCurve([0,k]); witnesses = [E.checked(h) for h in points]
    if len(witnesses)>16 or any(h is None for h in witnesses):
        raise ValueError('at most sixteen affine input points required')
    # The current cubic-field route is for irreducible x^3+k.
    from .core import integer_power_root
    if integer_power_root(-k,3) is not None: raise ValueError('rational-two-torsion model requires the isogeny route')
    literals = '['+','.join('['+','.join(str(x) for x in h)+']' for h in witnesses)+']'
    script = f'''default(parisize,128000000);
setrand(1);
E=ellinit([0,{k}]);T=ellrankinit(E);B=T[3][1];ok=bnfcertify(B);nc=nfcertify(B.nf);R=ellrank(T,{effort},{literals});C=ell2cover(T);
cv=vector(#C,i,[vector(5,j,Str(polcoef(C[i][1],j-1))),vector(5,j,Str(polcoef(C[i][2][1]*y^2,j-1,x))),vector(7,j,Str(polcoef(C[i][2][2]*y^3,j-1,x)))]);
print("PP_TWO_DESCENT:",[version(),R[1],R[2],R[3],vector(#R[4],i,vector(2,j,Str(R[4][i][j]))),[ok,vector(4,j,Str(polcoef(B.nf.pol,j-1))),B.nf.disc,B.clgp[2],vector(3,i,vector(3,j,Str(polcoef(B.nf.zk[i],j-1)))),nc],cv]);
quit
'''
    result = subprocess.run([gp_executable(gp),'-fq'],input=script,text=True,
                            capture_output=True,timeout=timeout,check=True)
    lines = [line[len('PP_TWO_DESCENT:'):] for line in result.stdout.splitlines() if line.startswith('PP_TWO_DESCENT:')]
    if len(lines)!=1 or '***' in result.stdout or '***' in result.stderr.replace('***   Warning: new stack size = 128000000 (122.070 Mbytes).',''):
        raise RuntimeError('PARI did not return one successful descent result: '+result.stderr[:500])
    version,lower,upper,sha,found,field,covers = json.loads(lines[0])
    certified,polynomial,disc,class_group,basis,nfcertified = field
    if certified!=1 or nfcertified!=[] or not 0<=lower<=upper or sha<0 or sha%2:
        raise ArithmeticError('invalid descent bounds or uncertified number field')
    packets = [dict(quartic=c[0],x_numerator=c[1],y_numerator=c[2]) for c in covers]
    if len(packets)-sha!=upper:
        raise ArithmeticError('Selmer dimension and Cassels bound disagree')
    for cover in packets: quartic_map(k,cover)
    order = cubic_order(polynomial,basis,disc)
    found = [encode_point(E.checked(h)) for h in found]
    # This lower bound is supplied by actual point witnesses, not rank parity.
    independent = E.independence(found,prime_bound=97,halving_limit=0)
    if independent['rank_lower_bound']<upper and found:
        independent = E.independence(found,prime_bound=500,halving_limit=8)
    if independent['rank_lower_bound']>upper:
        raise ArithmeticError('point-witness lower bound exceeds descent upper bound')
    return dict(schema='pp-mordell-two-descent/1',k=k,curve=E.specification,
                backend='PARI/GP',backend_version=version,effort=effort,
                backend_reported_lower=lower,rank_upper_bound=upper,
                witness_rank_lower_bound=independent['rank_lower_bound'],
                rank_determined=independent['rank_lower_bound']==upper,
                selmer_dimension=len(packets),two_torsion_dimension=0,
                cassels_removed_dimension=sha,points=found,independence=independent,
                field=dict(polynomial=polynomial,discriminant=disc,integral_basis=basis,
                           class_group_invariants=class_group,bnfcertify=certified,nfcertify=nfcertified,**order),
                covers=packets,integral_point_completeness=False,
                lean_rank_proof=False,sources=[PARI_DOC,NUMBER_FIELD_DOC])
