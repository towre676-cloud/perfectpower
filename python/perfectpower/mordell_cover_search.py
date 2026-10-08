"""Find rational witnesses on retained descent covers and lift them exactly.

Search is optional PARI discovery. Only positive witnesses enter rank bounds;
an empty return or timeout is never a global insolubility assertion.
"""
import copy
import json
import subprocess
from math import gcd, lcm
from .elliptic_arithmetic import EllipticCurve, encode_point, q
from .elliptic_two_descent import gp_executable, lift_quartic_point, quartic_map

DOC = 'https://pari.math.u-bordeaux.fr/dochtml/html-stable/Hyperelliptic_curves.html'


def homogeneous_cover_lift(k, cover, coordinates):
    """Weighted integer chart, retaining exactly the integral target domain."""
    quartic_map(k, cover)
    if not isinstance(coordinates,(list,tuple)) or len(coordinates) != 3:
        raise ValueError('three homogeneous integers required')
    if any(type(x) is not int for x in coordinates):
        raise ValueError('three homogeneous integers required')
    u,v,w = coordinates
    if v <= 0 or gcd(u,v) != 1 or not w:
        raise ValueError('primitive abscissa, positive denominator and nonzero ordinate required')
    coefficients = [q(x) for x in cover['quartic']]
    if any(x.denominator != 1 for x in coefficients):
        raise ValueError('integral quartic model required')
    def homogeneous(values,degree):
        return sum(q(x)*u**i*v**(degree-i) for i,x in enumerate(values))
    if homogeneous(coefficients,4) != w*w:
        raise ValueError('homogeneous quartic equation failed')
    nx = [q(x) for x in cover['x_numerator']]
    ny = [q(x) for x in cover['y_numerator']]
    denominators = [x.denominator for x in nx+ny]
    scale = 1 if all(d == 1 for d in denominators) else 2
    if any((scale**2*x).denominator != 1 for x in nx) or any((scale**3*x).denominator != 1 for x in ny):
        scale = lcm(*denominators)
    A = scale**2*homogeneous(nx,4)
    B = scale**3*homogeneous(ny,6)
    if A.denominator != 1 or B.denominator != 1:
        raise ArithmeticError('failed homogeneous denominator clearing')
    A,B = int(A),int(B); dx=scale**2*w*w; dy=scale**3*w**3
    if B*B != A**3+scale**6*k*w**6:
        raise ArithmeticError('integer homogeneous Mordell identity failed')
    target = lift_quartic_point(k,cover,[q(u)/v,q(w)/v**2])
    integral = A%dx == 0 and B%dy == 0
    return dict(coordinates=[u,v,w],scale=scale,A=A,B=B,
                x_denominator=dx,y_denominator=dy,mordell_point=target,
                target_integral=integral,
                integral_point=[A//dx,B//dy] if integral else None)


def affine_homogeneous_lift(k, cover, point):
    t,z = map(q,point); w=z*t.denominator**2
    if w.denominator != 1: raise ValueError('quartic ordinate does not clear integrally')
    return homogeneous_cover_lift(k,cover,[t.numerator,t.denominator,int(w)])


def augment_descent(descent, lifts):
    """Attach exactly checked cover points without changing the descent bound."""
    result = copy.deepcopy(descent)
    if result.get('schema') != 'pp-mordell-two-descent/1':
        raise ValueError('Mordell descent packet required')
    E = EllipticCurve([0, result['k']])
    if E.specification != result['curve']:
        raise ValueError('original Mordell model mismatch')
    points = [encode_point(E.checked(p)) for p in result['points']]
    records = []
    for entry in lifts:
        i = entry['cover_index']
        if type(i) is not int or not 0 <= i < len(result['covers']):
            raise ValueError('cover index outside retained list')
        point = lift_quartic_point(result['k'], result['covers'][i], entry['cover_point'])
        if point != entry['mordell_point']:
            raise ValueError('cover lift mismatch')
        if point not in points: points.append(point)
        record = copy.deepcopy(entry)
        homogeneous = affine_homogeneous_lift(result['k'],result['covers'][i],entry['cover_point'])
        if 'homogeneous' in record and record['homogeneous'] != homogeneous:
            raise ValueError('homogeneous chart mismatch')
        record['homogeneous'] = homogeneous
        records.append(record)
    if len(points) > 64: raise ValueError('at most 64 point witnesses')
    certificate = E.independence(points, prime_bound=500, halving_limit=8)
    lower = certificate['rank_lower_bound']
    upper = result['rank_upper_bound']
    if lower < result['witness_rank_lower_bound'] or lower > upper:
        raise ArithmeticError('new point bounds inconsistent with retained descent')
    result.update(points=points, independence=certificate,
                  witness_rank_lower_bound=lower, rank_determined=lower == upper)
    result.setdefault('cover_point_lifts', []).extend(records)
    return result


def search_mordell_covers(descent, *, height=100000, timeout=5, gp=None):
    """Search each retained affine quartic, stopping at its first found point."""
    if type(height) is not int or not 2 <= height <= 10000000:
        raise ValueError('integer cover height from 2 through 10000000')
    if type(timeout) not in (int, float) or not 0 < timeout <= 60:
        raise ValueError('per-cover timeout from zero through 60 seconds')
    if descent.get('schema') != 'pp-mordell-two-descent/1':
        raise ValueError('Mordell descent packet required')
    k = descent['k']; attempts = []; lifts = []
    for i, cover in enumerate(descent['covers']):
        quartic_map(k, cover)
        # Canonical rational literals prevent arbitrary GP source injection.
        f = '+'.join(f'({q(v)})*x^{j}' for j,v in enumerate(cover['quartic']))
        script = ('default(parisize,128000000);\n'
                  f'R={f};H=hyperellratpoints(R,{height},1);'
                  'print("PP_COVER_POINTS:",vector(#H,i,vector(2,j,Str(H[i][j]))));quit\n')
        attempt = dict(cover_index=i, height=height)
        try:
            p = subprocess.run([gp_executable(gp), '-fq'], input=script,
                               text=True, capture_output=True, timeout=timeout, check=True)
        except subprocess.TimeoutExpired:
            attempts.append(dict(attempt, status='timeout')); continue
        lines = [s.split(':',1)[1] for s in p.stdout.splitlines()
                 if s.startswith('PP_COVER_POINTS:')]
        warning = '***   Warning: new stack size = 128000000 (122.070 Mbytes).'
        if len(lines) != 1 or '***' in p.stderr.replace(warning, ''):
            raise RuntimeError('PARI cover search failed: '+p.stderr[:400])
        found = json.loads(lines[0])
        if type(found) is not list or len(found) > 1:
            raise ArithmeticError('first-point search returned invalid point list')
        attempt['status'] = 'no_point_returned' if not found else 'point_returned'
        for point in found:
            if not q(point[1]):
                attempt['status'] = 'exceptional_zero_ordinate'; continue
            x = q(point[0])
            if max(abs(x.numerator), x.denominator) > height:
                raise ArithmeticError('cover point outside requested height')
            target = lift_quartic_point(k, cover, point)
            lifts.append(dict(cover_index=i, cover_point=point, mordell_point=target,
                              homogeneous=affine_homogeneous_lift(k,cover,point)))
        attempts.append(attempt)
    return dict(schema='pp-mordell-cover-search/1', k=k, height=height,
                timeout_per_cover=timeout, attempts=attempts, lifts=lifts,
                global_empty_proof=False, integral_point_completeness=False,
                source=DOC)
