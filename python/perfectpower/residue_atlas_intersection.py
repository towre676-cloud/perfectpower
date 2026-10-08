"""Exact fiber products of complete residue atlases, including shared factors.

Constraints may have different source polynomials. No lcm-square census is
used: gcd fibers are joined and each compatible pair has one CRT lift.
"""
from collections import defaultdict
from math import gcd, lcm
import json
from .residue_atlas import verify_atlas, _canonical_equal, _parameter, _bounds, _axis_count
from .residue_atlas_product import verify_product
from .residue_determinant import integer


def generalized_crt(a, b, m, n):
    """Canonical common residue, or None when the gcd compatibility fails."""
    if any(type(z) is not int for z in (a, b, m, n)) or m <= 0 or n <= 0:
        raise ValueError('integer residues and positive integer moduli required')
    g = gcd(m, n)
    if (b-a) % g:
        return None
    q = n//g
    t = 0 if q == 1 else ((b-a)//g * pow(m//g, -1, q)) % q
    return (a+m*t) % lcm(m, n)


def _flatten(inputs):
    if not isinstance(inputs, list) or not 1 <= len(inputs) <= 8:
        raise ValueError('one through eight atlas constraints required')
    locals_ = []
    for packet in inputs:
        if verify_atlas(packet):
            locals_.append(packet)
        elif verify_product(packet):
            locals_.extend(packet['locals'])
        else:
            raise ValueError('invalid complete atlas or atlas product')
    return locals_


def _build(inputs, budget):
    locals_ = _flatten(inputs)
    roots, m, used, stages = [(0, 0)], 1, 0, []
    for atlas in locals_:
        n = atlas['modulus']; g = gcd(m, n); period = lcm(m, n)
        fibers = defaultdict(list)
        for x, y in atlas['roots']:
            used += 1
            if used > budget:
                raise ValueError('intersection exceeds work budget; no partial result')
            fibers[x % g, y % g].append((x, y))
        joined = []
        for a, b in roots:
            used += 1
            if used > budget:
                raise ValueError('intersection exceeds work budget; no partial result')
            for x, y in fibers[a % g, b % g]:
                used += 1
                if used > budget:
                    raise ValueError('intersection exceeds work budget; no partial result')
                joined.append((generalized_crt(a, x, m, n), generalized_crt(b, y, m, n)))
        stages.append({'left_modulus': m, 'right_modulus': n, 'gcd': g,
                       'lcm': period, 'left_count': len(roots),
                       'right_count': len(atlas['roots']), 'compatible_count': len(joined)})
        roots, m = sorted(joined), period
    return {'schema': 'pp-residue-atlas-intersection/1',
            'inputs': json.loads(json.dumps(inputs)), 'modulus': m,
            'roots': [list(z) for z in roots], 'stages': stages, 'work_limit': budget,
            'work': used, 'complete_modular_cover': True,
            'global_obstruction': not roots, 'global_height_bound': False,
            'execution_verified': False}


def intersect_atlases(inputs, *, work_limit=200000):
    return _build(inputs, _parameter(work_limit, 'work_limit', 2000000))


def verify_intersection(packet):
    try:
        budget = _parameter(packet['work_limit'], 'work_limit', 2000000)
        return _canonical_equal(packet, _build(packet['inputs'], budget))
    except (KeyError, ValueError, TypeError, IndexError, OverflowError):
        return False


def _prepare(packet, bounds):
    if not verify_intersection(packet):
        raise ValueError('complete atlas intersection required')
    return _bounds(bounds)


def intersection_population(packet, bounds):
    bounds = _prepare(packet, bounds); m = packet['modulus']
    return sum(_axis_count(*bounds[0], m, x)*_axis_count(*bounds[1], m, y)
               for x, y in packet['roots'])


def intersection_select(packet, bounds, index):
    bounds = _prepare(packet, bounds); m = packet['modulus']; index = integer(index, 1024)
    if index < 0:
        raise IndexError('negative candidate rank')
    for a, b in packet['roots']:
        nx, ny = _axis_count(*bounds[0], m, a), _axis_count(*bounds[1], m, b)
        if index < nx*ny:
            u, v = divmod(index, ny)
            return [bounds[0][0]+(a-bounds[0][0]) % m+u*m,
                    bounds[1][0]+(b-bounds[1][0]) % m+v*m]
        index -= nx*ny
    raise IndexError('candidate rank outside population')


def intersection_rank(packet, bounds, point):
    bounds = _prepare(packet, bounds); m = packet['modulus']
    if not isinstance(point, list) or len(point) != 2:
        raise ValueError('two integer coordinates required')
    x, y = [integer(v, 256) for v in point]
    if not (bounds[0][0] <= x <= bounds[0][1] and bounds[1][0] <= y <= bounds[1][1]):
        raise ValueError('point outside bounds')
    offset = 0
    for a, b in packet['roots']:
        nx, ny = _axis_count(*bounds[0], m, a), _axis_count(*bounds[1], m, b)
        if (x % m, y % m) == (a, b):
            x0 = bounds[0][0]+(a-bounds[0][0]) % m
            y0 = bounds[1][0]+(b-bounds[1][0]) % m
            return offset+(x-x0)//m*ny+(y-y0)//m
        offset += nx*ny
    raise ValueError('point fails simultaneous modular constraints')
