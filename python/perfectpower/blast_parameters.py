"""Exact score envelopes, closed normal regions, robust radii and integer grids."""
from fractions import Fraction as Q
from itertools import product
from .psg_polynomial import rational
from .divisor_square import WorkLimit
from .blast_alignment import score, subtract


def support(terms):
    points = sorted(set(tuple(f) for f in terms))
    if not points or any(len(f) != 4 or any(type(x) is not int or x < 0 for x in f) for f in points):
        raise ValueError('nonempty four-dimensional integer feature support required')
    return points


def line_atlas(terms, origin, direction, interval):
    points = support(terms)
    if len(points) > 2048:
        raise WorkLimit('line atlas exceeds 2048 feature summaries')
    if len(origin) != 4 or len(direction) != 4 or len(interval) != 2:
        raise ValueError('four-dimensional score line and two endpoints required')
    origin, direction = tuple(map(rational, origin)), tuple(map(rational, direction))
    low, high = map(rational, interval)
    if low > high:
        raise ValueError('ordered parameter interval required')
    regions = []
    for f in points:
        lo, hi, possible = low, high, True
        for g in points:
            delta = subtract(f, g)
            a, b = score(delta, origin), score(delta, direction)
            if not b:
                if a < 0:
                    possible = False
                    break
            elif b > 0:
                lo = max(lo, -a/b)
            else:
                hi = min(hi, -a/b)
            if lo > hi:
                possible = False
                break
        if possible:
            regions.append({'feature': list(f), 'interval': [str(lo), str(hi)],
                            'slope': str(score(f, direction)), 'intercept': str(score(f, origin)),
                            'boundary_only': lo == hi})
    return {'schema': 'pp-blast-line-atlas/1', 'regions': regions,
            'origin': list(map(str, origin)), 'direction': list(map(str, direction)),
            'interval': [str(low), str(high)], 'complete': True,
            'scope': 'closed optimality regions of supplied feature support; ties retained'}


def _clip(polygon, a, b, c):
    """Clip a convex possibly degenerate polygon by a*x+b*y+c >= 0."""
    if not polygon:
        return []
    out = []
    for first, second in zip(polygon, polygon[1:]+polygon[:1]):
        u = a*first[0]+b*first[1]+c
        v = a*second[0]+b*second[1]+c
        if u >= 0:
            out.append(first)
        if (u < 0 <= v) or (v < 0 <= u):
            t = u/(u-v)
            out.append((first[0]+t*(second[0]-first[0]), first[1]+t*(second[1]-first[1])))
    result = []
    for p in out:
        if p not in result:
            result.append(p)
    return result


def plane_atlas(terms, origin, directions, box):
    points = support(terms)
    if len(points) > 512:
        raise WorkLimit('plane atlas exceeds 512 feature summaries')
    if len(origin) != 4 or len(directions) != 2 or any(len(d) != 4 for d in directions) or len(box) != 2 or any(len(i) != 2 for i in box):
        raise ValueError('four-dimensional score plane and rectangular parameter domain required')
    origin = tuple(map(rational, origin))
    d, e = (tuple(map(rational, v)) for v in directions)
    (xmin, xmax), (ymin, ymax) = [tuple(map(rational, v)) for v in box]
    if xmin > xmax or ymin > ymax:
        raise ValueError('ordered parameter rectangle required')
    regions = []
    for f in points:
        polygon = [(xmin, ymin), (xmax, ymin), (xmax, ymax), (xmin, ymax)]
        for g in points:
            delta = subtract(f, g)
            polygon = _clip(polygon, score(delta, d), score(delta, e), score(delta, origin))
            if not polygon:
                break
        if polygon:
            area = abs(sum(a[0]*b[1]-a[1]*b[0] for a, b in zip(polygon, polygon[1:]+polygon[:1])))/2
            regions.append({'feature': list(f), 'vertices': [[str(x), str(y)] for x, y in polygon],
                            'area': str(area), 'boundary_only': area == 0})
    return {'schema': 'pp-blast-plane-atlas/1', 'regions': regions,
            'origin': list(map(str, origin)), 'directions': [list(map(str, v)) for v in (d, e)],
            'box': [[str(xmin), str(xmax)], [str(ymin), str(ymax)]], 'complete': True,
            'scope': 'exact closed optimality polygons of supplied feature support, including lower-dimensional ties'}


def robustness(terms, scoring):
    points = support(terms)
    values = {f: score(f, scoring) for f in points}
    best = max(values.values())
    winners = [f for f in points if values[f] == best]
    radii = []
    for f in winners:
        distances = [(best-values[g])/sum(abs(x) for x in subtract(f, g)) for g in points if g != f]
        radii.append({'feature': list(f), 'linfinity_radius': str(min(distances)) if distances else None})
    return {'score': str(best), 'winners': radii,
            'scope': 'independent perturbations of all four signed weights; winner remains weakly optimal inside closed radius'}


def integer_grid(terms, ranges, *, constraints=(), residue_filters=(), limit=100000):
    """Query bounded integer score parameters, retaining every tied summary.

    Constraints (coefficients,bound) impose dot(coefficients,w) <= bound;
    residue filters (coordinate,modulus,allowed) apply to signed weights.
    """
    points = support(terms)
    if len(ranges) != 4 or any(len(r) != 2 or any(type(x) is not int for x in r) or r[0] > r[1] for r in ranges):
        raise ValueError('four inclusive ordered integer ranges required')
    size = 1
    for lo, hi in ranges:
        size *= hi-lo+1
    if type(limit) is not int or limit < 1 or size*len(points) > limit:
        raise WorkLimit('integer score grid work budget exceeded')
    constraints = [(tuple(map(rational, c)), rational(b)) for c, b in constraints]
    if any(len(c) != 4 for c, b in constraints):
        raise ValueError('four coefficients per inequality required')
    for i, modulus, allowed in residue_filters:
        if type(i) is not int or not 0 <= i < 4 or type(modulus) is not int or modulus <= 0 or any(type(a) is not int or not 0 <= a < modulus for a in allowed):
            raise ValueError('valid modular filter required')
    out = []
    for w in product(*(range(lo, hi+1) for lo, hi in ranges)):
        if any(score(c, w) > b for c, b in constraints) or any(w[i] % modulus not in allowed for i, modulus, allowed in residue_filters):
            continue
        best = max(score(f, w) for f in points)
        out.append({'weights': list(w), 'score': str(best), 'features': [list(f) for f in points if score(f, w) == best]})
    return {'rows': out, 'count': len(out), 'complete': True, 'scope': 'supplied bounded integer box and filters'}


def normal_regions(terms, *, comparison_limit=100000):
    """Complete four-weight normal-region descriptions, including empty regions.

    Each supplied feature is optimal exactly when every returned homogeneous
    inequality holds. Feasibility, redundancy and full-dimensionality are not
    inferred, so interior points are not mislabelled as polytope vertices.
    """
    points = support(terms)
    if len(points)*len(points) > comparison_limit:
        raise WorkLimit('normal-region comparison budget exceeded')
    return {'schema': 'pp-blast-normal-regions/1',
            'regions': [{'feature': list(f), 'inequalities': [list(subtract(f,g)) for g in points if g!=f]}
                        for f in points],
            'inequality_convention': 'dot(coefficients,signed_weights) >= 0',
            'feasibility_evaluated': False, 'complete': True,
            'scope': 'necessary and sufficient optimality conditions for every supplied feature under all four signed weights'}
