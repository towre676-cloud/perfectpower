"""Exact quadratic projection and the proved Beukers–Tengely mixed example.

The 49-coordinate bound is proved by PerfectPower.MixedRunge.coordinate_bound.
Python execution is not a proof; the Lean audit checks the complete four points.
"""
from math import isqrt


def quadratic_roots(a, b, c):
    """All distinct integer roots; degenerate zero polynomial raises."""
    if any(type(z) is not int for z in (a, b, c)):
        raise ValueError('integer coefficients required')
    if a == 0:
        if b == 0:
            if c == 0:
                raise ValueError('zero polynomial has infinitely many roots')
            return []
        return [-c//b] if c % b == 0 else []
    delta = b*b-4*a*c
    if delta < 0:
        return []
    r = isqrt(delta)
    if r*r != delta:
        return []
    return sorted({(w-b)//(2*a) for w in {r, -r} if (w-b) % (2*a) == 0})


def equation(x, y):
    return y**4+2*y**3-9*x*x*y*y+2*x*y-15*x-7 == 0


def solve_example():
    points = sorted((x, y) for y in range(-25, 24)
                    for x in quadratic_roots(-9*y*y, 2*y-15, y**4+2*y**3-7))
    return {'points': points, 'complete': True, 'execution_verified': False,
            'coordinate': 'y', 'coordinate_interval': [-25, 23],
            'fibres_examined': 49, 'theorem': 'PerfectPower.MixedRunge.complete',
            'source': 'Beukers–Tengely (2005), Section 5',
            'method': 'quadratic projection and proved square-gap tails'}
