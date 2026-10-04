from math import isqrt

def iroot(v, d):
    """Integer r with r^d = v, or None (exact)."""
    if v < 0:
        if d % 2 == 0:
            return None
        r = iroot(-v, d)
        return None if r is None else -r
    if d == 2:
        r = isqrt(v)
        return r if r*r == v else None
    lo, hi = 0, 1
    while hi ** d <= v:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** d <= v:
            lo = mid
        else:
            hi = mid
    return lo if lo ** d == v else None


def run(N):
    out = []
    for n in range(1, N + 1):
        v = (2*(n-1000000000000000000000000000000)**3-2*(n-1000000000000000000000000000000))**2+25
        r = iroot(v, 2)
        if r is not None:
            out.append((n, sorted({r, -r}) if True else [r]))
    return out
