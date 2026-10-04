"""Specialized from: 4*n^6 - 24000000000000000000000000000000*n^5 + 59999999999999999999999999999999999999999999999999999999999992*n^4 - 79999999999999999999999999999999999999999999999999999999999968000000000000000000000000000000*n^3 + 59999999999999999999999999999999999999999999999999999999999952000000000000000000000000000000000000000000000000000000000004*n^2 - 23999999999999999999999999999999999999999999999999999999999968000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000*n + 3999999999999999999999999999999999999999999999999999999999992000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000025 = m^2,  n >= 1, m in Z
status: COMPLETE_FINITE; method: factor pairs and complete integer polynomial fibres
justification:
  PerfectPower.NativeDivisorSquare.complete
  Python instance; execution is not verified
The Python below is generated; it is not itself formally verified."""
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

# complete finite list (factor pairs and complete integer polynomial fibres)
HITS = {999999999999999999999999999998: [13], 999999999999999999999999999999: [5], 1000000000000000000000000000000: [5], 1000000000000000000000000000001: [5], 1000000000000000000000000000002: [13]}

def reduced(N):
    return {n: ms for n, ms in HITS.items() if n <= N}

def back(n, ms):
    return sorted(set(ms) | {-m for m in ms}) if True else sorted(ms)


def run(N):
    out = []
    for n, ms in sorted(reduced(N).items()):
        ws = back(n, ms)
        if ws:
            out.append((n, ws))
    return out
