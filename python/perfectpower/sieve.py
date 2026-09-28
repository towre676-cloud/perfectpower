"""Sieved exhaustive scan: all n in [lo, hi) with F(n) a perfect d-th power, exactly.

A residue r modulo m is discarded when F(r) mod m is not a d-th power residue modulo m.  That is
sound: if F(n) = y^d then F(n) = y^d (mod m) for every m, so no hit is ever discarded.  The
surviving n (typically well under 1e-3 of the range) are then tested exactly with integer roots.
The sieve uses bytearray slice assignment, so it runs at C speed in the standard library; a
range of 10^8 takes seconds, which makes "scan evidence" up to 10^8 cheap.

The result is EXACT_WITHIN_BOUND: complete for [lo, hi) and silent beyond it.
"""
from __future__ import annotations

from .core import integer_power_root

MODULI = (64, 63, 65, 11, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83)
CHUNK = 1 << 24


def _ev(f, n):
    r = 0
    for c in reversed(f):
        r = r * n + c
    return r


def _bad_residues(f, d, m):
    powers = {pow(x, d, m) for x in range(m)}
    return [r for r in range(m) if _ev(f, r) % m not in powers]


def sieve_hits(f, d: int, hi: int, lo: int = 1, moduli=MODULI):
    """Exact list of n in [lo, hi) with F(n) a d-th power (F given low-to-high)."""
    f = list(f)
    bad = [(m, rs) for m in moduli for rs in (_bad_residues(f, d, m),) if rs]
    out = []
    start = lo
    while start < hi:
        size = min(CHUNK, hi - start)
        mask = bytearray(b'\x01') * size
        for m, rs in bad:
            for r in rs:
                off = (r - start) % m
                if off < size:
                    mask[off::m] = bytes(len(range(off, size, m)))
        pos = mask.find(1)
        while pos != -1:
            n = start + pos
            if integer_power_root(_ev(f, n), d) is not None:
                out.append(n)
            pos = mask.find(1, pos + 1)
        start += size
    return out
