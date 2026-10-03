"""Exact finite residue filters for one- and two-unit orbits.

These are search certificates, not Lean theorems. A period is returned only
when the full matrix returns to the identity modulo m; bounded prefixes fail.
"""
from rank_one_sources import Mx, mm

IDENTITY = [[int(i == j) for j in range(3)] for i in range(3)]


def matrix_period(A, modulus, limit=100000):
    if modulus < 2:
        raise ValueError('modulus must be at least 2')
    A = [[x % modulus for x in row] for row in A]
    X = IDENTITY
    powers = []
    for _ in range(limit):
        powers.append(X)
        X = [[x % modulus for x in row] for row in mm(X, A)]
        if X == IDENTITY:
            return powers
    raise ValueError('no certified period within limit')


def apply(A, gamma):
    return tuple(sum(row[j] * gamma[j] for j in range(3)) for row in A)


def allowed(P, Q, units, gamma, modulus, leading, shift=0, plane=(0,0,1), extra_divisibility=()):
    """Necessary exponent residues for w2=0 and a | w0+h*w1.

    modulus must be a positive multiple of |a|. Negative exponents are
    interpreted modulo the certified periods. Supports rank one or two.
    """
    if leading == 0 or modulus % abs(leading):
        raise ValueError('modulus must be a multiple of nonzero |a|')
    if len(units) not in (1, 2):
        raise ValueError('expected one or two units')
    if any(d < 1 or modulus % d for _,d in extra_divisibility):
        raise ValueError('extra divisors must divide the modulus')
    powers = [matrix_period(Mx(P, Q, eta), modulus) for eta in units]
    rows = []
    for i, A in enumerate(powers[0]):
        for j, B in enumerate(powers[1] if len(powers) == 2 else [IDENTITY]):
            w = apply(mm(A, B), gamma)
            if (sum(plane[t]*w[t] for t in range(3)) % modulus == 0
                    and (w[0] + shift*w[1]) % abs(leading) == 0
                    and all(sum(row[t]*w[t] for t in range(3)) % d == 0 for row,d in extra_divisibility)):
                rows.append([i, j] if len(powers) == 2 else [i])
    return {'modulus': modulus, 'periods': [len(xs) for xs in powers],
            'allowed_residues': rows, 'tested_residues': len(powers[0]) * (len(powers[1]) if len(powers)==2 else 1),
            'status': 'exact Python residue filter; not an exponent bound or Lean certificate'}
