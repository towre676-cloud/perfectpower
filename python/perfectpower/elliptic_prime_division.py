"""Complete rational division by the odd primes 5 and 7, and composed division by 2,3,5,7.

Same certificate design as rational_thirds: the rational ell-torsion kernel is
closed by a full rational-root certificate of psi_ell, one exact point of the
target fibre (an anchor) is found or the division equation is certified to
have no admissible root, and the fibre is the anchor's torsion coset. Every
returned point is checked against the generalized group law.

On u=x+A/3 the curve is Y^2=f(u)=u^3+p u+r. With F=4f and the y-free
f_n (psi_n=f_n for odd n, psi_n=2Y f_n for even n),
  f_{2m+1}=F^2 f_{m+2} f_m^3-f_{m-1} f_{m+1}^3   (m even)
  f_{2m+1}=f_{m+2} f_m^3-F^2 f_{m-1} f_{m+1}^3   (m odd)
  f_{2m}=f_m (f_{m+2} f_{m-1}^2-f_{m-2} f_{m+1}^2),
and for odd n, [n]u=phi_n/f_n^2 with phi_n=u f_n^2-F f_{n+1} f_{n-1}.
The division equation phi_ell-(x_T+A/3) f_ell^2 has degree ell^2.
Budgets: a shared root-node budget, a coefficient bit budget, and a branch budget.
"""
from fractions import Fraction as Q
from . import polyalg as P
from .elliptic_arithmetic import (encode_point, q, sqrtq, root_budget,
                                 rational_root_certificate, discovered_roots)
from .divisor_square import WorkLimit

PRIMES = (5, 7)


def short_model(E):
    C, B, A, _ = E.cubic
    p = B - A*A/3
    r = C - A*B/3 + 2*A**3/27
    return p, r, A/3


def y_free_division(p, r, n):
    """f_0..f_n on Y^2=u^3+p u+r (lists of polyalg polynomials)."""
    F = P.scale(P.poly((r, p, Q(0), Q(1))), 4)
    F2 = P.power(F, 2)
    f = {0: P.poly((Q(0),)), 1: P.poly((Q(1),)), 2: P.poly((Q(1),)),
         3: P.poly((-p*p, 12*r, 6*p, Q(0), Q(3))),
         4: P.scale(P.poly((-8*r*r - p**3, -4*p*r, -5*p*p, 20*r, 5*p, Q(0), Q(1))), 2)}
    for k in range(5, n + 2):
        m = k//2
        if k % 2:
            if m % 2 == 0:
                f[k] = P.subtract(P.mul(F2, P.mul(f[m + 2], P.power(f[m], 3))), P.mul(f[m - 1], P.power(f[m + 1], 3)))
            else:
                f[k] = P.subtract(P.mul(f[m + 2], P.power(f[m], 3)), P.mul(F2, P.mul(f[m - 1], P.power(f[m + 1], 3))))
        else:
            f[k] = P.mul(f[m], P.subtract(P.mul(f[m + 2], P.power(f[m - 1], 2)), P.mul(f[m - 2], P.power(f[m + 1], 2))))
    return f, F


def odd_division_polynomials(E, n):
    """psi_n and phi_n in the completed x coordinate, [n]x=phi_n/psi_n^2-A/3 (odd n)."""
    if n % 2 == 0 or n < 3:
        raise ValueError('odd n>=3 required')
    p, r, shift = short_model(E)
    f, F = y_free_division(p, r, n)
    phi = P.subtract(P.mul(P.X, P.power(f[n], 2)), P.mul(F, P.mul(f[n + 1], f[n - 1])))
    return P.compose_linear(f[n], shift, 1), P.compose_linear(phi, shift, 1)


def division_equation(E, n, target):
    psi, phi = odd_division_polynomials(E, n)
    return P.add(phi, P.scale(P.power(psi, 2), -target[0] - E.cubic[2]/3))


def coefficient_bits(f):
    return max((max(abs(c.numerator).bit_length(), c.denominator.bit_length()) for c in f), default=0)


def ordered(points):
    return sorted(set(points), key=lambda h: encode_point(h) or [])


def lifts(E, roots, scalar, target):
    out = []
    for x in roots:
        y = sqrtq(P.evaluate(E.cubic, x))
        if y is not None:
            for yy in sorted({y, -y}):
                h = E.uncomplete((x, yy))
                if E.mul(h, scalar) == target:
                    out.append(h)
    return ordered(out)


def rational_prime_division(E, p, ell, node_limit=100000, bit_limit=4096, *, local_obstructions=False):
    """All rational P with ell P=p (p=None for the ell-torsion kernel), ell in {5,7}."""
    if type(ell) is not int or ell not in PRIMES:
        raise ValueError('ell must be 5 or 7')
    if type(bit_limit) is not int or not 64 <= bit_limit <= 65536:
        raise ValueError('bit limit 64 through 65536 required')
    root_budget(node_limit)
    p = E.checked(p)
    if type(local_obstructions) is not bool:
        raise ValueError('literal local obstruction flag required')
    if local_obstructions:
        from .elliptic_reduction import reduction_obstruction
        obstruction = reduction_obstruction(E, p, ell)
        if obstruction is not None:
            return dict(schema='pp-rational-prime-division/2', curve=E.specification, prime=ell,
                        target=encode_point(p), points=[], complete=True, execution_verified=False,
                        method='good_reduction_obstruction', anchor=None, torsion_certificate=None,
                        division_certificate=None, obstruction_certificate=obstruction,
                        node_limit=node_limit, bit_limit=bit_limit, root_nodes=0)
    psi, _ = odd_division_polynomials(E, ell)
    if coefficient_bits(psi) > bit_limit:
        raise WorkLimit('division polynomial coefficient bit budget exhausted')
    torsion = rational_root_certificate(psi, node_limit)
    used = torsion['integer_certificate']['nodes_checked']
    kernel = ordered([None, *lifts(E, (q(x) for x in torsion['roots']), ell, None)])
    anchor = None
    division = None
    if p is None:
        out = kernel
        method = 'torsion_kernel'
    else:
        f = division_equation(E, ell, p)
        if coefficient_bits(f) > bit_limit:
            raise WorkLimit('division equation coefficient bit budget exhausted')
        for x in discovered_roots(f):
            c = lifts(E, [x], ell, p)
            if c:
                anchor = c[0]
                break
        if anchor is None:
            if used >= node_limit:
                raise WorkLimit('shared division root budget exhausted')
            division = rational_root_certificate(f, node_limit - used)
            used += division['integer_certificate']['nodes_checked']
            c = lifts(E, (q(x) for x in division['roots']), ell, p)
            if c:
                anchor = c[0]
        out = [] if anchor is None else ordered(E.add(anchor, t) for t in kernel)
        method = 'empty_division_fibre' if anchor is None else 'torsion_coset'
    if not all(E.mul(h, ell) == p for h in out):
        raise ArithmeticError('division polynomial/group mismatch')
    return dict(schema='pp-rational-prime-division/1', curve=E.specification, prime=ell,
                target=encode_point(p), points=[encode_point(h) for h in out], complete=True,
                execution_verified=False, method=method, anchor=encode_point(anchor),
                torsion_certificate=torsion, division_certificate=division,
                node_limit=node_limit, bit_limit=bit_limit, root_nodes=used)


def general_factors(scalar):
    if type(scalar) is not int or not 1 <= scalar <= 420:
        raise ValueError('positive scalar 1 through 420 required')
    n, out = scalar, []
    for prime in (2, 3, 5, 7):
        while n % prime == 0:
            out.append(prime)
            n //= prime
    if n != 1:
        raise ValueError('only prime factors 2, 3, 5 and 7 supported')
    return out


def rational_division_general(E, p, scalar, node_limit=100000, branch_limit=64, bit_limit=4096):
    """Staged complete division by any product of 2,3,5,7 with shared budgets."""
    from .elliptic_division import rational_thirds
    fs = general_factors(scalar)
    root_budget(node_limit)
    if type(branch_limit) is not int or not 1 <= branch_limit <= 64:
        raise ValueError('branch limit 1 through 64 required')
    p = E.checked(p)
    frontier, stages, used = [p], [], 0
    for prime in fs:
        packets, out = [], []
        for target in frontier:
            if used >= node_limit:
                raise WorkLimit('shared division root budget exhausted')
            if prime == 2:
                packet = E.rational_halves(target, node_limit - used)
            elif prime == 3:
                packet = rational_thirds(E, target, node_limit - used)
            else:
                packet = rational_prime_division(E, target, prime, node_limit - used, bit_limit)
            used += packet['root_nodes']
            packets.append(packet)
            out.extend(E.checked(h) for h in packet['points'])
            if len(out) > branch_limit:
                raise WorkLimit('division branch budget exhausted')
        nxt = ordered(out)
        stages.append(dict(prime=prime, targets=[encode_point(h) for h in frontier], fibres=packets,
                           points=[encode_point(h) for h in nxt]))
        frontier = nxt
    if not all(E.mul(h, scalar) == p for h in frontier):
        raise ArithmeticError('composed division mismatch')
    return dict(schema='pp-rational-division-general/1', curve=E.specification, target=encode_point(p),
                scalar=scalar, factors=fs, stages=stages, points=[encode_point(h) for h in frontier],
                complete=True, execution_verified=False, node_limit=node_limit, root_nodes=used,
                branch_limit=branch_limit, bit_limit=bit_limit)
