"""Discovery-free replay for prime-5/7 and composed 2,3,5,7 division packets.

Division polynomials are rebuilt independently of the producer. The producer
uses the short model u=x+A/3. Here, as in Silverman (AEC, Exercise 3.7), the
recurrence runs directly in the original x with b-invariants:
  psi_3=3x^4+b2 x^3+3b4 x^2+3b6 x+b8,
  psi_4/psi_2=2x^6+b2 x^5+5b4 x^4+10b6 x^3+10b8 x^2+(b2 b8-b4 b6)x+(b4 b8-b6^2),
  psi_2^2=B=4x^3+b2 x^2+2b4 x+b6.
Root certificates are replayed by the shared Sturm checker; no search is run.
"""
from fractions import Fraction as Q
from . import polyalg as P
from .elliptic_arithmetic import encode_point, sqrtq
from .elliptic_certificate_verifier import (CheckBudget, fields, exact_int, model,
                                            checked_point, check_rational_roots, _verify_halves)
from .elliptic_division_verifier import _verify_thirds, canonical
from .divisor_square import WorkLimit


def silverman_division(E, n):
    b2, b4, b6, b8 = E.b2, E.b4, E.b6, E.b8
    B = P.poly((b6, 2*b4, b2, Q(4)))
    B2 = P.power(B, 2)
    g = {0: P.poly((Q(0),)), 1: P.poly((Q(1),)), 2: P.poly((Q(1),)),
         3: P.poly((b8, 3*b6, 3*b4, b2, Q(3))),
         4: P.poly((b4*b8 - b6*b6, b2*b8 - b4*b6, 10*b8, 10*b6, 5*b4, b2, Q(2)))}
    for k in range(5, n + 2):
        m = k//2
        if k % 2:
            t1, t2 = P.mul(g[m + 2], P.power(g[m], 3)), P.mul(g[m - 1], P.power(g[m + 1], 3))
            g[k] = P.subtract(P.mul(B2, t1), t2) if m % 2 == 0 else P.subtract(t1, P.mul(B2, t2))
        else:
            g[k] = P.mul(g[m], P.subtract(P.mul(g[m + 2], P.power(g[m - 1], 2)), P.mul(g[m - 2], P.power(g[m + 1], 2))))
    phi = P.subtract(P.mul(P.X, P.power(g[n], 2)), P.mul(B, P.mul(g[n + 1], g[n - 1])))
    return g[n], phi


def _lifted(E, roots, ell, target, budget):
    out = set()
    for x in roots:
        budget.charge()
        y = sqrtq(P.evaluate(E.cubic, x))
        if y is not None:
            for yy in {y, -y}:
                h = E.uncomplete((x, yy))
                if E.mul(h, ell) == target:
                    out.add(h)
    return out


def _bits(f):
    return max((max(abs(c.numerator).bit_length(), c.denominator.bit_length()) for c in f), default=0)


def _verify_prime(cert, budget, node_limit):
    version=cert.get('schema') if type(cert) is dict else None
    local=type(cert) is dict and cert.get('method')=='local_root_obstruction'
    fields(cert, 'schema curve prime target points complete execution_verified method anchor torsion_certificate division_certificate node_limit bit_limit root_nodes'+(' obstruction_certificate' if version=='pp-rational-prime-division/2' else ' local_obstruction' if local else ''))
    if version not in ('pp-rational-prime-division/1','pp-rational-prime-division/2') or cert['complete'] is not True or cert['execution_verified'] is not False:
        return False
    ell = exact_int(cert['prime'], 5, 7)
    if ell not in (5, 7):
        return False
    E = model(cert['curve'])
    target = checked_point(E, cert['target'])
    limit = min(node_limit, exact_int(cert['node_limit'], 1, 100000))
    bit_limit = exact_int(cert['bit_limit'], 64, 65536)
    if version=='pp-rational-prime-division/2':
        from .elliptic_reduction import verify_reduction_obstruction
        return (cert['method']=='good_reduction_obstruction' and cert['points']==[]
                and type(cert['points']) is list and cert['anchor'] is None
                and cert['torsion_certificate'] is None and cert['division_certificate'] is None
                and type(cert['root_nodes']) is int and cert['root_nodes']==0
                and verify_reduction_obstruction(E,target,ell,cert['obstruction_certificate'],budget))
    budget.charge(ell*ell*64)
    psi, phi = silverman_division(E, ell)
    if _bits(psi) > bit_limit:
        return False
    roots, used = check_rational_roots(cert['torsion_certificate'], psi, limit, budget)
    kernel = canonical({None, *_lifted(E, roots, ell, None, budget)})
    anchor = checked_point(E, cert['anchor'])
    division = cert['division_certificate']
    if target is None:
        if cert['method'] != 'torsion_kernel' or anchor is not None or division is not None:
            return False
        expected = kernel
    else:
        f = P.add(phi, P.scale(P.power(psi, 2), -target[0]))
        if _bits(f) > bit_limit:
            return False
        candidates = None
        if division is not None:
            candidates, count = check_rational_roots(division, f, limit - used, budget)
            used += count
        if local:
            if anchor is not None or division is not None or f[-1]!=1:return False
            evidence=cert['local_obstruction'];fields(evidence,'prime root_residues')
            ell=exact_int(evidence['prime'],5,199)
            if any(ell%d==0 for d in range(2,__import__('math').isqrt(ell)+1)):return False
            if any(c.denominator%ell==0 for c in (*f,*E.cubic)):return False
            coefficients=[c.numerator*pow(c.denominator,-1,ell)%ell for c in f]
            cubic=[c.numerator*pow(c.denominator,-1,ell)%ell for c in E.cubic]
            roots=[x for x in range(ell) if P.evaluate(coefficients,x)%ell==0]
            budget.charge(ell*len(f))
            supplied=evidence['root_residues']
            if type(supplied) is not list or any(type(x) is not int for x in supplied) or supplied!=roots:return False
            if any(pow(int(P.evaluate(cubic,x))%ell,(ell-1)//2,ell)!=ell-1 for x in roots):return False
            expected=[]
        elif anchor is None:
            if cert['method'] != 'empty_division_fibre' or candidates is None:
                return False
            if _lifted(E, candidates, ell, target, budget):
                return False
            expected = []
        else:
            if cert['method'] != 'torsion_coset' or E.mul(anchor, ell) != target:
                return False
            if candidates is not None and anchor[0] not in candidates:
                return False
            expected = canonical(E.add(anchor, t) for t in kernel)
    if type(cert['points']) is not list or len(cert['points']) > ell*ell:
        return False
    supplied = [checked_point(E, h) for h in cert['points']]
    return supplied == expected and type(cert['root_nodes']) is int and cert['root_nodes'] == used and used <= limit


def verify_prime_division(cert, *, work_limit=4000000, node_limit=100000):
    try:
        exact_int(node_limit, 1, 100000)
        budget = CheckBudget(work_limit)
        budget.packet(cert)
        return _verify_prime(cert, budget, node_limit)
    except (ValueError, TypeError, KeyError, IndexError, ArithmeticError, WorkLimit):
        return False


def _verify_general(cert, budget, node_limit):
    fields(cert, 'schema curve target scalar factors stages points complete execution_verified node_limit root_nodes branch_limit bit_limit')
    if cert['schema'] != 'pp-rational-division-general/1' or cert['complete'] is not True or cert['execution_verified'] is not False:
        return False
    E = model(cert['curve'])
    target = checked_point(E, cert['target'])
    scalar = exact_int(cert['scalar'], 1, 420)
    n, fs = scalar, []
    for prime in (2, 3, 5, 7):
        while n % prime == 0:
            fs.append(prime)
            n //= prime
    if n != 1 or type(cert['factors']) is not list or any(type(x) is not int for x in cert['factors']) or cert['factors'] != fs:
        return False
    branch = exact_int(cert['branch_limit'], 1, 64)
    bit_limit = exact_int(cert['bit_limit'], 64, 65536)
    limit = min(node_limit, exact_int(cert['node_limit'], 1, 100000))
    used = 0
    if type(cert['stages']) is not list or len(cert['stages']) != len(fs):
        return False
    frontier = [target]
    for prime, stage in zip(fs, cert['stages']):
        fields(stage, 'prime targets fibres points')
        if type(stage['prime']) is not int or stage['prime'] != prime or stage['targets'] != [encode_point(h) for h in frontier]:
            return False
        if type(stage['fibres']) is not list or len(stage['fibres']) != len(frontier):
            return False
        out = []
        for h, packet in zip(frontier, stage['fibres']):
            if type(packet) is not dict or packet.get('curve') != cert['curve'] or packet.get('target') != encode_point(h):
                return False
            if type(packet.get('node_limit')) is not int or packet['node_limit'] != cert['node_limit'] - used:
                return False
            if prime == 2:
                ok = _verify_halves(packet, budget, limit - used)
            elif prime == 3:
                ok = _verify_thirds(packet, budget, limit - used)
            else:
                ok = packet.get('bit_limit') == bit_limit and packet.get('prime') == prime and _verify_prime(packet, budget, limit - used)
            if not ok:
                return False
            used += packet['root_nodes']
            out.extend(checked_point(E, v) for v in packet['points'])
            if len(out) > branch:
                return False
        frontier = canonical(out)
        if stage['points'] != [encode_point(h) for h in frontier]:
            return False
    if type(cert['points']) is not list or cert['points'] != [encode_point(h) for h in frontier]:
        return False
    budget.charge(len(frontier)*scalar)
    return (type(cert['root_nodes']) is int and cert['root_nodes'] == used and used <= limit
            and all(E.mul(h, scalar) == target for h in frontier))


def verify_general_division(cert, *, work_limit=8000000, node_limit=100000):
    try:
        exact_int(node_limit, 1, 100000)
        budget = CheckBudget(min(work_limit, 20000000))
        budget.packet(cert)
        return _verify_general(cert, budget, node_limit)
    except (ValueError, TypeError, KeyError, IndexError, ArithmeticError, WorkLimit):
        return False
