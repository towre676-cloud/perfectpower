"""Small good-reduction obstructions to rational prime division.

If a rational target has no ell-preimage after good reduction, it has none
over Q. A failed local obstruction search makes no claim. The finite group
is enumerated exactly on the completed model Y^2=x^3+A*x^2+B*x+C.
"""
REDUCTION_PRIMES = (11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97)


def residue(q, modulus):
    return q.numerator % modulus * pow(q.denominator, -1, modulus) % modulus


def reduction_group(E, modulus):
    if type(modulus) is not int or modulus not in REDUCTION_PRIMES:
        raise ValueError('supported small reduction prime required')
    if any(a.denominator % modulus == 0 for a in E.a) or residue(E.discriminant, modulus) == 0:
        raise ValueError('good integral reduction required')
    C, B, A, _ = [residue(a, modulus) for a in E.cubic]
    squares = {}
    for y in range(modulus):
        squares.setdefault(y*y % modulus, []).append(y)
    points = [None]
    for x in range(modulus):
        for y in squares.get((x**3 + A*x*x + B*x + C) % modulus, []):
            points.append((x, y))

    def add(left, right):
        if left is None: return right
        if right is None: return left
        x, y = left; u, v = right
        if x == u and (y+v) % modulus == 0: return None
        if x == u:
            slope = (3*x*x + 2*A*x + B) * pow(2*y, -1, modulus) % modulus
        else:
            slope = (v-y) * pow(u-x, -1, modulus) % modulus
        xx = (slope*slope - A - x - u) % modulus
        return xx, (slope*(x-xx)-y) % modulus

    def multiply(point, scalar):
        out = None
        while scalar:
            if scalar & 1: out = add(out, point)
            point = add(point, point); scalar //= 2
        return out
    return points, multiply


def reduction_obstruction(E, target, ell):
    target = E.complete(E.checked(target))
    if target is None: return None
    for modulus in REDUCTION_PRIMES:
        if modulus == ell or any(a.denominator % modulus == 0 for a in target): continue
        try: points, multiply = reduction_group(E, modulus)
        except ValueError: continue
        # Multiplication is bijective when ell is coprime to the group order.
        if len(points) % ell: continue
        reduced = tuple(residue(a, modulus) for a in target)
        if reduced not in {multiply(h, ell) for h in points}:
            return dict(prime=modulus, group_order=len(points), completed_target=list(reduced))
    return None


def verify_reduction_obstruction(E, target, ell, cert, budget):
    try:
        from .elliptic_certificate_verifier import fields
        fields(cert, 'prime group_order completed_target')
        modulus = cert['prime']
        if type(modulus) is not int or modulus == ell: return False
        budget.charge(100*modulus)
        points, multiply = reduction_group(E, modulus)
        completed = E.complete(E.checked(target))
        if completed is None or any(a.denominator % modulus == 0 for a in completed): return False
        reduced = [residue(a, modulus) for a in completed]
        if type(cert['group_order']) is not int or cert['group_order'] != len(points): return False
        if type(cert['completed_target']) is not list or any(type(a) is not int for a in cert['completed_target']) or cert['completed_target'] != reduced: return False
        return tuple(reduced) not in {multiply(h, ell) for h in points}
    except (ValueError, TypeError, KeyError, ArithmeticError):
        return False
