"""Refined resolution of affine-face systems left incomplete by bernstein_boxes.

`solve_affine_faces` closes a system {F=0, a*y+B(x)=0} on a box [xa,xb]x[yc,yd]
when the exact remainder R(x)=F(x,-B(x)/a) has one weak Bernstein sign and its
zeros lie only on the faces x=xa or x=xb ("face-only property").  This module
decides the remaining cases exactly instead of refining Bernstein tensors:

* R identically zero: every point of the graph y=-B(x)/a solves the system.  An
  exact rational interior point is a counterexample to the face-only property.
* R nonzero: exact Sturm isolation (rational endpoints) of every distinct real
  root of the squarefree part in [xa,xb].  An interior root is enclosed by an
  Arb Krawczyk/interval-Newton ball inside its isolating interval; the exact sign
  change gives existence, the Sturm count gives uniqueness and completeness.

In both cases the face-only property is certified FALSE (it is not weakened),
and the complete real zero set and complete integer model list are certified by
a different route, recorded with its own verifier.  Nothing here is Lean checked.
"""
from fractions import Fraction as Q
from math import floor, ceil
from . import bernstein_boxes as B
from . import polyalg as P

SCHEMA = 'pp-affine-face-refined/1'


def _sign(v):
    return (v > 0) - (v < 0)


def _peval(p, x):
    out = Q(0)
    for c in reversed(p):
        out = out*x + c
    return out


def _variations(chain, x):
    signs = [s for s in (_sign(_peval(p, x)) for p in chain) if s]
    return sum(1 for u, v in zip(signs, signs[1:]) if u != v)


def _count(chain, lo, hi):
    """Distinct roots of the squarefree chain head in (lo, hi]."""
    return _variations(chain, lo) - _variations(chain, hi)


def isolate(p, lo, hi, width=Q(1, 2**20), limit=4096):
    """Exact isolating intervals for the distinct real roots of p in [lo, hi].

    Returns (exact_roots, intervals): exact rational roots found at bisection
    points, and open intervals (l, h) each containing exactly one root and no
    endpoint root.  Every root in [lo, hi] is listed exactly once.
    """
    p = P.poly(p)
    if P.is_zero(p):
        raise ValueError('zero polynomial has no isolated roots')
    sq = P.exact_div(p, P.gcd_poly(p, P.derivative(p))) if P.degree(p) > 0 else p
    chain = [P.poly(c) for c in P.sturm_chain(sq)] if P.degree(sq) > 0 else [sq]
    exact = sorted({x for x in (Q(lo), Q(hi)) if _peval(sq, x) == 0})
    out = []
    stack = [(Q(lo), Q(hi))]
    steps = 0
    while stack:
        l, h = stack.pop()
        n = _count(chain, l, h) - (1 if _peval(sq, h) == 0 else 0)
        if n == 0:
            continue
        if n == 1 and h - l <= width and _peval(sq, l)*_peval(sq, h) < 0:
            out.append((l, h))
            continue
        steps += 1
        if steps > limit:
            raise ValueError('isolation work limit')
        m = (l + h)/2
        if _peval(sq, m) == 0:
            exact.append(m)
        stack.append((m, h))
        stack.append((l, m))
    return sorted(set(exact)), sorted(out), [list(map(str, c)) for c in chain]


def newton_ball(p, l, h, prec=192, rounds=40):
    """Interval-Newton enclosure of the unique root of p in (l, h) as an Arb ball.

    Existence and uniqueness follow when, for some iterate X, p' excludes 0 on X
    and the Newton image N(X)=m-p(m)/p'(X) lies in the interior of X.
    """
    from flint import arb, ctx, fmpq
    old = ctx.prec
    ctx.prec = prec
    try:
        def ev(q, x):
            v = arb(0)
            for c in reversed(q):
                v = v*x + arb(fmpq(c.numerator, c.denominator))
            return v
        p = P.poly(p)
        dp = P.derivative(p)
        X = arb(fmpq(l.numerator, l.denominator)).union(arb(fmpq(h.numerator, h.denominator)))
        proved = False
        for _ in range(rounds):
            d = ev(dp, X)
            if d.contains(0):
                break
            m = arb(X.mid())
            N = m - ev(p, m)/d
            if N.lower() > X.lower() and N.upper() < X.upper():
                proved = True
            if not N.overlaps(X):
                return X, False
            new = N.intersection(X)
            if new.rad() >= X.rad():
                X = new
                break
            X = new
        return X, proved
    finally:
        ctx.prec = old


def _poly_x(R):
    """Univariate ascending coefficients of an x-only bivariate dict."""
    if any(j for (i, j) in R):
        raise ValueError('remainder depends on y')
    deg = max((i for (i, j) in R), default=-1)
    return [R.get((i, 0), Q(0)) for i in range(deg + 1)]


def refine(equations, box, prec=192, width=Q(1, 2**40)):
    eqs = [B.poly(p) for p in equations]
    xa, xb, yc, yd = B.rectangle(box)
    base = B.solve_affine_faces(equations, box)
    for j, G in enumerate(eqs):
        if set(k for k in G if k[1]) != {(0, 1)}:
            continue
        for i, F in enumerate(eqs):
            if i == j:
                continue
            quotient, remainder = B.affine_remainder(F, G)
            a = G[0, 1]
            Bx = {k: c for k, c in G.items() if not k[1]}

            def yof(x):
                return -B.evaluate(Bx, x, 0)/a

            def solves(x, y):
                return all(B.evaluate(eq, x, y) == 0 for eq in eqs)

            packet = dict(schema=SCHEMA, equations=[B.encode(e) for e in eqs], box=list(map(str, (xa, xb, yc, yd))),
                          eliminated_equation=j, source_equation=i, quotient=B.encode(quotient),
                          remainder=B.encode(remainder), original_complete=base['complete'],
                          original_verified=B.verify_affine_faces(base), kernel_checked=False)
            if not remainder:
                # identical vanishing on the whole graph y=-B(x)/a
                x0 = (xa + xb)/2
                y0 = yof(x0)
                interior = xa < x0 < xb and yc < y0 < yd and solves(x0, y0)
                lo_int, hi_int = ceil(xa), floor(xb)
                if hi_int - lo_int > 10**6:
                    raise ValueError('integer x-range budget')
                models = [[x, int(yof(x))] for x in range(lo_int, hi_int + 1)
                          if yof(x).denominator == 1 and yc <= yof(x) <= yd and solves(x, yof(x))]
                packet.update(route='identical_vanishing_graph', face_only_property=False,
                              face_only_certificate=dict(kind='exact_interior_point', x=str(x0), y=str(y0), interior=interior),
                              real_zero_set=dict(kind='graph', y_of_x=B.encode({k: c/(-a) for k, c in Bx.items()}),
                                                 x_range=[str(xa), str(xb)]),
                              models=models, integer_models_complete=True)
                packet['face_only_certified_false'] = interior
                return packet
            R = _poly_x(remainder)
            exact, intervals, chain = isolate(R, xa, xb, width=width)
            interior_roots = []
            for (l, h) in intervals:
                if not (xa < l and h < xb):
                    continue
                ball, newton = newton_ball(P.exact_div(P.poly(R), P.gcd_poly(P.poly(R), P.derivative(P.poly(R)))) if P.degree(P.poly(R)) > 0 else R, l, h, prec)
                # y interval: y=-B(x)/a over [l,h], bounded by exact evaluation of a monotone bound
                ys = [yof(l), yof(h)]
                yl, yh = min(ys), max(ys)
                Bdeg = max((k[0] for k in Bx), default=0)
                in_y = Bdeg <= 1 and yc < yl and yh < yd
                interior_roots.append(dict(isolating_interval=[str(l), str(h)],
                                           sign_change=[_sign(_peval(R, l)), _sign(_peval(R, h))],
                                           arb_ball=ball.str(40, radius=True), newton_contraction=newton,
                                           y_interval=[str(yl), str(yh)], y_inside_open_box=in_y,
                                           contains_integer=ceil(l) <= floor(h)))
            for x in exact:
                if xa < x < xb:
                    interior_roots.append(dict(exact_root=str(x), y=str(yof(x)), y_inside_open_box=yc < yof(x) < yd,
                                               sign_change=None, contains_integer=x.denominator == 1))
            face_roots = [str(x) for x in exact if x in (xa, xb)]
            # Complete integer models: exact roots that are integers, plus
            # isolating intervals containing an integer k with R(k)=0.
            candidates = set(x for x in exact if x.denominator == 1)
            for (l, h) in intervals:
                for k in range(ceil(l), floor(h) + 1):
                    if _peval(R, Q(k)) == 0:
                        candidates.add(Q(k))
            models = [[int(x), int(yof(x))] for x in sorted(candidates)
                      if yof(x).denominator == 1 and yc <= yof(x) <= yd and solves(x, yof(x))]
            witness = next((r for r in interior_roots if r['y_inside_open_box'] and (r.get('sign_change') is None or r['newton_contraction'])), None)
            packet.update(route='sturm_isolation', squarefree_sturm_chain=chain, face_roots=face_roots,
                          interior_roots=interior_roots, distinct_real_roots=len(exact) + len(intervals),
                          face_only_property=not interior_roots,
                          face_only_certificate=None if witness is None else dict(kind='interior_root', root=witness),
                          models=models, integer_models_complete=True)
            packet['face_only_certified_false'] = witness is not None
            return packet
    raise ValueError('no affine elimination available')


def verify(packet):
    """Replay a refined packet from its equations and box (exact recomputation)."""
    try:
        if packet.get('schema') != SCHEMA or packet.get('kernel_checked') is not False:
            return False
        eqs = [B.poly(e) for e in packet['equations']]
        G, F = eqs[packet['eliminated_equation']], eqs[packet['source_equation']]
        q, r = B.poly(packet['quotient']), B.poly(packet['remainder'])
        if B.add(B.mul(q, G), r) != F or any(j for (i, j) in r):
            return False
        expect = refine(packet['equations'], packet['box'])
        if expect != packet:
            return False
        if packet['face_only_certified_false']:
            c = packet['face_only_certificate']
            if c['kind'] == 'exact_interior_point':
                x, y = Q(c['x']), Q(c['y'])
                xa, xb, yc, yd = map(Q, packet['box'])
                if not (xa < x < xb and yc < y < yd and all(B.evaluate(e, x, y) == 0 for e in eqs)):
                    return False
            elif 'exact_root' in c['root']:
                x, y = Q(c['root']['exact_root']), Q(c['root']['y'])
                xa, xb, yc, yd = map(Q, packet['box'])
                if not (xa < x < xb and yc < y < yd and all(B.evaluate(e, x, y) == 0 for e in eqs)):
                    return False
            else:
                l, h = map(Q, c['root']['isolating_interval'])
                R = _poly_x(r)
                if _peval(R, l)*_peval(R, h) >= 0:
                    return False
        return True
    except (KeyError, ValueError, TypeError, IndexError, ZeroDivisionError):
        return False


def corpus():
    """The 144-case affine-face corpus of develop_metric_boxes.py, in order."""
    out = []
    for d in range(2, 8):
        for power in range(2, 10):
            for a in [1, 2, -1]:
                out.append((d, power, a, [[(0, d, 1), (power, 0, -1)], [(0, 1, a), (1, 0, -1)]]))
    return out
