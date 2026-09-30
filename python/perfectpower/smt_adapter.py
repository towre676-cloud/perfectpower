"""A host-solver adapter: replace solved arithmetic conjuncts in an SMT problem by their complete
solution sets.

Given a problem in SMT-LIB 2 (quantifier-free nonlinear integer arithmetic), every top-level
conjunct that is an equality `P = 0` with

    P(n, m) = ± (m^2 - F(n)),   F(n) = (r n + s)^3 + k,   F integral,

is recognized (`compiler.match_affine_cube`).  If `y^2 = x^3 + k` has a complete integral-point
list proved in Lean (`compiler.mordell_complete`: the solved-family registry, the 1163 curves
without points, and the hand-proved curves), the conjunct is replaced by the exact finite
disjunction of its integer solutions (`n` ranges over **all** integers here), or by `false`:

    m^2 = F(n)  <=>  OR_{(t, y) in L, r | t - s} (n = (t - s)/r  and  m = y).

**Justification of one replacement:** the cited Lean theorem gives the complete list `L` of the
curve, and the identity `F(n) = (r n + s)^3 + k` is checked exactly by the adapter (polynomial
coefficients).  The adapter does not emit a Lean proof of the *replacement*; that step is the
elementary substitution `x = r n + s`.  Every other conjunct is left to the host solver unchanged,
and an unrecognized problem is returned unchanged.

Requires the `z3-solver` package (imported lazily); nothing else in the repository depends on it.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

from .compiler import match_affine_cube, mordell_complete


Poly = dict  # {tuple of (var, exp) pairs sorted: coefficient}


def _mono_mul(a, b):
    d = dict(a)
    for v, e in b:
        d[v] = d.get(v, 0) + e
    return tuple(sorted(d.items()))


def _pmul(p, q):
    out = {}
    for ma, ca in p.items():
        for mb, cb in q.items():
            m = _mono_mul(ma, mb)
            out[m] = out.get(m, 0) + ca * cb
    return {m: c for m, c in out.items() if c}


def _padd(p, q, sign=1):
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, 0) + sign * c
    return {m: c for m, c in out.items() if c}


class Unsupported(Exception):
    pass


def to_poly(e) -> Poly:
    """A z3 integer arithmetic term as an exact polynomial, or Unsupported."""
    import z3
    if z3.is_int_value(e):
        v = e.as_long()
        return {(): v} if v else {}
    if z3.is_rational_value(e):          # a Real numeral: accepted only when it is an integer
        if e.denominator_as_long() != 1:
            raise Unsupported('non-integer numeral')
        v = e.numerator_as_long()
        return {(): v} if v else {}
    if z3.is_const(e) and e.sort() == z3.IntSort():
        return {((str(e), 1),): 1}
    k = e.decl().kind()
    if k == z3.Z3_OP_TO_REAL:            # z3py's `**` on Int terms coerces to Real
        return to_poly(e.arg(0))
    args = [to_poly(a) for a in e.children()] if k != z3.Z3_OP_POWER else None
    if k == z3.Z3_OP_ADD:
        out = {}
        for a in args:
            out = _padd(out, a)
        return out
    if k == z3.Z3_OP_SUB:
        out = args[0]
        for a in args[1:]:
            out = _padd(out, a, -1)
        return out
    if k == z3.Z3_OP_UMINUS:
        return {m: -c for m, c in args[0].items()}
    if k == z3.Z3_OP_MUL:
        out = {(): 1}
        for a in args:
            out = _pmul(out, a)
        return out
    if k == z3.Z3_OP_POWER:
        base, ex = e.children()
        ex = to_poly(ex)
        if set(ex) - {()} or ex.get((), 0) < 0:
            raise Unsupported('power')
        out, b = {(): 1}, to_poly(base)
        for _ in range(ex.get((), 0)):
            out = _pmul(out, b)
        return out
    raise Unsupported(str(e.decl()))


def recognize(P: Poly):
    """(n, m, F as coefficient list low->high) with P = ±(m^2 - F(n)), else None."""
    vars_ = sorted({v for mono in P for v, _ in mono})
    if len(vars_) != 2:
        return None
    for m in vars_:
        n = vars_[0] if vars_[1] == m else vars_[1]
        for sign in (1, -1):
            Q = {mono: sign * c for mono, c in P.items()}
            if Q.get(((m, 2),)) != 1:
                continue
            rest = {mono: c for mono, c in Q.items() if mono != ((m, 2),)}
            if any(v != n for mono in rest for v, _ in mono):
                continue
            deg = max((e for mono in rest for _, e in mono), default=0)
            F = [0] * (deg + 1)
            for mono, c in rest.items():
                F[mono[0][1] if mono else 0] = -c
            return n, m, F
    return None


@dataclass
class Replacement:
    conjunct: str
    n: str
    m: str
    substitution: str
    curve: str
    solutions: list
    lean: list


@dataclass
class Result:
    assertions: list
    replacements: list = field(default_factory=list)


def reduce_assertions(assertions) -> Result:
    """Split top-level conjunctions; replace every recognized solved conjunct."""
    import z3
    flat, todo = [], list(assertions)
    while todo:
        a = todo.pop(0)
        if z3.is_and(a):
            todo = list(a.children()) + todo
        else:
            flat.append(a)
    out = Result(assertions=[])
    for a in flat:
        rep = None
        if z3.is_eq(a) and a.arg(0).sort() in (z3.IntSort(), z3.RealSort()):  # variables must be Int
            try:
                P = _padd(to_poly(a.arg(0)), to_poly(a.arg(1)), -1)
                rec = recognize(P)
            except Unsupported:
                rec = None
            if rec is not None:
                n, m, F = rec
                F = tuple(F) + (0,) * max(0, 4 - len(F))
                mac = match_affine_cube(F) if len(F) == 4 else None
                if mac is not None:
                    r, s, k = mac
                    solved = mordell_complete(k)
                    if solved is not None:
                        T, lean = solved
                        sols = sorted((Fraction(t - s, r), sg * y) for t, ys in T.items() for y in ys
                                      for sg in ((1, -1) if y else (1,)) if (t - s) % r == 0)
                        sols = [(int(x), y) for x, y in sols]
                        N, Mv = z3.Int(n), z3.Int(m)
                        new = z3.Or([z3.And(N == x, Mv == y) for x, y in sols]) if sols else z3.BoolVal(False)
                        rep = Replacement(conjunct=str(a), n=n, m=m, substitution=f'x = {r}*{n} + ({s})',
                                          curve=f'y^2 = x^3 + ({k})', solutions=sols, lean=lean)
                        out.assertions.append(new)
                        out.replacements.append(rep)
        if rep is None:
            out.assertions.append(a)
    return out


def reduce_smt2(text: str) -> Result:
    import z3
    return reduce_assertions(list(z3.parse_smt2_string(text)))
