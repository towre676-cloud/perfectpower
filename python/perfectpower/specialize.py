"""Program specialization: replace a brute-force loop by the program its arithmetic dictates.

The input language is deliberately narrow.  A LoopProgram is

    for n in 1..N:  if TEST(expr(n)): record n and its witnesses

where expr is an integer polynomial in n written with + - * ** (constant exponents) and integer
literals, and TEST is one of

    ('power', d)            expr = m^d for an integer m                  witnesses: m
    ('triangular', dom)     expr = y (y+1)/2 for an integer y in dom      witnesses: y
    ('root', a, b, c, dom)  a y^2 + b y + c = expr for an integer y in dom witnesses: y

original_source() writes the brute-force program.  specialize() compiles the constraint
(compiler.compile_constraint) and writes a standalone program from the plan: a literal list, a
linear test from a transported completeness theorem, a radical parametrization, or Pell-orbit
iteration, followed by the backward maps of the reductions.  Both are plain Python using exact
integers; `run(N)` returns [(n, witnesses)].  A plan without an enumeration (NOT_ENUMERATED) is
not specialized.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass

from .compiler import (COMPLETE_FINITE, NOT_ENUMERATED, STRUCTURED_FILTERED, STRUCTURED_INFINITE,
                       CLASSIFIED_FINITE, PowerConstraint, QuadraticRootConstraint,
                       TriangularConstraint, compile_constraint, padd, pmul, ppow, pscale, _trim)


# ---------------------------------------------------------------------------
# expressions
# ---------------------------------------------------------------------------

def parse_poly(src: str, var: str = 'n') -> tuple[int, ...]:
    """Integer polynomial (low to high) from a restricted Python expression."""
    def go(node):
        if isinstance(node, ast.Expression):
            return go(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
            return (node.value,)
        if isinstance(node, ast.Name) and node.id == var:
            return (0, 1)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            p = go(node.operand)
            return pscale(p, -1) if isinstance(node.op, ast.USub) else p
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                e = go(node.right)
                if len(e) != 1 or e[0] < 0:
                    raise ValueError('exponents must be nonnegative integer constants')
                return ppow(go(node.left), e[0])
            left, right = go(node.left), go(node.right)
            if isinstance(node.op, ast.Add):
                return padd(left, right)
            if isinstance(node.op, ast.Sub):
                return padd(left, pscale(right, -1))
            if isinstance(node.op, ast.Mult):
                return pmul(left, right)
        raise ValueError(f'unsupported syntax: {ast.dump(node)}')
    return _trim(go(ast.parse(src, mode='eval')))


@dataclass(frozen=True)
class LoopProgram:
    expr: str
    test: tuple

    def constraint(self):
        F = parse_poly(self.expr)
        kind = self.test[0]
        if kind == 'power':
            return PowerConstraint(F, self.test[1])
        if kind == 'triangular':
            return TriangularConstraint(F, self.test[1])
        if kind == 'root':
            _, a, b, c, dom = self.test
            return QuadraticRootConstraint(a, b, c, F, dom)
        raise ValueError(kind)


_HELPERS = '''from math import isqrt

def iroot(v, d):
    """Integer r with r^d = v, or None (exact)."""
    if v < 0:
        if d % 2 == 0:
            return None
        r = iroot(-v, d)
        return None if r is None else -r
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
'''

_DOMAIN_SRC = {'int': 'True', 'nonneg': 'y >= 0', 'pos': 'y >= 1'}


def original_source(prog: LoopProgram) -> str:
    """The brute-force loop, testing every n."""
    kind = prog.test[0]
    if kind == 'power':
        d = prog.test[1]
        test = (f'        r = iroot(v, {d})\n'
                f'        if r is not None:\n'
                f'            out.append((n, sorted({{r, -r}}) if {d % 2 == 0} else [r]))\n')
    else:
        if kind == 'triangular':
            a, b, c, dom = 1, 1, 0, prog.test[1]
            rhs = '2 * v'
        else:
            _, a, b, c, dom = prog.test
            rhs = 'v'
        test = (f'        disc = ({b}) ** 2 - 4 * ({a}) * (({c}) - {rhs})\n'
                f'        s = isqrt(disc) if disc >= 0 else -1\n'
                f'        if s >= 0 and s * s == disc:\n'
                f'            ys = sorted({{(m - ({b})) // ({2 * a}) for m in (s, -s)\n'
                f'                         if (m - ({b})) % ({2 * a}) == 0}})\n'
                f'            ys = [y for y in ys if {_DOMAIN_SRC[dom]}]\n'
                f'            if ys:\n'
                f'                out.append((n, ys))\n')
    return (_HELPERS + '\n\ndef run(N):\n    out = []\n    for n in range(1, N + 1):\n'
            f'        v = {prog.expr}\n' + test + '    return out\n')


# ---------------------------------------------------------------------------
# specialized programs
# ---------------------------------------------------------------------------

def _back_source(plan) -> str:
    """Source of `back(n, ms)`: the composed backward maps of the plan's reductions."""
    con = plan.original
    if isinstance(con, PowerConstraint):
        d = con.d
        return ('def back(n, ms):\n'
                f'    return sorted(set(ms) | {{-m for m in ms}}) if {d % 2 == 0} else sorted(ms)\n')
    if isinstance(con, TriangularConstraint):
        return ('def back(n, ms):\n'
                '    # m^2 = 8F + 1 forces m odd: y = (m - 1) / 2 is always an integer\n'
                '    ys = {(m - 1) // 2 for m in set(ms) | {-m for m in ms}}\n'
                f'    return sorted(y for y in ys if {_DOMAIN_SRC[con.y_domain]})\n')
    a, b = con.a, con.b
    return ('def back(n, ms):\n'
            f'    # the square root alone is not enough: y = (m - ({b})) / ({2 * a}) must be an integer\n'
            f'    ys = {{(m - ({b})) // ({2 * a}) for m in set(ms) | {{-m for m in ms}}\n'
            f'          if (m - ({b})) % ({2 * a}) == 0}}\n'
            f'    return sorted(y for y in ys if {_DOMAIN_SRC[con.y_domain]})\n')


def _reduced_source(plan) -> str | None:
    """Source of `reduced(N)`: {n: [m >= 0 ...]} for the reduced power constraint."""
    G, d = plan.reduced.F, plan.reduced.d
    g_src = ' + '.join(f'({c}) * n ** {i}' for i, c in enumerate(G) if c) or '0'
    absr = 'abs(r)' if d % 2 == 0 else 'r'
    witness = (f'def witness(n):\n    v = {g_src}\n    r = iroot(v, {d})\n'
               f'    return None if r is None else {absr}\n')
    if plan._finite_list is not None:
        lit = {n: sorted({abs(m) if d % 2 == 0 else m for m in ms})
               for n, ms in plan._finite_list.items()}
        return ('# complete finite list (' + plan.method + ')\n'
                f'HITS = {lit!r}\n\ndef reduced(N):\n'
                '    return {n: ms for n, ms in HITS.items() if n <= N}\n')
    method = plan.method
    if method.startswith('identity'):
        return witness + ('\ndef reduced(N):\n    # every n is a hit\n'
                          '    return {n: [witness(n)] for n in range(1, N + 1)}\n')
    if method == 'radical parametrization':
        from .atlas import classify
        det = classify(G, d).details
        z0, t, u, v = det['z0'], det['t'], det['u'], det['v']
        return witness + (
            '\ndef reduced(N):\n'
            f'    # n = (s * {z0} * w^{t} + {u}) / {v}, w in the admissible classes mod {v}\n'
            '    ns = set()\n'
            f'    for rho in {det["good_residues_mod_v"]!r}:\n'
            f'        w = rho if rho >= 1 else {v}\n'
            f'        while {z0} * w ** {t} + ({u}) <= {v} * N:\n'
            f'            num = {z0} * w ** {t} + ({u})\n'
            f'            if num >= {v}:\n'
            f'                ns.add(num // {v})\n'
            f'            w += {v}\n'
            + (f'    w = 1\n'
               f'    while ({u}) - {z0} * w ** {t} >= {v}:\n'
               f'        num = ({u}) - {z0} * w ** {t}\n'
               f'        if num % {v} == 0 and num // {v} <= N:\n'
               f'            ns.add(num // {v})\n'
               f'        w += 1\n' if -1 in det['signs'] else '')
            + f'    ns |= {{n for n in {sorted(_zeros(G))!r} if n <= N}}\n'
            '    return {n: [witness(n)] for n in sorted(ns) if witness(n) is not None}\n')
    if method == 'Pell orbits':
        branches = plan.data['branches']
        bounded = plan.data['bounded_branches']
        lines = [witness, '\ndef reduced(N):', '    ns = set()']
        for br in branches:
            A, B, C = br['quadratic']
            D = br['D']
            x1, y1 = br['unit']
            lines += [f'    # {A} n^2 + ({B}) n + ({C}) = m^2  <=>  X^2 - {D} m^2 = {br["Delta"]},'
                      f' X = {2 * A} n + ({B})',
                      f'    for n in range(1, min(N, {br["small_n_checked_directly"]}) + 1):',
                      f'        v = {A} * n * n + ({B}) * n + ({C})',
                      '        if v >= 0 and isqrt(v) ** 2 == v:',
                      '            ns.add(n)',
                      f'    for X, Y in {[tuple(s) for s in br["seeds"]]!r}:',
                      '        while True:   # to the first orbit element with X > 0, Y >= 0',
                      f'            pX, pY = {x1} * X - {D * y1} * Y, {x1} * Y - {y1} * X',
                      '            if pX > 0 and pY >= 0:',
                      '                X, Y = pX, pY',
                      '            else:',
                      '                break',
                      f'        while X <= {2 * A} * N + ({B}):',
                      f'            if X > 0 and Y >= 0 and (X - ({B})) % {2 * A} == 0 and X - ({B}) >= {2 * A}:',
                      f'                ns.add((X - ({B})) // {2 * A})',
                      f'            X, Y = {x1} * X + {D * y1} * Y, {y1} * X + {x1} * Y   # times the unit']
        for (A, B, C) in bounded:
            from .compiler import bounded_branch_hits
            fixed = bounded_branch_hits(A, B, C)
            lines += [f'    ns |= {{n for n in {fixed!r} if n <= N}}   # bounded branch {A}, {B}, {C}']
        lines += [f'    ns |= {{n for n in {sorted(_zeros(G))!r} if n <= N}}',
                  '    return {n: [witness(n)] for n in sorted(ns) if n <= N}\n']
        return '\n'.join(lines)
    return None


def _zeros(G):
    from .atlas import _positive_zeros
    return _positive_zeros(G)


@dataclass
class Specialization:
    program: LoopProgram
    plan: object
    source: str | None
    original: str

    def run_original(self, N):
        return _exec(self.original)(N)

    def run_specialized(self, N):
        if self.source is None:
            raise ValueError(f'no specialized program ({self.plan.status})')
        return _exec(self.source)(N)

    def explain(self) -> dict:
        return {'program': {'expr': self.program.expr, 'test': list(self.program.test)},
                'plan': self.plan.explain(), 'specialized': self.source is not None}


def _exec(src: str):
    env: dict = {}
    exec(compile(src, '<generated>', 'exec'), env)
    return env['run']


def specialize(prog: LoopProgram) -> Specialization:
    plan = compile_constraint(prog.constraint())
    orig = original_source(prog)
    if plan.status == NOT_ENUMERATED or not plan.exact_to_any_N:
        return Specialization(prog, plan, None, orig)
    red = _reduced_source(plan)
    if red is None:
        return Specialization(prog, plan, None, orig)
    head = (f'"""Specialized from: {plan.original.describe()}\n'
            f'status: {plan.status}; method: {plan.method}\n'
            'justification:\n' + ''.join(f'  {j}\n' for j in plan.justification) +
            'The Python below is generated; it is not itself formally verified."""\n')
    if plan.data.get('specialized_test'):
        head += f'# membership test for the reduced constraint: {plan.data["specialized_test"]}\n'
    src = (head + _HELPERS + '\n' + red + '\n' + _back_source(plan) +
           '\n\ndef run(N):\n    out = []\n    for n, ms in sorted(reduced(N).items()):\n'
           '        ws = back(n, ms)\n        if ws:\n            out.append((n, ws))\n'
           '    return out\n')
    return Specialization(prog, plan, src, orig)
