"""Solution-preserving descent on the non-obstructed Thue classes: a measurement, not a certificate.

`ThueLocal.descB` splits F(a, b) = M at a prime p | M into the zero class (F, M/p^3) and the root
lines of F mod p, each a new form with right side M/p^s.  On an obstructed class every leaf is
locally impossible.  On a class with solutions some leaf must survive: descent is a local method,
and a global solution lies in some p-adic class at every step.

Here descent runs on every class **not** closed by `make_lean_thue_branch.py`, over all primes of
M, pruning children that are locally impossible (the same check as `Kind.leaf`), until the right
side is +-1.  Each node's form is F o T for an integer matrix T of determinant +-p^s, so the
solutions of the parent are exactly the images T(u, v) of the child solutions: solutions are
preserved, not lost.  The surviving leaves are unit equations G(u, v) = +-1, canonicalized by
GL_2(Z) (`thue_graph.canonical`; (G, -1) ~ (G, 1) by -I).

The question measured is the one a solution-preserving certificate would need answered.  After
descent, how many *distinct* unit equations remain, and are they shared across classes and
curves?  Closing them still needs a global input: a bound or a solved leaf.  Nothing is promoted.

Run: python3 python/descent_residual.py   (a few seconds)
Writes receipts/descent_residual.json.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))
sys.path.insert(0, str(ROOT))

from perfectpower import thue_graph as G  # noqa: E402
from python.make_lean_thue_branch import lift_obstruction, line_mat, vp  # noqa: E402


def primes_of(n):
    n, out, p = abs(n), [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def small_solutions(F, M, B=60):
    return [(u, v) for u in range(-B, B + 1) for v in range(-B, B + 1) if G.evalF(F, u, v) == M]


def residual(F, M, cap=4000):
    """Leaves (G, +-1) of the full descent of F = M, with locally impossible children pruned."""
    leaves, pruned, count = [], 0, 0
    stack = [(tuple(F), M)]
    while stack:
        F, M = stack.pop()
        count += 1
        if count > cap:
            raise ValueError('descent too large')
        if abs(M) == 1:
            leaves.append((F, M))
            continue
        p = primes_of(M)[0]
        kids = []
        if M % p ** 3 == 0:
            kids.append((F, M // p ** 3))
        roots = [l for l in range(p) if G.evalF(F, l, 1) % p == 0]
        if F[0] % p == 0:
            roots.append(None)
        for lam in roots:
            H = G.compose(F, line_mat(p, lam))
            s = min(min(vp(c, p) if c else 60 for c in H), vp(M, p))
            kids.append((tuple(c // p ** s for c in H), M // p ** s))
        for K, N in kids:
            dead = any(lift_obstruction(K, N, q, 3) for q in (2, 3, 5, 7) if N % q)
            if dead:
                pruned += 1
            else:
                stack.append((K, N))
    return leaves, pruned, count


def main():
    graph = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    closed = {c for curve in graph['curves'] if curve['status'] == 'COMPLETE' for c in curve['classes']}
    rows, canon = [], {}
    for c in graph['classes']:
        if c['id'] in closed:
            continue
        try:
            leaves, pruned, count = residual(c['representative'], c['M'])
        except ValueError:
            rows.append({'class': c['id'], 'curves': c['curves'], 'status': 'descent too large'})
            continue
        keys = []
        for F, M in leaves:
            H = F if M == 1 else tuple(-x for x in F)
            key = G.canonical(H)[0]
            canon.setdefault(key, set()).add(c['id'])
            keys.append(list(key))
        rows.append({'class': c['id'], 'curves': c['curves'], 'M': c['M'], 'label': c['pari_label'],
                     'nodes': count, 'pruned': pruned, 'unit_leaves': len(leaves),
                     'distinct_unit_leaves': len({tuple(k) for k in keys})})
    shared = {k: v for k, v in canon.items() if len(v) > 1}
    leaf_rows = [{'form': list(k), 'classes': sorted(v),
                  'small_solutions': len(small_solutions(k, 1))} for k, v in sorted(canon.items())]
    out = {'label': 'MEASUREMENT: solution-preserving descent to unit equations; no certificate, nothing promoted',
           'classes_open': len(rows),
           'classes_too_large': sum(r.get('status') == 'descent too large' for r in rows),
           'unit_leaves_total': sum(r.get('unit_leaves', 0) for r in rows),
           'distinct_unit_equations': len(canon),
           'unit_equations_shared_by_several_classes': len(shared),
           'unit_equations_without_small_solutions': sum(r['small_solutions'] == 0 for r in leaf_rows),
           'classes': rows, 'unit_equations': leaf_rows}
    (ROOT / 'receipts' / 'descent_residual.json').write_text(json.dumps(out, indent=1) + '\n')
    print({k: v for k, v in out.items() if not isinstance(v, list)})


if __name__ == '__main__':
    main()
