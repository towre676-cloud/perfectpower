"""The open Thue branches as a transformation graph, and the curves it closes.

1. Every open branch of every OPEN_BRANCH curve (`receipts/mordell_branch.json`) becomes a node
   `F_{p,q}(a, b) = k^3` (`thue_graph.open_equations`).
2. Nodes are grouped into exact GL_2(Z) classes by a canonical form (`thue_graph.canonical`):
   each node carries a matrix T with F o T = (representative).  These edges are certificates,
   checked in Lean by evaluation.
3. For each class, a p-adic descent certificate is searched on the representative
   (`ThueLocal.descB`: split into the zero class and the root lines of F mod p, dividing out the
   p-content, down to leaves impossible modulo a small power of p).  An obstructed class becomes ONE obligation theorem, whatever
   the number of branches (of whatever curves) that transport to it.
4. A curve all of whose open branches transport to proved obligations gets a complete list:
   `DescentThue.complete_of_thue`.

The PARI solutions (`receipts/mordell_branch_thue.json`, external) are used only to label classes
("carries points", "Thue solutions but no integral readout", "no Thue solutions"); no certificate
depends on them.

Writes PerfectPower/Generated/MordellThue.lean and receipts/thue_graph.json.
"""
import csv
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower import thue_graph as G  # noqa: E402
from perfectpower.branch_descent import compile_curve  # noqa: E402
from perfectpower.descent import W1, W2  # noqa: E402

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]


def lift_obstruction(F, M, p, emax):
    """(e, level sizes) for the first empty level of the lifting tree mod p^e, else None.
    The same tree as `ThueLocal.lvl` (level 0 is {(0, 0)})."""
    level, sizes, m = [(0, 0)], [], 1
    for e in range(1, emax + 1):
        new = [(a + m * i, b + m * j) for a, b in level for i in range(p) for j in range(p)
               if (G.evalF(F, a + m * i, b + m * j) - M) % (m * p) == 0]
        level, m = new, m * p
        sizes.append(len(level))
        if not level:
            return e, sizes
        if len(level) > 400000:
            return None
    return None


def vp(n, p):
    v = 0
    while n % p == 0 and v < 60:
        n //= p
        v += 1
    return v


def line_mat(p, lam):
    return ((lam, p), (1, 0)) if lam is not None else ((1, 0), (0, p))


def descent(F, M, p, maxnodes=500):
    """A descent certificate (list of nodes, node 0 = (F, M)) with the semantics of
    `ThueLocal.descB`, or None.

    Exact repeated subproblems are interned: a node `(F, M)` reached along two paths is
    built and checked once, and both parents point at it (the checker needs only that a
    child's index exceed its parent's, so a DAG is valid).  The nodes are then renumbered
    in a topological order.  Only *identical* `(F, M)` are shared; GL_2(Z)-equivalent nodes
    are not, since that would need a transport step the checker does not have."""
    raw, memo = [], {}

    def build(F, M):
        key = (F, M)
        if key in memo:
            return memo[key]
        if len(raw) > maxnodes:
            raise ValueError('too large')
        idx = len(raw)
        raw.append(None)
        memo[key] = idx
        if M % p:
            r = lift_obstruction(F, M, p, 6)
            if not r:
                raise ValueError('leaf not locally impossible')
            raw[idx] = (F, M, ('leaf', r[0]))
            return idx
        zero = build(F, M // p ** 3) if M % p ** 3 == 0 else None
        lines = []
        roots = [l for l in range(p) if G.evalF(F, l, 1) % p == 0]
        if F[0] % p == 0:
            roots.append(None)
        for lam in roots:
            H = G.compose(F, line_mat(p, lam))
            s = min(min(vp(c, p) if c else 60 for c in H), vp(M, p))
            assert s >= 1
            H2 = tuple(c // p ** s for c in H)
            j = build(H2, M // p ** s)
            lines.append((lam, s, j))
        raw[idx] = (F, M, ('split', zero, lines))
        return idx
    try:
        build(tuple(F), M)
    except ValueError:
        return None
    # topological renumbering: parents before children (reverse postorder from the root)
    order, seen = [], set()

    def visit(i):
        if i in seen:
            return
        seen.add(i)
        k = raw[i][2]
        if k[0] == 'split':
            for j in ([k[1]] if k[1] is not None else []) + [l[2] for l in k[2]]:
                visit(j)
        order.append(i)
    visit(0)
    order.reverse()
    new = {old: n for n, old in enumerate(order)}
    nodes = []
    for old in order:
        F, M, k = raw[old]
        if k[0] == 'split':
            k = ('split', None if k[1] is None else new[k[1]], [(l, s, new[j]) for l, s, j in k[2]])
        nodes.append((F, M, k))
    return nodes


def tree_size(nodes, i=0):
    """Number of nodes of the certificate unfolded as a tree (no interning)."""
    k = nodes[i][2]
    if k[0] == 'leaf':
        return 1
    kids = ([k[1]] if k[1] is not None else []) + [l[2] for l in k[2]]
    return 1 + sum(tree_size(nodes, j) for j in kids)


def descent_multi(F, M, maxnodes=400, qs=(2, 3, 5, 7, 11, 13), work_cap=150000):
    """A multi-prime descent certificate (`ThueLocal.descM`): nodes `(p, F, M, kind)`, each checked
    at its own prime, or None.  A node becomes a leaf when a small lifting tree at some prime `q`
    closes it (kernel work at most `work_cap`); otherwise it splits at the smallest prime of `M`.
    Exact repeated subproblems are interned; nodes are renumbered topologically."""
    raw, memo = [], {}

    def primes_of(n):
        n, out, q = abs(n), [], 2
        while q * q <= n:
            if n % q == 0:
                out.append(q)
                while n % q == 0:
                    n //= q
            q += 1
        return out + ([n] if n > 1 else [])

    def build(F, M):
        key = (F, M)
        if key in memo:
            return memo[key]
        if len(raw) > maxnodes:
            raise ValueError('too large')
        idx = len(raw)
        raw.append(None)
        memo[key] = idx
        for q in qs:
            r = lift_obstruction(F, M, q, 5 if q <= 7 else 3)
            if r and q * q * (1 + sum(r[1][:-1])) <= work_cap:
                raw[idx] = (q, F, M, ('leaf', r[0]))
                return idx
        for p in primes_of(M):            # try each split prime, rolling back a failed attempt
            mark, saved = len(raw), dict(memo)
            try:
                zero = build(F, M // p ** 3) if M % p ** 3 == 0 else None
                lines = []
                roots = [l for l in range(p) if G.evalF(F, l, 1) % p == 0]
                if F[0] % p == 0:
                    roots.append(None)
                for lam in roots:
                    H = G.compose(F, line_mat(p, lam))
                    s = min(min(vp(c, p) if c else 60 for c in H), vp(M, p))
                    lines.append((lam, s, build(tuple(c // p ** s for c in H), M // p ** s)))
                raw[idx] = (p, F, M, ('split', zero, lines))
                return idx
            except ValueError as ex:
                if str(ex) == 'too large':
                    raise
                del raw[mark:]
                memo.clear()
                memo.update(saved)
        raise ValueError('no split prime closes this node')
    try:
        build(tuple(F), M)
    except ValueError:
        return None
    order, seen = [], set()

    def visit(i):
        if i in seen:
            return
        seen.add(i)
        k = raw[i][3]
        if k[0] == 'split':
            for j in ([k[1]] if k[1] is not None else []) + [l[2] for l in k[2]]:
                visit(j)
        order.append(i)
    visit(0)
    order.reverse()
    new = {o: n for n, o in enumerate(order)}
    out = []
    for o in order:
        p, F, M, k = raw[o]
        if k[0] == 'split':
            k = ('split', None if k[1] is None else new[k[1]], [(l, s, new[j]) for l, s, j in k[2]])
        out.append((p, F, M, k))
    return out


def kind_lean(k):
    if k[0] == 'leaf':
        return f'(Kind.leaf {k[1]})'
    z = 'none' if k[1] is None else f'(some {k[1]})'
    ls = ', '.join(f"({'none' if l is None else f'(some {l})'}, {s}, {j})" for l, s, j in k[2])
    return f'(Kind.split {z} [{ls}])'


def _i(v):
    return f'({v})' if v < 0 else str(v)


def form_lean(F):
    return '(' + ', '.join(_i(c) for c in F) + ')'


def mat_lean(T):
    return f'(({_i(T[0][0])}, {_i(T[0][1])}), ({_i(T[1][0])}, {_i(T[1][1])}))'


HEADER = '''import PerfectPower.DescentThue

/-!
# Curves closed by transported Thue obligations (generated by `python/make_lean_thue_branch.py`)

Each `obl_*` is one GL₂(ℤ)-class of open branch equations `G(u, v) = M`, proved to have no
integral solution by a p-adic lifting tree (`ThueLocal.no_solution_of_lvl`) that the kernel
recomputes.  Each curve theorem is `DescentThue.complete_of_thue`: its field-cube and local
branches as in `DescentBranch`, and every other branch carried to an obligation by a unimodular
matrix checked by evaluation.
-/

namespace PerfectPower.Generated.MordellThue

open PerfectPower ThueLocal

'''


def main():
    ledger = json.loads((ROOT / 'receipts' / 'mordell_branch.json').read_text())
    thue_path = ROOT / 'receipts' / 'mordell_branch_thue.json'
    pari = {}
    if thue_path.exists():
        for cv in json.loads(thue_path.read_text())['curves']:
            for b in cv['branches']:
                pari[(b['D'], b['k'], b['p'], b['q'])] = b.get('solutions')
    nodes = G.open_equations(ledger)
    groups = G.classes(nodes)
    classes = []
    for idx, ((rep, M), members) in enumerate(sorted(groups.items(), key=lambda kv: (kv[1][0]['D'], kv[0]))):
        n0 = members[0]
        sols = pari.get((n0['D'], n0['k'], n0['p'], n0['q']))
        integral = None
        if sols is not None:
            integral = [(a, b) for a, b in sols
                        if (n0['p'] * W1(n0['D'], a, b) + n0['D'] * n0['q'] * W2(n0['D'], a, b)) % n0['M'] == 0]
        label = ('unknown' if sols is None else 'no_thue_solutions' if not sols else
                 'thue_solutions_without_points' if not integral else 'carries_points')
        cls = {'id': idx, 'representative': list(rep), 'M': M, 'size': len(members),
               'curves': sorted({m['D'] for m in members}), 'discriminant': G.disc(rep),
               'pari_label': label,
               'members': [{'D': m['D'], 'k': m['k'], 'p': m['p'], 'q': m['q'], 'F': list(m['F']),
                            'T': [list(m['T'][0]), list(m['T'][1])]} for m in members]}
        if label != 'carries_points':
            # only primes dividing 6 * disc(F) * M * c0 can obstruct (elsewhere F is smooth mod p
            # and solutions lift by Hensel); the certificate does not rely on this, it only
            # saves search time
            bad = 6 * G.disc(rep) * M * (rep[0] or 1)
            for p in [q for q in PRIMES if bad % q == 0]:
                cert = descent(rep, M, p)
                if cert is not None:
                    leaf_work = sum(p * p * (1 + sum(lift_obstruction(F, MM, p, 6)[1][:-1]))
                                    for F, MM, k in cert if k[0] == 'leaf')
                    lift = lift_obstruction(rep, M, p, 12 if p <= 3 else 6)
                    lift_work = None if not lift else sum(x * p * p for x in [1] + lift[1][:-1])
                    cls.update({'descent': {'p': p, 'nodes': len(cert), 'tree_nodes': tree_size(cert),
                                            'leaf_work': leaf_work,
                                            'lifting_tree_work_for_comparison': lift_work,
                                            'lifting_tree_depth': None if not lift else lift[0],
                                            'certificate': [[list(F), MM, list(k[:2]) if k[0] == 'leaf' else
                                                             [k[0], k[1], [list(x) for x in k[2]]]]
                                                            for F, MM, k in cert]},
                                'lean': f'PerfectPower.Generated.MordellThue.obl_{idx}', '_cert': cert})
                    break
            if 'descent' not in cls:
                mc = descent_multi(rep, M)
                if mc is not None:
                    leaf_work = sum(q * q * (1 + sum(lift_obstruction(F, MM, q, 5 if q <= 7 else 3)[1][:-1]))
                                    for q, F, MM, k in mc if k[0] == 'leaf')
                    cls.update({'descent': {'p': 'multi', 'primes': sorted({q for q, *_ in mc}), 'nodes': len(mc),
                                            'tree_nodes': None, 'leaf_work': leaf_work,
                                            'lifting_tree_work_for_comparison': None, 'lifting_tree_depth': None,
                                            'certificate': [[q, list(F), MM, list(k[:2]) if k[0] == 'leaf' else
                                                             [k[0], k[1], [list(x) for x in k[2]]]]
                                                            for q, F, MM, k in mc]},
                                'lean': f'PerfectPower.Generated.MordellThue.obl_{idx}', '_cert': mc})
        classes.append(cls)
    by_node = {}
    for c in classes:
        for m in c['members']:
            by_node[(m['D'], m['k'], m['p'], m['q'])] = c
    # curves: closed iff every open branch lies in an obstructed class
    curves, blocks, used = [], [], set()
    open_D = sorted({n['D'] for n in nodes})
    for D in open_D:
        c = compile_curve(D)
        cls_here = [by_node[(D, e['k'], e['p'], e['q'])] for e in c['open']]
        closed = all('descent' in x for x in cls_here)
        rec = {'D': D, 'open_branches': len(c['open']), 'classes': sorted({x['id'] for x in cls_here}),
               'status': 'COMPLETE' if closed else 'OPEN_THUE', 'points': [list(p) for p in c['points']]}
        if closed:
            used |= set(rec['classes'])
            rec['lean'] = f'PerfectPower.Generated.MordellThue.minus{D}'
            blocks.append((D, c, cls_here))
        curves.append(rec)
    # emit
    out = [HEADER]
    for c in classes:
        if 'descent' not in c:
            continue
        ob = c['descent']
        cert = c.pop('_cert')
        if ob['p'] == 'multi':
            rest = ', '.join(f"({q}, {form_lean(F)}, {M}, {kind_lean(k)})" for q, F, M, k in cert[1:])
            out.append(f"/-- Obligation {c['id']}: `G(u, v) = {c['M']}` has no integral solution: a multi-prime "
                       f"descent certificate (primes {ob['primes']}, {len(cert)} node(s); no single-prime "
                       f"certificate was found). {c['size']} branch equations of `y^2 = x^3 - D`, "
                       f"D ∈ {c['curves']}, transport to it. -/\n"
                       f"theorem obl_{c['id']} : ∀ u v : ℤ, evalF {form_lean(c['representative'])} u v ≠ {c['M']} :=\n"
                       f"  no_solution_of_descM {cert[0][0]} _ _ {kind_lean(cert[0][3])}\n    [{rest}]\n    (by decide +kernel)\n")
            continue
        rest = ', '.join(f"({form_lean(F)}, {M}, {kind_lean(k)})" for F, M, k in cert[1:])
        out.append(f"/-- Obligation {c['id']}: `G(u, v) = {c['M']}` has no integral solution: a {ob['p']}-adic "
                   f"descent certificate with {len(cert)} node(s) (the plain lifting tree would need "
                   f"{ob['lifting_tree_work_for_comparison']} lifts to depth {ob['lifting_tree_depth']}). {c['size']} branch equations of "
                   f"`y^2 = x^3 - D`, D ∈ {c['curves']}, transport to it. -/\n"
                   f"theorem obl_{c['id']} : ∀ u v : ℤ, evalF {form_lean(c['representative'])} u v ≠ {c['M']} :=\n"
                   f"  no_solution_of_desc {ob['p']} _ _ {kind_lean(cert[0][2])}\n    [{rest}]\n    (by decide +kernel)\n")
    for D, c, cls_here in blocks:
        from perfectpower.branch_descent import lean_args
        a = lean_args(c)
        cubes = '[' + ', '.join('(' + ', '.join(_i(v) for v in t) + ')' for t in a['cubes']) + ']'
        mods = '[' + ', '.join('(' + ', '.join(_i(v) for v in t) + ')' for t in a['mods']) + ']'
        ys = '[' + ', '.join(_i(v) for v in a['Ys']) + ']'
        pts = '[' + ', '.join(f'({_i(x)}, {_i(y)})' for x, y in a['P']) + ']'
        thues = []
        for e in c['open']:
            m = next(m for m in by_node[(D, e['k'], e['p'], e['q'])]['members']
                     if (m['D'], m['k'], m['p'], m['q']) == (D, e['k'], e['p'], e['q']))
            thues.append(f"({_i(e['k'])}, {_i(e['p'])}, {_i(e['q'])}, {mat_lean(m['T'])})")
        ids = sorted({x['id'] for x in cls_here})
        closed_list = '[' + ', '.join(f"({form_lean(classes[i]['representative'])}, {classes[i]['M']})" for i in ids) + ']'
        pat = ' | '.join(['rfl'] * len(ids))
        exacts = ', '.join(f'obl_{i}' for i in ids)
        out.append(
            f"set_option maxHeartbeats 0 in\n"
            f"/-- **The complete list of integral points of `y^2 = x^3 - {D}`** ({len(a['P'])} point(s)): "
            f"{len(a['cubes'])} field-cube and {len(a['mods'])} local branches, and {len(thues)} Thue "
            f"branches transported to obligations {ids}. -/\n"
            f"theorem minus{D} (x y : ℤ) : y ^ 2 = x ^ 3 - {D} ↔ (x, y) ∈ ({pts} : List (ℤ × ℤ)) :=\n"
            f"  DescentThue.complete_of_thue {D} (by norm_num) {c['r']} {c['t']} (by norm_num) (by norm_num)"
            f" {c['K']} {c['Q']}\n    (by norm_num) (by norm_num)\n"
            f"    {cubes}\n    {mods}\n    [{', '.join(thues)}]\n    {closed_list}\n"
            f"    (by intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc\n"
            + (f"        rcases hc with rfl; exact {exacts})\n" if len(ids) == 1 else
               f"        rcases hc with {pat} <;> first {' '.join('| exact ' + x for x in exacts.split(', '))})\n")
            + f"    {ys}\n    {pts}\n    (by decide +kernel) (by decide +kernel) x y\n")
    out.append('end PerfectPower.Generated.MordellThue\n')
    (ROOT / 'PerfectPower' / 'Generated' / 'MordellThue.lean').write_text('\n'.join(out))
    census = {}
    with open(ROOT / 'data' / 'mordell_census.csv') as f:
        for row in csv.DictReader(f):
            census[int(row['k'])] = sorted(int(v) for v in row['x_coordinates'].split())
    for r in curves:
        if r['status'] == 'COMPLETE':
            r['agrees_with_sage'] = sorted({x for x, _ in r['points']}) == census.get(-r['D'])
            if not r['agrees_with_sage']:
                raise SystemExit(f"D = {r['D']}: certified list disagrees with the Sage census")
    obstructed = [c for c in classes if 'descent' in c]
    summary = {
        'nodes': len(nodes), 'classes': len(classes),
        'class_sizes': sorted({c['size'] for c in classes}),
        'classes_shared_across_curves': sum(len(c['curves']) > 1 for c in classes),
        'pari_labels': {lab: sum(c['pari_label'] == lab for c in classes)
                        for lab in sorted({c['pari_label'] for c in classes})},
        'obstructed_classes': len(obstructed),
        'obligations_emitted': len(obstructed),
        'curves_closed': [r['D'] for r in curves if r['status'] == 'COMPLETE'],
        'descent_nodes_total': sum(c['descent']['nodes'] for c in obstructed),
        'descent_nodes_without_interning': sum(c['descent']['tree_nodes'] or c['descent']['nodes'] for c in obstructed),
        'multi_prime_obligations': [c['id'] for c in obstructed if c['descent']['p'] == 'multi'],
        'descent_leaf_work_total': sum(c['descent']['leaf_work'] for c in obstructed),
        'lifting_tree_work_one_per_class': sum(c['descent']['lifting_tree_work_for_comparison'] or 0 for c in obstructed),
        'lifting_tree_work_one_per_branch': sum((c['descent']['lifting_tree_work_for_comparison'] or 0) * c['size']
                                                for c in obstructed),
    }
    out_json = {'summary': summary, 'classes': classes, 'curves': curves,
                'note': 'GL_2(Z) classes are computed by a reduced-Hessian normal form; transport inside '
                        'a class is certified, inequivalence between classes is not formalized. '
                        'PARI labels are external and used only for reporting'}
    (ROOT / 'receipts' / 'thue_graph.json').write_text(json.dumps(out_json, indent=1) + '\n')
    print(json.dumps(summary, indent=1))


if __name__ == '__main__':
    main()
