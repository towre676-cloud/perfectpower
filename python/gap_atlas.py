"""The fixed-exponent gap atlas for squares and cubes (`receipts/gap_atlas.json`, `docs/GAP_ATLAS.md`).

For a gap `1 ≤ k ≤ 100`, the positive solutions of `a² − b³ = k` (a square just above a cube) are the
points `(x, y) = (b, a)` of `y² = x³ + k` with `x, y ≥ 1`, and those of `b³ − a² = k` (a cube just
above a square) are the points of `y² = x³ − k` with `x, y ≥ 1`.  Each direction inherits the
status of its curve, read from the axiom audit and the registries:
* `lean`: a Lean theorem with no added premise gives the complete point list
  (`ClassLists.K{k}.plus{k}`, `MordellMinus{D}`, the `MordellRegistry` curves, or
  `MordellDescent` for empty curves);
* `matveev`: a Lean theorem conditional on named instances of Matveev's bound;
* `census`: the Sage/PARI census (rank-proved generators, exact scan to |x| ≤ 10⁵) only.
This is Pillai's equation `a^p − b^q = k` at the fixed exponents `(p, q) = (2, 3)`.  A growing set of
fixed-exponent, fixed-gap results is not Pillai's conjecture, in which the exponents vary too.

Run: python3 python/gap_atlas.py
"""
from __future__ import annotations

import json
import math
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STD = {'propext', 'Classical.choice', 'Quot.sound'}


def audited():
    """Declarations audited on the standard axioms."""
    out = set()
    for line in (ROOT / 'audit' / 'axioms_report.txt').read_text().splitlines():
        m = re.match(r"'(\S+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)", line)
        if m and (m.group(2) is None or {a.strip() for a in m.group(2).split(',')} <= STD):
            out.add(m.group(1))
    return out


def census():
    """`k ↦ points` from the committed census JSONL (`both_signs=False` lists x; y = ±√(x³ + k))."""
    pts = {}
    for line in (ROOT / 'data' / 'mordell_census.jsonl').read_text().splitlines():
        r = json.loads(line)
        k = r['k']
        if abs(k) > 100:
            continue
        P = []
        for x in r['x_coordinates']:
            n = x ** 3 + k
            y = math.isqrt(n)
            assert y * y == n
            P += [(x, y), (x, -y)] if y else [(x, 0)]
        pts[k] = sorted(set(P))
    return pts


def statuses(aud):
    st = {}
    for name in aud:
        m = re.search(r'\.ClassLists\.K(\d+)\.plus(\d+)$', name)
        if m and m.group(1) == m.group(2):
            st[int(m.group(1))] = ('lean', name)
    reg = json.loads((ROOT / 'receipts' / 'mordell_registry.json').read_text())
    for c in reg['curves']:
        if c['D'] <= 100 and c['lean'] in aud:
            st[-c['D']] = ('lean', c['lean'])
    # hand-written curves (`MordellMinus{D}.lean`), complete lists of y² = x³ − D
    for D, thm in ((1, 'points_iff'), (2, 'points'), (4, 'points'), (5, 'no_points'), (6, 'no_points'),
                   (13, 'points')):
        name = f'PerfectPower.MordellMinus{D}.{thm}'
        if name in aud:
            st[-D] = ('lean', name)
    desc = json.loads((ROOT / 'receipts' / 'mordell_descent.json').read_text())
    for r in desc['rows']:
        if abs(r['k']) <= 100:
            st.setdefault(r['k'], ('lean', 'PerfectPower.Generated.MordellDescent (no integral point)'))
    # conditional on Matveev: the theorems make_counts.py reports apart
    for name in aud:
        m = re.search(r'\.Minus(\d+)\.minus(\d+)$', name) or re.search(r'\.Field756\.minus(\d+)$', name)
        if m:
            D = int(m.group(1))
            if D <= 100 and -D not in st:
                st[-D] = ('matveev', name)
    return st


def run():
    aud = audited()
    pts = census()
    st = statuses(aud)
    rows = []
    for k in range(1, 101):
        row = {'k': k}
        for key, curve in (('square_above_cube', k), ('cube_above_square', -k)):
            sols = sorted((y, x) for x, y in pts[curve] if x >= 1 and y >= 1)   # (a, b)
            s, thm = st.get(curve, ('census', None))
            row[key] = {'curve_k': curve, 'solutions': [list(t) for t in sols], 'status': s, 'theorem': thm,
                        'trivial_base': any(a == 1 or b == 1 for a, b in sols)}
        rows.append(row)
    tally = {}
    for r in rows:
        for key in ('square_above_cube', 'cube_above_square'):
            tally[r[key]['status']] = tally.get(r[key]['status'], 0) + 1
    return {'scope': "Pillai's equation at fixed exponents (2, 3): positive solutions of a^2 - b^3 = ±k, "
                     '1 <= k <= 100, with the status of the curve that settles each direction',
            'summary': {'gaps': 100, 'directions_by_status': dict(sorted(tally.items())),
                        'catalan_check': rows[0]['square_above_cube']['solutions']},
            'rows': rows}


def md(out):
    def cell(d):
        s = ', '.join(f'({a},{b})' for a, b in d['solutions']) or '—'
        return s, {'lean': 'Lean', 'matveev': 'Matveev', 'census': 'census'}[d['status']]
    lines = ['# The square–cube gap atlas', '',
             "Pillai's equation at fixed exponents: the positive solutions of $a^2-b^3=k$ (a square just above a",
             'cube) and of $b^3-a^2=k$ (a cube just above a square), for $1\\le k\\le100$, generated by',
             '`python/gap_atlas.py` (`receipts/gap_atlas.json`).', '',
             'Each direction is settled by the integral points of one Mordell curve, $y^2=x^3+k$ or $y^2=x^3-k$,',
             'and inherits that curve\'s status.',
             '- **Lean**: a Lean theorem with no added premise.',
             '- **Matveev**: a Lean theorem conditional on named instances of Matveev\'s bound.',
             '- **census**: Sage/PARI integral points with proved ranks only, not a Lean theorem.', '',
             'Pairs are $(a,b)$. The row $k=1$ contains Catalan\'s $3^2-2^3=1$. A collection of fixed-exponent,',
             "fixed-gap results like this one is not Pillai's conjecture, in which the exponents also vary.", '',
             f"Status counts over the 200 directions: {', '.join(f'{k} {v}' for k, v in out['summary']['directions_by_status'].items())}.", '',
             '| k | a² − b³ = k | status | b³ − a² = k | status |', '|---:|---|---|---|---|']
    for r in out['rows']:
        s1, t1 = cell(r['square_above_cube'])
        s2, t2 = cell(r['cube_above_square'])
        lines.append(f"| {r['k']} | {s1} | {t1} | {s2} | {t2} |")
    return '\n'.join(lines) + '\n'


if __name__ == '__main__':
    out = run()
    assert out['summary']['catalan_check'] == [[3, 2]]
    (ROOT / 'receipts' / 'gap_atlas.json').write_text(json.dumps(out, indent=1) + '\n')
    (ROOT / 'docs' / 'GAP_ATLAS.md').write_text(md(out))
    print('gap atlas:', out['summary']['directions_by_status'])
