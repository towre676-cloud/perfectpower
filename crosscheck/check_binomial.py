"""Plain-Python gate tying receipts/binomial_curves.json to the Lean hypotheses (no Sage needed).

Run by `make receipts`.  It checks that
  1. each curve in the receipt has a proved rank and a saturated basis;
  2. every receipt point lies on its curve (exact integers), and the receipt's x-list is the
     x-projection of its point list;
  3. the x-list is *exactly* the disjunction in the Lean hypothesis (`IntegralPointsCubePlusOne`,
     `IntegralPointsCongruent6` in PerfectPower/Binomial.lean), parsed from the Lean source;
  4. the points proved valid in `binomial_curve_points_valid` are the receipt's points with y >= 0;
  5. an independent scan over |X| <= 10^6 finds no integral point outside the receipt;
  6. pulling the points back through the Lean reductions gives exactly the hit lists stated in
     `choose_two_cube_hits` and `choose_three_square_hits`.
Completeness beyond the scan window is still Sage's claim (rank, saturation, elliptic-logarithm
sieving), not Lean's and not this script's.  Writes receipts/binomial_gate.json.
"""
import json
import re
import sys
from math import comb, isqrt
from pathlib import Path

root = Path(__file__).resolve().parents[1]
SCAN = 10 ** 6
CURVES = {  # receipt key -> (a4, a6, Lean hypothesis name)
    'Y^2 = X^3 + 1': (0, 1, 'IntegralPointsCubePlusOne'),
    'Y^2 = X^3 - 36X': (-36, 0, 'IntegralPointsCongruent6'),
}


def lean_hypothesis_xs(src, name):
    body = src.split(f'def {name} : Prop :=', 1)[1].split('\n\n', 1)[0]
    rhs = body.split('→', 1)[1]
    return sorted(int(v) for v in re.findall(r'X = (-?\d+)', rhs))


def lean_valid_lists(src):
    body = src.split('theorem binomial_curve_points_valid', 1)[1].split(':= by', 1)[0]
    lists = re.findall(r'\[((?:\(-?\d+, -?\d+\)(?:, )?)+)\]', body)
    return [sorted((int(a), int(b)) for a, b in re.findall(r'\((-?\d+), (-?\d+)\)', L)) for L in lists]


def lean_hit_lists(src):
    out = []
    for thm in ('choose_two_cube_hits', 'choose_three_square_hits'):
        stmt = src.split(f'theorem {thm}', 1)[1].split(':= by', 1)[0]
        rhs = stmt.split('↔', 1)[1]
        out.append(sorted(int(v) for v in re.findall(r'n = (\d+)', rhs)))
    return out


def scan(a4, a6):
    xs = []
    for x in range(-SCAN, SCAN + 1):
        v = x ** 3 + a4 * x + a6
        if v >= 0 and isqrt(v) ** 2 == v:
            xs.append(x)
    return xs


def main():
    rec = json.loads((root / 'receipts' / 'binomial_curves.json').read_text())
    src = (root / 'PerfectPower' / 'Binomial.lean').read_text()
    valid = lean_valid_lists(src)
    assert len(valid) == 2, 'could not parse binomial_curve_points_valid'
    report = {}
    for i, (key, (a4, a6, hyp)) in enumerate(CURVES.items()):
        c = rec[key]
        assert c['a_invariants'] == [0, 0, 0, a4, a6], key
        assert c['rank_method'].startswith('mwrank') and c['saturation_index'] == 1, key
        pts = sorted(tuple(p) for p in c['integral_points'])
        for x, y in pts:
            assert y * y == x ** 3 + a4 * x + a6, (key, x, y)
        assert sorted({x for x, _ in pts}) == c['x_coordinates'], key
        # both signs of y are listed
        assert sorted((x, -y) for x, y in pts) == pts, key
        lean_xs = lean_hypothesis_xs(src, hyp)
        assert lean_xs == c['x_coordinates'], (key, lean_xs, c['x_coordinates'])
        assert valid[i] == sorted(p for p in pts if p[1] >= 0), (key, valid[i])
        sc = scan(a4, a6)
        assert set(sc) <= set(c['x_coordinates']), (key, sorted(set(sc) - set(c['x_coordinates'])))
        report[key] = {'lean_hypothesis': hyp, 'x_coordinates': lean_xs, 'rank': c['rank'],
                       'saturation_index': c['saturation_index'],
                       'scan_abs_x_le': SCAN, 'scan_agrees': sorted(sc) == c['x_coordinates']}
    # pull back through the reductions
    xs2 = rec['Y^2 = X^3 + 1']['x_coordinates']
    hits2 = sorted({(Y + 1) // 2 for X in xs2 if X % 2 == 0 for Y in (isqrt(X ** 3 + 1),)
                    if Y % 2 == 1 and (Y + 1) // 2 >= 1})
    xs3 = rec['Y^2 = X^3 - 36X']['x_coordinates']
    hits3 = sorted({X // 6 + 1 for X in xs3 if X % 6 == 0 and X // 6 + 1 >= 1
                    and isqrt(X ** 3 - 36 * X) % 36 == 0})
    L2, L3 = lean_hit_lists(src)
    assert hits2 == L2, (hits2, L2)
    assert hits3 == L3, (hits3, L3)
    for n in L2:
        m = round(comb(n, 2) ** (1 / 3))
        assert any(k ** 3 == comb(n, 2) for k in (m - 1, m, m + 1)), n
    for n in L3:
        assert isqrt(comb(n, 3)) ** 2 == comb(n, 3), n
    report['hit_lists'] = {'C(n,2)=m^3': L2, 'C(n,3)=m^2': L3}
    report['boundary'] = ('completeness of each integral-point list beyond |X| <= 1e6 rests on Sage '
                          '(proved rank, saturated basis, elliptic-logarithm sieving); Lean takes it '
                          'as the named hypothesis')
    (root / 'receipts' / 'binomial_gate.json').write_text(json.dumps(report, indent=1) + '\n')
    print('binomial gate OK:', report['hit_lists'])


if __name__ == '__main__':
    sys.exit(main())
