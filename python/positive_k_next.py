"""Exact triage for the irreducible positive-k Thue equations.

This reads the existing receipt; it makes no completeness claim for the
bounded representation search recorded there.  Monic rows carry an exact
norm identity, which a future Lean source theorem can use directly.

Run: python3 python/positive_k_next.py
"""

import json
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def monic_order(form):
    """Return the depressed polynomial z³+pz+q and coordinate shift.

    If a=±1 and F=(a,B,C,d), theta is a root of
    T³+(B/a)T²+(C/a)T+d/a, z=theta+B/(3a), and
    F(u,v)=a*N((u+Bv/(3a))-vz).  The output is integer only because
    every middle coefficient in this branch is a multiple of three.
    """
    a, B, C, d = form
    if abs(a) != 1 or B % (3 * a):
        return None
    h = B // (3 * a)
    p = C // a - 3 * h * h
    q = d // a - (C // a) * h + 2 * h * h * h
    # Translation of the polynomial, checked coefficient by coefficient.
    assert 3 * h == B // a
    assert p + 3 * h * h == C // a
    assert q + p * h + h**3 == d // a
    return {'p': p, 'q': q, 'u_shift': h, 'norm': a}


def run():
    data = json.loads((ROOT / 'receipts/positive_k.json').read_text())
    rows = []
    by_curve = defaultdict(list)
    for curve in data['curves']:
        for cls in curve['class_detail']:
            if cls['local_obstruction'] is not None or cls['reducible'] is not None:
                continue
            form = cls['form']
            order = monic_order(form)
            if order:
                p, q = order['p'], order['q']
                assert -4 * p**3 - 27 * q**2 == cls['disc'] == -108 * curve['k']
            row = {'k': curve['k'], 'form': form, 'disc': cls['disc'],
                   'leading_abs': abs(form[0]), 'monic_order': order,
                   'known_representations': cls['representations'],
                   'known_points': cls['points']}
            rows.append(row)
            by_curve[curve['k']].append(row)

    leading = dict(sorted(Counter(r['leading_abs'] for r in rows).items()))
    assert len(rows) == data['summary']['open_irreducible'] == 104
    assert sum(r['monic_order'] is not None for r in rows) == 68
    assert len(by_curve) == 61
    # A small source with a known hit exercises unit generation and exhaustive
    # exclusion; the other class of k=2 is locally impossible modulo 9.
    pilot = by_curve[2]
    assert len(pilot) == 1 and pilot[0]['form'] == [-1, 0, -3, -2]
    assert pilot[0]['monic_order'] == {'p': 3, 'q': 2, 'u_shift': 0, 'norm': -1}
    out = {
        'source': 'receipts/positive_k.json',
        'scope': 'Irreducible, locally admissible positive-k classes only.',
        'caveat': 'The known representations were found in a bounded search; they are targets, not completeness certificates.',
        'summary': {'equations': len(rows), 'curves': len(by_curve),
                    'leading_abs': leading, 'monic_unit_equations': leading[1],
                    'equations_with_known_points': sum(bool(r['known_points']) for r in rows),
                    'curves_with_one_irreducible_equation': sum(len(v) == 1 for v in by_curve.values())},
        'pilot': {'k': 2, 'source': pilot[0],
                  'other_class': 'F=(0,-3,0,-2) has no solution modulo 9',
                  'exact_identity': 'F(u,v)=-N(u-v*z), z^3+3*z+2=0; F=1 implies N=-1',
                  'target_points': [[-1, -1], [-1, 1]]},
        'equations': rows,
    }
    target = ROOT / 'receipts/positive_k_next.json'
    target.write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out['summary'], sort_keys=True))
    print('pilot k=2: F=(-1,0,-3,-2), z^3+3z+2=0, norm=-1')


if __name__ == '__main__':
    run()
