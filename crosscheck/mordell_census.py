"""Mordell census: all integral points of y^2 = x^3 + k for 0 < |k| <= K (Hall's conjecture frontier).

Run with a Sage / passagemath Python from the repository root:

    /opt/sagevenv/bin/python crosscheck/mordell_census.py 10000 [workers]

Engine: EllipticCurve([0,0,0,0,k]).integral_points(mw_base=gens), where gens are Mordell-Weil
generators from mwrank (saturated) and integral_points performs elliptic-logarithm sieving
(Stroeker-Tzanakis / Gebel-Petho-Zimmer).  Per-row labels:
  certified_by_independent_computation  rank proved (mwrank, or analytically when rank <= 1)
  conditional_on_unproven_rank          generators from proof=False (rank not proved)
  scan_only                             engine failure; only the small-x scan is recorded
In every case the listed points are re-verified in exact integer arithmetic and cross-checked
against an independent scan |x| <= SCAN.  Lean plays no part in completeness.

Output: data/mordell_census.csv (one row per k) and receipts/mordell_census_summary.json.
"""
import csv
import json
import sys
import time
from math import isqrt
from multiprocessing import Pool
from pathlib import Path

SCAN = 10 ** 5
LABEL = {'certified_by_independent_computation': 'INDEPENDENT_COMPUTATION',
         'conditional_on_unproven_rank': 'CONDITIONAL_ON_UNPROVEN_RANK',
         'scan_only': 'SCAN_EVIDENCE_ONLY'}


def _setup():
    global EllipticCurve
    from sage.all__sagemath_schemes import EllipticCurve as _E
    import sage.all__sagemath_eclib  # noqa: F401
    import sage.all__sagemath_symbolics  # noqa: F401
    from sage.schemes.elliptic_curves.ell_rational_field import EllipticCurve_rational_field

    def exact_interval(self, xmin, xmax):
        # PARI ellratpoints segfaults on some curves in passagemath 10.8.12; exact scan instead.
        a4, a6 = int(self.a4()), int(self.a6())
        xmin, xmax = int(xmin), int(xmax)
        if xmax - xmin > 10 ** 7:
            raise RuntimeError('interval too long for exact scan')
        return {x for x in range(xmin, xmax + 1)
                if x ** 3 + a4 * x + a6 >= 0 and isqrt(x ** 3 + a4 * x + a6) ** 2 == x ** 3 + a4 * x + a6}
    EllipticCurve_rational_field.integral_x_coords_in_interval = exact_interval
    EllipticCurve = _E


def scan_points(k):
    """Independent check: all x with |x| <= SCAN and x^3 + k a square (x >= -cbrt(k))."""
    out = []
    for x in range(-SCAN, SCAN + 1):
        v = x ** 3 + k
        if v >= 0:
            r = isqrt(v)
            if r * r == v:
                out.append(x)
    return out


def one(k):
    E = EllipticCurve([0, 0, 0, 0, k])
    row = {'k': k}
    status = 'certified_by_independent_computation'
    try:
        try:
            rank = int(E.rank(proof=True))
            gens = E.gens(proof=True)
            method = 'mwrank'
        except RuntimeError:
            try:
                rank = int(E.rank(only_use_mwrank=False, proof=True))
                gens = E.gens(proof=True) if rank else []
                method = 'analytic'
            except RuntimeError:
                rank = int(E.rank(proof=False))
                gens = E.gens(proof=False)
                method = 'unproven'
                status = 'conditional_on_unproven_rank'
        pts = E.integral_points(mw_base=gens, both_signs=False)
        xs = sorted({int(P[0]) for P in pts})
    except BaseException as exc:          # cysignals SignalError derives from BaseException
        if isinstance(exc, KeyboardInterrupt):
            raise
        return {'k': k, 'status': 'scan_only', 'error': f'{type(exc).__name__}: {exc}'[:200],
                'xs': scan_points(k)}
    for x in xs:                                   # exact re-verification
        v = x ** 3 + k
        assert v >= 0 and isqrt(v) ** 2 == v, (k, x)
    small = [x for x in xs if abs(x) <= SCAN]
    row.update(status=status, rank=rank, rank_method=method, xs=xs,
               scan_agrees=small == scan_points(k),
               torsion=int(E.torsion_order()), disc=int(E.discriminant()))
    return row


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    ks = [k for k in range(-K, K + 1) if k != 0]
    t0 = time.time()
    with Pool(workers, initializer=_setup, maxtasksperchild=200) as pool:
        rows = sorted(pool.imap_unordered(one, ks, chunksize=8), key=lambda r: r['k'])
    import sage.version
    global ENGINE
    ENGINE = f'passagemath {sage.version.version} integral_points (mwrank)'
    root = Path(__file__).resolve().parents[1]
    (root / 'data').mkdir(exist_ok=True)
    with open(root / 'data' / 'mordell_census.csv', 'w', newline='') as fh:
        w = csv.writer(fh, lineterminator='\n')
        w.writerow(['k', 'rank', 'rank_method', 'torsion', 'n_points_up_to_sign', 'x_coordinates',
                    'max_x', 'max_hall_ratio', 'scan_agrees_up_to_1e5', 'certification', 'engine'])
        for r in rows:
            xs = r['xs']
            hall = max((isqrt(abs(x) * 10 ** 12) / 10 ** 6 / abs(r['k']) for x in xs if x > 0), default='')
            w.writerow([r['k'], r.get('rank', ''), r.get('rank_method', ''), r.get('torsion', ''),
                        len(xs), ' '.join(map(str, xs)), max(xs, default=''),
                        f'{hall:.6f}' if hall != '' else '', r.get('scan_agrees', ''), LABEL[r['status']],
                        ENGINE if r['status'] != 'scan_only' else 'stdlib scan |x| <= 1e5'])
    records = sorted(((isqrt(x * 10 ** 12) / 10 ** 6 / abs(r['k']), r['k'], x)
                      for r in rows for x in r['xs'] if x > 0), reverse=True)[:25]
    summary = {
        'K': K, 'curves': len(rows),
        'labels': {s: sum(1 for r in rows if r['status'] == s)
                   for s in ('certified_by_independent_computation', 'conditional_on_unproven_rank', 'scan_only')},
        'scan_disagreements': [r['k'] for r in rows if r.get('scan_agrees') is False],
        'points_beyond_scan': sum(1 for r in rows for x in r['xs'] if abs(x) > SCAN),
        'top_hall_ratios': [{'ratio': round(a, 6), 'k': k, 'x': x} for a, k, x in records],
        'engine': f'passagemath/Sage {sage.version.version}: integral_points, mwrank generators',
        'caveat': 'completeness is certified by Sage, not by Lean; conditional rows rest on an unproved rank',
    }
    (root / 'receipts' / 'mordell_census_summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'top_hall_ratios'}, indent=1))
    print('top:', summary['top_hall_ratios'][:5], f'{time.time() - t0:.0f}s')


if __name__ == '__main__':
    main()
