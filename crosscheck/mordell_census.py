"""Mordell census: all integral points of y^2 = x^3 + k for 0 < |k| <= K (Hall's conjecture frontier).

Run with a Sage / passagemath Python from the repository root:

    /opt/sagevenv/bin/python crosscheck/mordell_census.py 10000 [workers]

Per curve (data/mordell_census.jsonl, one JSON object per k) the census records:
  curve a-invariants; engine and version; rank and how it was proved (mwrank 2-descent,
  analytic rank <= 1, or unproven); Mordell-Weil generators; the saturation index returned by
  E.saturation(gens) (1 = saturated at all primes checked by Sage); the integral-point method;
  the sorted x-coordinates and their SHA-256; and the independent scan result for |x| <= 1e5.

Labels (docs/TRUST_BOUNDARY.md):
  INDEPENDENT_COMPUTATION        rank proved, generators saturated, points re-verified exactly,
                                 and the independent scan |x| <= 1e5 agrees
  CONDITIONAL_ON_UNPROVEN_RANK   generators from proof=False; everything else as above
  SCAN_DISAGREEMENT              Sage's list and the scan disagree on |x| <= 1e5 (never certified)
  SCAN_EVIDENCE_ONLY             engine failure; only the scan is recorded
Completeness is Sage's claim, not Lean's; Generated/MordellPoints.lean checks only that listed
points lie on their curves.

Also writes data/mordell_census.csv (flat view, including the engine column) and
receipts/mordell_census_summary.json; `python3 crosscheck/mordell_census.py --from-jsonl` rebuilds
both from the JSONL without Sage (run by `make receipts`), after checking that the keys are
exactly 0 < |k| <= K once each, every x-list is strictly increasing, and every row passes
`check_row`.  It does not rerun the scan; only `make crosscheck` does.
"""
import csv
import hashlib
import json
import sys
import time
from math import isqrt
from multiprocessing import Pool
from pathlib import Path

SCAN = 10 ** 5
ENGINE = None


def _setup():
    global EllipticCurve, ENGINE
    from sage.all__sagemath_schemes import EllipticCurve as _E
    import sage.all__sagemath_eclib  # noqa: F401
    import sage.all__sagemath_symbolics  # noqa: F401
    import sage.version
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
    ENGINE = (f'passagemath {sage.version.version}: EllipticCurve.integral_points(mw_base=gens, '
              f'both_signs=False); gens from mwrank; ellratpoints step replaced by exact interval scan')


def scan_points(k):
    """Independent check: all x with |x| <= SCAN and x^3 + k a square."""
    out = []
    for x in range(-SCAN, SCAN + 1):
        v = x ** 3 + k
        if v >= 0:
            r = isqrt(v)
            if r * r == v:
                out.append(x)
    return out


def xs_hash(xs):
    return hashlib.sha256(' '.join(map(str, xs)).encode()).hexdigest()


def one(k):
    E = EllipticCurve([0, 0, 0, 0, k])
    scan = scan_points(k)
    row = {'k': k, 'a_invariants': [0, 0, 0, 0, k], 'engine': ENGINE, 'scan_x_abs_le_1e5': scan}
    try:
        try:
            rank = int(E.rank(proof=True))
            gens = E.gens(proof=True)
            method = 'mwrank (proof=True)'
            proved = True
        except RuntimeError:
            try:
                rank = int(E.rank(only_use_mwrank=False, proof=True))
                gens = E.gens(proof=True) if rank else []
                method = 'analytic rank (only_use_mwrank=False, proof=True)'
                proved = True
            except RuntimeError:
                rank = int(E.rank(proof=False))
                gens = E.gens(proof=False)
                method = 'unproven (proof=False)'
                proved = False
        sat_index = int(E.saturation(gens)[1]) if gens else 1
        pts = E.integral_points(mw_base=gens, both_signs=False)
        xs = sorted({int(P[0]) for P in pts})
    except BaseException as exc:          # cysignals SignalError derives from BaseException
        if isinstance(exc, KeyboardInterrupt):
            raise
        row.update(certification='SCAN_EVIDENCE_ONLY', error=f'{type(exc).__name__}: {exc}'[:200],
                   x_coordinates=scan, x_hash=xs_hash(scan))
        return row
    for x in xs:                                   # exact re-verification
        v = x ** 3 + k
        assert v >= 0 and isqrt(v) ** 2 == v, (k, x)
    agrees = [x for x in xs if abs(x) <= SCAN] == scan
    if not agrees:
        label = 'SCAN_DISAGREEMENT'
    elif not proved or sat_index != 1:
        label = 'CONDITIONAL_ON_UNPROVEN_RANK' if not proved else 'CONDITIONAL_ON_UNSATURATED_BASIS'
    else:
        label = 'INDEPENDENT_COMPUTATION'
    row.update(rank=rank, rank_method=method, rank_proved=proved,
               generators=[[str(c) for c in P.xy()] for P in gens], saturation_index=sat_index,
               torsion=int(E.torsion_order()), discriminant=int(E.discriminant()),
               x_coordinates=xs, x_hash=xs_hash(xs), scan_agrees=agrees, certification=label)
    return row


def hall(x, k):
    return isqrt(abs(x) * 10 ** 12) / 10 ** 6 / abs(k)


def check_row(r):
    """Gate for the committed JSONL: hash, exact point check, and the label rule."""
    xs, k = r['x_coordinates'], r['k']
    assert r['x_hash'] == xs_hash(xs), ('hash', k)
    for x in xs:
        v = x ** 3 + k
        assert v >= 0 and isqrt(v) ** 2 == v, ('point', k, x)
    if r['certification'] == 'SCAN_EVIDENCE_ONLY':
        return
    scan = [x for x in xs if abs(x) <= SCAN]
    agrees = scan == r['scan_x_abs_le_1e5']
    assert agrees == r['scan_agrees'], ('scan flag', k)
    expected = ('SCAN_DISAGREEMENT' if not agrees else
                'CONDITIONAL_ON_UNPROVEN_RANK' if not r['rank_proved'] else
                'CONDITIONAL_ON_UNSATURATED_BASIS' if r['saturation_index'] != 1 else
                'INDEPENDENT_COMPUTATION')
    assert r['certification'] == expected, ('label', k, r['certification'], expected)


def check_domain(rows, K):
    """Gate for the whole file: the keys are exactly {-K..-1, 1..K}, once each, in order; every
    x-list is strictly increasing (sorted, no duplicates) and every curve is the declared one."""
    ks = [r['k'] for r in rows]
    expected = [k for k in range(-K, K + 1) if k != 0]
    if ks != expected:
        from collections import Counter
        dup = sorted(k for k, c in Counter(ks).items() if c > 1)
        missing = sorted(set(expected) - set(ks))
        extra = sorted(set(ks) - set(expected))
        raise AssertionError(f'census domain: duplicates {dup[:5]}, missing {missing[:5]}, '
                             f'outside bound {extra[:5]}, sorted={ks == sorted(ks)}')
    for r in rows:
        xs = r['x_coordinates']
        assert all(a < b for a, b in zip(xs, xs[1:])), ('x-list not strictly increasing', r['k'])
        assert r['a_invariants'] == [0, 0, 0, 0, r['k']], ('curve', r['k'])
        assert r['scan_x_abs_le_1e5'] == sorted(set(r['scan_x_abs_le_1e5'])), ('scan list', r['k'])


def write_outputs(rows, K, root):
    """Flat CSV and summary, derived from the per-curve rows (the JSONL is the primary record)."""
    with open(root / 'data' / 'mordell_census.csv', 'w', newline='') as fh:
        w = csv.writer(fh, lineterminator='\n')
        w.writerow(['k', 'rank', 'rank_method', 'rank_proved', 'saturation_index', 'torsion',
                    'n_points_up_to_sign', 'x_coordinates', 'x_sha256', 'max_x', 'max_hall_ratio',
                    'scan_agrees_up_to_1e5', 'certification', 'engine'])
        for r in rows:
            xs = r['x_coordinates']
            hr = max((hall(x, r['k']) for x in xs if x > 0), default=None)
            w.writerow([r['k'], r.get('rank', ''), r.get('rank_method', ''), r.get('rank_proved', ''),
                        r.get('saturation_index', ''), r.get('torsion', ''), len(xs), ' '.join(map(str, xs)),
                        r['x_hash'], max(xs, default=''), f'{hr:.6f}' if hr is not None else '',
                        r.get('scan_agrees', ''), r['certification'], r.get('engine', '')])
    records = sorted(((hall(x, r['k']), r['k'], x) for r in rows for x in r['x_coordinates'] if x > 0),
                     reverse=True)[:25]
    labels = {}
    for r in rows:
        labels[r['certification']] = labels.get(r['certification'], 0) + 1
    engines = sorted({r['engine'] for r in rows if r.get('engine')})
    summary = {
        'K': K, 'curves': len(rows), 'labels': dict(sorted(labels.items())),
        'scan_disagreements': [r['k'] for r in rows if r.get('scan_agrees') is False],
        'unsaturated': [r['k'] for r in rows if r.get('saturation_index', 1) != 1],
        'points_beyond_scan': sum(1 for r in rows for x in r['x_coordinates'] if abs(x) > SCAN),
        'total_points': sum(len(r['x_coordinates']) for r in rows),
        'top_hall_ratios': [{'ratio': round(a, 6), 'k': k, 'x': x} for a, k, x in records],
        'engine': engines,
        'jsonl_sha256': hashlib.sha256((root / 'data' / 'mordell_census.jsonl').read_bytes()).hexdigest(),
        'caveat': 'completeness is certified by Sage, not by Lean; conditional rows rest on an '
                  'unproved rank; Lean checks only that listed points lie on their curves',
    }
    (root / 'receipts' / 'mordell_census_summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    return summary


def main():
    root = Path(__file__).resolve().parents[1]
    if sys.argv[1:2] == ['--from-jsonl']:
        # rebuild the CSV and summary from the committed JSONL (plain Python, no Sage needed)
        rows = [json.loads(line) for line in open(root / 'data' / 'mordell_census.jsonl')]
        K = int(sys.argv[2]) if len(sys.argv) > 2 else 10000        # the declared bound
        check_domain(rows, K)
        for r in rows:
            check_row(r)
        summary = write_outputs(rows, K, root)
        print(json.dumps({k: v for k, v in summary.items() if k != 'top_hall_ratios'}, indent=1))
        return
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    ks = [k for k in range(-K, K + 1) if k != 0]
    t0 = time.time()
    with Pool(workers, initializer=_setup, maxtasksperchild=200) as pool:
        rows = sorted(pool.imap_unordered(one, ks, chunksize=8), key=lambda r: r['k'])
    (root / 'data').mkdir(exist_ok=True)
    with open(root / 'data' / 'mordell_census.jsonl', 'w') as fh:
        for r in rows:
            fh.write(json.dumps(r, separators=(',', ':')) + '\n')
    summary = write_outputs(rows, K, root)
    print(json.dumps({k: v for k, v in summary.items() if k != 'top_hall_ratios'}, indent=1))
    print('top:', summary['top_hall_ratios'][:5], f'{time.time() - t0:.0f}s')


if __name__ == '__main__':
    main()
