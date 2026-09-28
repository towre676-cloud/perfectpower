"""Cross-validate atlas scans of m^2 = n^3 + a n + b against Sage's certified integral points.

Run with a Sage (or passagemath) Python, from the repository root:

    PYTHONPATH=python sage -python crosscheck/cubics_sage.py            # or
    PYTHONPATH=python /opt/sagevenv/bin/python crosscheck/cubics_sage.py

For every nonsingular cubic with |a|, |b| <= BOUND it records
  * the stdlib scan hits n in [1, SCAN] (EXACT_COMPUTATION, this repository);
  * Sage's EllipticCurve.integral_points() with x >= 1 (Mordell-Weil generators from mwrank
    under proof=True, then elliptic-logarithm sieving; an independent computation);
  * whether the two agree, and whether any certified hit lies beyond the scan horizon.
Rows where mwrank cannot prove the rank are labelled conditional_on_unproven_rank; rows where the
engine fails are labelled scan_only.  PARI's ellratpoints step is replaced by an exact scan of the
same bounded interval because it segfaults on some curves in passagemath 10.8.12.
The Sage side is an external certificate: this repository does not re-check the Baker bound or
the elliptic-logarithm sieve, and Lean plays no part in it.
"""
import json
import sys
import time
from pathlib import Path

from sage.all__sagemath_schemes import EllipticCurve
import sage.all__sagemath_eclib  # noqa: F401  (mwrank backend)
import sage.all__sagemath_symbolics  # noqa: F401  (needed by integral_points)
import sage

from perfectpower.atlas import classify
from perfectpower.core import hit_indices

BOUND = int(sys.argv[1]) if len(sys.argv) > 1 else 10
SCAN = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 5

from sage.schemes.elliptic_curves.ell_rational_field import EllipticCurve_rational_field
from math import isqrt


def _integral_x_coords_exact(self, xmin, xmax):
    # Replacement for the PARI ellratpoints step, which segfaults on some curves in
    # passagemath 10.8.12 (e.g. a = -6, b = -5).  Exact scan of the same finite interval.
    a4, a6 = int(self.a4()), int(self.a6())
    xmin, xmax = int(xmin), int(xmax)
    if xmax - xmin > 10 ** 7:
        raise RuntimeError('interval too long for exact scan')
    out = set()
    for x in range(xmin, xmax + 1):
        v = x ** 3 + a4 * x + a6
        if v >= 0 and isqrt(v) ** 2 == v:
            out.add(x)
    return out


EllipticCurve_rational_field.integral_x_coords_in_interval = _integral_x_coords_exact

rows = []
t0 = time.time()
for a in range(-BOUND, BOUND + 1):
    for b in range(-BOUND, BOUND + 1):
        if 4 * a ** 3 + 27 * b ** 2 == 0:
            continue
        f = [b, a, 0, 1]
        scan = [n for n, _ in hit_indices(f, 2, 0, SCAN)]
        E = EllipticCurve([0, 0, 0, a, b])
        row = {'a': a, 'b': b, 'coefficients_F_low_to_high': f,
               'atlas_kind': classify(f, 2).kind, 'scan_hits': scan}
        status = 'certified_by_independent_computation'
        try:
            try:
                rank = int(E.rank(proof=True))
                gens = E.gens(proof=True)
            except RuntimeError as exc:           # mwrank cannot prove the rank
                row['rank_note'] = str(exc)
                try:                              # analytic rank <= 1 is provable (Kolyvagin)
                    rank = int(E.rank(only_use_mwrank=False, proof=True))
                    row['rank_method'] = 'analytic (only_use_mwrank=False, proof=True)'
                    gens = E.gens(proof=True) if rank else []
                except RuntimeError:
                    rank = int(E.rank(proof=False))
                    gens = E.gens(proof=False)
                    status = 'conditional_on_unproven_rank'
            pts = E.integral_points(mw_base=gens, both_signs=False)
        except (Exception, BaseException) as exc:  # PARI crashes surface as cysignals SignalError
            row.update(status='scan_only', engine_error=f'{type(exc).__name__}: {exc}')
            rows.append(row)
            print('engine error', a, b, exc, flush=True)
            continue
        sage_hits = sorted({int(P[0]) for P in pts if P[0] >= 1})
        beyond = [x for x in sage_hits if x > SCAN]
        row.update({
            'rank': rank, 'generators': [[str(c) for c in P.xy()] for P in gens],
            'sage_hits_x_ge_1': sage_hits,
            'agree_within_scan': [x for x in sage_hits if x <= SCAN] == scan,
            'certified_hits_beyond_scan': beyond,
            'status': status,
        })
        rows.append(row)
out = Path('receipts') / 'cubic_crossval.json'
summary = {
    'bound': BOUND, 'scan_horizon': SCAN, 'curves': len(rows),
    'certified_rows': sum(1 for r in rows if r['status'] == 'certified_by_independent_computation'),
    'conditional_rows': [(r['a'], r['b']) for r in rows if r['status'] == 'conditional_on_unproven_rank'],
    'scan_only_rows': [(r['a'], r['b'], r['engine_error']) for r in rows if r['status'] == 'scan_only'],
    'disagreements': [(r['a'], r['b']) for r in rows
                      if r['status'] != 'scan_only' and not r['agree_within_scan']],
    'rows_with_hits_beyond_scan': [(r['a'], r['b'], r['certified_hits_beyond_scan'])
                                   for r in rows if r.get('certified_hits_beyond_scan')],
    'max_certified_hit': max((max(r.get('sage_hits_x_ge_1', []), default=0), r['a'], r['b'])
                             for r in rows),
    'rows_needing_scan_beyond': {str(H): sum(1 for r in rows
                                             if max(r.get('sage_hits_x_ge_1', []), default=0) > H)
                                 for H in (10 ** 3, 10 ** 4, 10 ** 5)},
    'engine': f'passagemath/Sage {sage.version.version}: EllipticCurve.integral_points (mwrank, proof=True)',
    'seconds': round(time.time() - t0, 1),
}
out.write_text(json.dumps({'summary': summary, 'rows': rows}, indent=1) + '\n')
print(json.dumps(summary, indent=1))
