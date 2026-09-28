"""Genus-one cross-validation beyond the monic table: non-monic and shifted cubics, and m^3 = quadratic.

Run with a Sage / passagemath Python from the repository root:

    PYTHONPATH=python /opt/sagevenv/bin/python crosscheck/genus1_sage.py [trials] [workers]

Every family is reduced to an integral short Weierstrass model, keeping integrality explicit:

  m^2 = a n^3 + b n^2 + c n + e   (a != 0)
      X = a n, Y = a m:          Y^2 = X^3 + b X^2 + ac X + a^2 e
      U = 9X + 3b, V = 27Y:      V^2 = U^3 + A U + B,  A = 81ac - 27b^2,
                                                       B = 54b^3 - 243abc + 729a^2 e
      pull back: n = (U - 3b) / (9a),  m = V / (27a), both required to be integers.
  m^3 = a n^2 + b n + c          (a != 0, D = b^2 - 4ac != 0)
      X = 4a m, Y = 4a(2an + b):  Y^2 = X^3 + 16 a^2 D
      pull back: m = X / (4a),  n = (Y / (4a) - b) / (2a), both required to be integers.

Every integral (n, m) gives an integral (U, V) (resp. (X, Y)), so the Sage list of integral points
on the model, pulled back through the congruences, contains every hit.  Sage computes the model's
integral points from Mordell-Weil generators (rank proved by mwrank or analytic rank <= 1; the
label says which), saturation, and elliptic-logarithm sieving.  For each family we record the Sage
hits n >= 1, the exact sieve scan to SCAN (perfectpower.sieve), their agreement, and the largest
hit (the "late hit" benchmark).  Output: receipts/genus1_crossval.json.

Labels: INDEPENDENT_COMPUTATION (rank proved, saturated, scan agrees below SCAN),
CONDITIONAL_ON_UNPROVEN_RANK, SCAN_DISAGREEMENT (never certified), SCAN_EVIDENCE_ONLY (engine
failure).  Lean plays no part; crosscheck/check_genus1.py re-verifies the receipt in plain Python.
"""
import hashlib
import json
import random
import sys
import time
from math import isqrt
from multiprocessing import Pool
from pathlib import Path

SCAN = 10 ** 6
SEED = 20260928
EXTRA = [  # hand-picked: the external fuzzer's late hit, and classical cases
    ('cubic', [-1, -3, 2, 1]),        # n^3 + 2n^2 - 3n - 1: hits 2, 47882
    ('cubic', [4, 1, 0, 1]),          # n^3 + n + 4: hit 4128 (monic table)
    ('cubic', [0, 2, -3, 1]),         # 6 C(n,3) / n-shift sanity: n(n-1)(n-2)
    ('cubic', [1, 0, 0, 2]),          # 2n^3 + 1
    ('quadratic', [0, -1, 1]),        # n(n-1) = m^3 (2 C(n,2))
    ('quadratic', [1, 1, 1]),         # n^2 + n + 1 = m^3 (Nagell-Ljunggren type)
    ('quadratic', [2, 0, 1]),         # n^2 + 2 = m^3 (Fermat: n = 5)
]


def weierstrass(kind, f):
    if kind == 'cubic':
        e, c, b, a = f
        A = 81 * a * c - 27 * b * b
        B = 54 * b ** 3 - 243 * a * b * c + 729 * a * a * e
        return A, B
    c, b, a = f
    return 0, 16 * a * a * (b * b - 4 * a * c)


def pullback(kind, f, U, V):
    """All n >= 1 obtained from the model point (U, +-V)."""
    out = set()
    if kind == 'cubic':
        e, c, b, a = f
        if (U - 3 * b) % (9 * a) == 0 and V % (27 * a) == 0:
            n = (U - 3 * b) // (9 * a)
            if n >= 1:
                out.add(n)
    else:
        c, b, a = f
        if U % (4 * a) == 0:
            for W in (V, -V):
                if W % (4 * a) == 0 and (W // (4 * a) - b) % (2 * a) == 0:
                    n = (W // (4 * a) - b) // (2 * a)
                    if n >= 1:
                        out.add(n)
    return out


def is_hit(kind, f, n):
    v = sum(c * n ** i for i, c in enumerate(f))
    if kind == 'cubic':
        return v >= 0 and isqrt(v) ** 2 == v
    r = round(abs(v) ** (1 / 3)) if v else 0
    return any((s * k) ** 3 == v for k in (r - 1, r, r + 1) for s in (1, -1) if k >= 0)


def families(trials):
    rng = random.Random(SEED)
    out, seen = list(EXTRA), {tuple(f) for _, f in EXTRA}
    while len(out) < trials:
        if rng.random() < 0.7:
            a = rng.choice([1, 2, 3, 4, 5, 6, 7, -1, -2])
            f = [rng.randint(-8, 8), rng.randint(-8, 8), rng.randint(-6, 6), a]
            kind = 'cubic'
            A, B = weierstrass(kind, f)
            if 4 * A ** 3 + 27 * B ** 2 == 0:
                continue
            if a == 1 and f[2] == 0:
                continue                           # monic depressed: already in cubic_crossval
        else:
            a = rng.choice([1, 2, 3, 4, 5, 6, 7, -1, -3])
            f = [rng.randint(-20, 20), rng.randint(-10, 10), a]
            kind = 'quadratic'
            if f[1] ** 2 - 4 * a * f[0] == 0:
                continue
        if tuple(f) in seen:
            continue
        seen.add(tuple(f))
        out.append((kind, f))
    return out


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
    ENGINE = f'passagemath {sage.version.version}: integral_points(mw_base=gens, both_signs=True)'


def one(item):
    kind, f = item
    from perfectpower.sieve import sieve_hits
    A, B = weierstrass(kind, f)
    d = 2 if kind == 'cubic' else 3
    scan = sieve_hits(f, d, SCAN + 1)
    row = {'kind': kind, 'd': d, 'F_low_to_high': f, 'model_a_invariants': [0, 0, 0, A, B],
           'engine': ENGINE, 'scan_bound': SCAN, 'scan_hits': scan}
    try:
        E = EllipticCurve([0, 0, 0, A, B])
        try:
            rank, gens, method, proved = int(E.rank(proof=True)), None, 'mwrank (proof=True)', True
            gens = E.gens(proof=True)
        except RuntimeError:
            try:
                rank = int(E.rank(only_use_mwrank=False, proof=True))
                gens = E.gens(proof=True) if rank else []
                method, proved = 'analytic rank (only_use_mwrank=False, proof=True)', True
            except RuntimeError:
                rank, gens = int(E.rank(proof=False)), E.gens(proof=False)
                method, proved = 'unproven (proof=False)', False
        sat = int(E.saturation(gens)[1]) if gens else 1
        pts = sorted({(int(P[0]), int(P[1])) for P in E.integral_points(mw_base=gens, both_signs=True)})
    except BaseException as exc:                   # cysignals errors derive from BaseException
        if isinstance(exc, KeyboardInterrupt):
            raise
        row.update(certification='SCAN_EVIDENCE_ONLY', error=f'{type(exc).__name__}: {exc}'[:200])
        return row
    hits = sorted({n for U, V in pts for n in pullback(kind, f, U, V)})
    for n in hits:
        assert is_hit(kind, f, n), (f, n)
    agrees = [n for n in hits if n <= SCAN] == scan
    label = ('SCAN_DISAGREEMENT' if not agrees else
             'CONDITIONAL_ON_UNPROVEN_RANK' if not proved else
             'CONDITIONAL_ON_UNSATURATED_BASIS' if sat != 1 else 'INDEPENDENT_COMPUTATION')
    row.update(rank=rank, rank_method=method, rank_proved=proved, saturation_index=sat,
               generators=[[str(c) for c in P.xy()] for P in gens], model_integral_points=pts,
               hits=hits, max_hit=max(hits, default=None), scan_agrees=agrees, certification=label)
    return row


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    fams = families(trials)
    t0 = time.time()
    with Pool(workers, initializer=_setup, maxtasksperchild=50) as pool:
        rows = pool.map(one, fams, chunksize=2)
    root = Path(__file__).resolve().parents[1]
    labels = {}
    for r in rows:
        labels[r['certification']] = labels.get(r['certification'], 0) + 1
    late = sorted(((r['max_hit'], r['kind'], r['F_low_to_high']) for r in rows
                   if r.get('max_hit') and r['max_hit'] > 1000), reverse=True)
    body = json.dumps(rows, separators=(',', ':'))
    out = {'description': 'genus-one families m^2 = cubic (non-monic/shifted) and m^3 = quadratic; '
                          'Sage integral points on an integral Weierstrass model, pulled back',
           'seed': SEED, 'trials': len(rows), 'scan_bound': SCAN, 'labels': dict(sorted(labels.items())),
           'scan_disagreements': [r['F_low_to_high'] for r in rows if r.get('scan_agrees') is False],
           'hits_beyond_scan': [{'kind': k, 'F_low_to_high': f, 'max_hit': m} for m, k, f in late if m > SCAN],
           'late_hit_benchmark': [{'kind': k, 'F_low_to_high': f, 'max_hit': m} for m, k, f in late],
           'rows_sha256': hashlib.sha256(body.encode()).hexdigest(),
           'rows': rows}
    (root / 'receipts' / 'genus1_crossval.json').write_text(json.dumps(out, indent=0) + '\n')
    print(json.dumps({k: out[k] for k in ('trials', 'labels', 'scan_disagreements', 'hits_beyond_scan')}),
          f'{time.time() - t0:.0f}s')
    print('late:', out['late_hit_benchmark'][:10])


if __name__ == '__main__':
    main()
