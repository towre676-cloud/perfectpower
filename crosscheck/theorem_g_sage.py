"""Independent check of Theorem G: genus by normalisation (Singular) and places at infinity (Sage).

For every d <= DMAX and every multiplicity profile (r_1 >= r_2 >= ...) with sum r_i <= DEGMAX,
take F = prod_i (x - i)^{r_i} (distinct integer roots, leading coefficient 1), g = gcd(d, r_i),
d' = d / g, and the geometric component y^{d'} = prod (x - i)^{r_i / g} (the other components are
twists by roots of unity and have the same invariants).

  * genus: Singular's geometric genus of the plane curve (Sage `Curve(...).genus()`, computed via
    normalisation), for every case;
  * places at infinity: Sage's function field (integral closure), the geometric count being the
    sum of the degrees of the poles of x (the component is absolutely irreducible, so the constant
    field is Q).  This is slow for large covers, so it runs under a per-case alarm (NINF_SECONDS)
    and is recorded as null when it times out.

Theorem G predicts n_inf = gcd(d', deg F / g) and chi = 2 - 2 g_C - n_inf = d' (1 - S),
S = sum (1 - 1/t_i), t_i = d / gcd(d, r_i), i.e. g_C = (2 - n_inf - d'(1 - S)) / 2.  We compare
Singular's genus with that value in every case, and Sage's n_inf with gcd(d', deg F / g) where it
was computed.

Run: /opt/sagevenv/bin/python crosscheck/theorem_g_sage.py [DMAX] [DEGMAX] [workers]
Writes receipts/theorem_g_check.json.  An external computation: it tests the formula, it does not
prove it, and Siegel's theorem is not involved.
"""
import json
import sys
import time
from fractions import Fraction
from math import gcd
from multiprocessing import Pool
from pathlib import Path

NINF_SECONDS = 5


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield []
        return
    for p in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - p, p):
            yield [p] + rest


def formula(d, rs):
    g = gcd(d, *rs)
    dp = d // g
    ts = [d // gcd(d, r) for r in rs]
    S = sum(Fraction(t - 1, t) for t in ts)
    chi = dp * (1 - S)
    n_inf = gcd(dp, sum(rs) // g)
    return g, dp, ts, S, chi, n_inf


def exceptional(ts):
    big = sorted(t for t in ts if t > 1)
    return len(big) <= 1 or big == [2, 2]


def _setup():
    global K, R, x, Y, PXY, X2, Y2, Curve, alarm, cancel_alarm, AlarmInterrupt
    from sage.all__sagemath_schemes import QQ, PolynomialRing as PR, Curve as _Curve
    from sage.rings.function_field.constructor import FunctionField
    from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
    from cysignals.alarm import alarm as _alarm, cancel_alarm as _cancel, AlarmInterrupt as _AI
    K = FunctionField(QQ, 'x')
    x = K.gen()
    R = PolynomialRing(K, 'Y')
    Y = R.gen()
    PXY = PR(QQ, 'x,y')
    X2, Y2 = PXY.gens()
    Curve = _Curve
    alarm, cancel_alarm, AlarmInterrupt = _alarm, _cancel, _AI


def one(item):
    d, rs = item
    g, dp, ts, S, chi, n_inf = formula(d, rs)
    genus_formula = (2 - n_inf - chi) / 2
    row = {'d': d, 'multiplicities': rs, 't_profile': ts, 'd_prime': dp, 'S': str(S),
           'chi_formula': str(chi), 'n_inf_formula': n_inf, 'genus_formula': str(genus_formula)}
    t0 = time.time()
    if dp == 1:
        # y = prod (x - i)^{r_i / g}: the graph of a polynomial, genus 0, one point at infinity
        row.update(genus_singular=0, n_inf_sage=1, agrees=(genus_formula == 0 and n_inf == 1),
                   seconds=0.0)
        return row
    H = PXY.one()
    for i, r in enumerate(rs):
        H *= (X2 - i) ** (r // g)
    genus = int(Curve(Y2 ** dp - H).genus())
    ninf = None
    G = K.one()
    for i, r in enumerate(rs):
        G *= (x - i) ** (r // g)
    try:
        alarm(NINF_SECONDS)
        L = K.extension(Y ** dp - G, 'y')
        ninf = sum(int(P.degree()) for P in L(x).poles())
        cancel_alarm()
    except AlarmInterrupt:
        ninf = None
    except BaseException:
        cancel_alarm()
        raise
    row.update(genus_singular=genus, n_inf_sage=ninf,
               agrees=(Fraction(genus) == genus_formula and (ninf is None or ninf == n_inf)),
               seconds=round(time.time() - t0, 2))
    return row


def main():
    DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    DEGMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    items = [(d, rs) for d in range(2, DMAX + 1) for n in range(1, DEGMAX + 1) for rs in partitions(n)]
    t0 = time.time()
    with Pool(workers, initializer=_setup, maxtasksperchild=40) as pool:
        rows = pool.map(one, items, chunksize=4)
    bad = [r for r in rows if not r['agrees']]
    out = {'description': 'Theorem G check: Singular geometric genus (every case) and Sage places at '
                          'infinity (where computed within the alarm) against chi = d\'(1 - S)',
           'd_max': DMAX, 'degree_max': DEGMAX, 'cases': len(rows), 'disagreements': bad,
           'cases_with_chi_negative': sum(1 for r in rows if Fraction(r['chi_formula']) < 0),
           'n_inf_computed': sum(1 for r in rows if r['n_inf_sage'] is not None),
           'n_inf_alarm_seconds': NINF_SECONDS,
           'S_gt_1_iff_not_power_radical_pell': all(
               (Fraction(r['S']) > 1) == (not exceptional(r['t_profile'])) for r in rows),
           'rows': [{k: v for k, v in r.items() if k != 'seconds'} for r in rows]}
    root = Path(__file__).resolve().parents[1]
    (root / 'receipts' / 'theorem_g_check.json').write_text(json.dumps(out, indent=0) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'rows'}), f'{time.time() - t0:.0f}s')


if __name__ == '__main__':
    main()
