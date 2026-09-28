"""Independent check of Theorem G: genus and places at infinity by normalisation in Sage.

For every d <= DMAX and every multiplicity profile (r_1 >= r_2 >= ...) with sum r_i <= DEGMAX,
take F = prod_i (x - i)^{r_i} (distinct integer roots, leading coefficient 1), g = gcd(d, r_i),
d' = d / g, and the geometric component y^{d'} = prod (x - i)^{r_i / g} (the other components are
twists by roots of unity and have the same invariants).  Sage's function-field machinery computes
its genus (integral closure / normalisation) and the places above x = infinity (geometric count =
sum of their degrees; the component is absolutely irreducible, so the constant field is Q).  We
compare 2 - 2 g_C - n_inf with Theorem G's d' (1 - S), S = sum (1 - 1/t_i), t_i = d / gcd(d, r_i),
and n_inf with gcd(d', deg F / g).

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


def _setup():
    global K, R, x, Y
    from sage.all__sagemath_schemes import QQ  # noqa: F401
    from sage.rings.function_field.constructor import FunctionField
    from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
    from sage.rings.rational_field import QQ as Q
    K = FunctionField(Q, 'x')
    x = K.gen()
    R = PolynomialRing(K, 'Y')
    Y = R.gen()


def one(item):
    d, rs = item
    g, dp, ts, S, chi, n_inf = formula(d, rs)
    row = {'d': d, 'multiplicities': rs, 't_profile': ts, 'd_prime': dp, 'S': str(S),
           'chi_formula': str(chi), 'n_inf_formula': n_inf}
    if dp == 1:
        row.update(genus_sage=0, n_inf_sage=1, chi_sage='1', agrees=(chi == 1 and n_inf == 1),
                   note='d\' = 1: the component is the graph of a polynomial')
        return row
    t0 = time.time()
    G = K.one()
    for i, r in enumerate(rs):
        G *= (x - i) ** (r // g)
    L = K.extension(Y ** dp - G, 'y')
    genus = int(L.genus())
    ninf = sum(int(P.degree()) for P in L(x).poles())
    chi_s = 2 - 2 * genus - ninf
    row.update(genus_sage=genus, n_inf_sage=ninf, chi_sage=str(chi_s),
               agrees=(Fraction(chi_s) == chi and ninf == n_inf), seconds=round(time.time() - t0, 2))
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
    finite = [r for r in rows if Fraction(r['chi_formula']) < 0]
    def exceptional(ts):
        big = sorted(t for t in ts if t > 1)
        return len(big) <= 1 or big == [2, 2]
    exceptional_ok = all((Fraction(r['S']) > 1) == (not exceptional(r['t_profile'])) for r in rows)
    out = {'description': 'Theorem G check: Sage genus and places at infinity vs chi = d\'(1 - S)',
           'd_max': DMAX, 'degree_max': DEGMAX, 'cases': len(rows), 'disagreements': bad,
           'cases_with_chi_negative': len(finite),
           'S_gt_1_iff_not_power_radical_pell': exceptional_ok,
           'seconds': round(time.time() - t0), 'rows': rows}
    root = Path(__file__).resolve().parents[1]
    (root / 'receipts' / 'theorem_g_check.json').write_text(json.dumps(out, indent=0) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'rows'}))


if __name__ == '__main__':
    main()
