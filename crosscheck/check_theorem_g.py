"""Plain-Python gate for receipts/theorem_g_check.json (no Sage; run by `make receipts`).

It checks that the receipt covers every (d, profile) in its declared range exactly once, recomputes
every formula field (t-profile, d', S, chi = d'(1 - S), n_inf = gcd(d', deg F / g), the
Riemann-Hurwitz genus) and every agreement flag from the stored Singular/Sage values, and
recomputes the summary.  It does not rerun Singular or Sage.
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from theorem_g_sage import exceptional, formula, partitions  # noqa: E402

root = Path(__file__).resolve().parents[1]


def main():
    rec = json.loads((root / 'receipts' / 'theorem_g_check.json').read_text())
    rows = rec['rows']
    want = sorted((d, tuple(rs)) for d in range(2, rec['d_max'] + 1)
                  for n in range(1, rec['degree_max'] + 1) for rs in partitions(n))
    have = sorted((r['d'], tuple(r['multiplicities'])) for r in rows)
    assert have == want, 'receipt does not cover the declared range exactly once'
    bad = []
    for r in rows:
        g, dp, ts, S, chi, n_inf = formula(r['d'], r['multiplicities'])
        gf = (2 - n_inf - chi) / 2
        assert (r['t_profile'], r['d_prime'], r['S'], r['chi_formula'], r['n_inf_formula'],
                r['genus_formula']) == (ts, dp, str(S), str(chi), n_inf, str(gf)), r
        gs, ns = r['genus_singular'], r['n_inf_sage']
        agrees = gs is None or (Fraction(gs) == gf and (ns is None or ns == n_inf))
        assert agrees == r['agrees'], r
        if not agrees:
            bad.append(r)
    assert [(r['d'], r['multiplicities']) for r in bad] == \
        [(r['d'], r['multiplicities']) for r in rec['disagreements']]
    assert rec['n_inf_computed'] == sum(1 for r in rows if r['n_inf_sage'] is not None)
    gc = sum(1 for r in rows if r['genus_singular'] is not None)
    assert rec.get('genus_computed', gc) == gc
    rec['genus_computed'] = gc
    assert rec['S_gt_1_iff_not_power_radical_pell'] == all(
        (Fraction(r['S']) > 1) == (not exceptional(r['t_profile'])) for r in rows)
    print(f"Theorem G gate OK: {len(rows)} cases, genus computed in {rec['genus_computed']}, "
          f"places at infinity in {rec['n_inf_computed']}, {len(bad)} disagreements")


if __name__ == '__main__':
    main()
