"""Exponent-residue tables for the D = 72 unit family (measurement; stdlib only, exact).

For a modulus q, reduce `ℤ[δ]` (`δ^3 = 9δ + 6`) mod q, take the periods of `ε1, ε2`, and list the
exponent residues `(r, s)` with `α ε1^r ε2^s` in the lattice `B ≡ 0` (and `A ≡ 0` when `3 | q`)
mod q.  Every solution's exponent pair reduces into this table, **given** unit generation
(`UnitPremises.UnitGen`).  These are necessary filters, not completeness results, and tables for
different moduli are correlated through shared periods, so their survival fractions do not
multiply.  Adapted from the direct-H handoff (Apache-2.0).

Run: python3 python/d72_unit_sieve.py     Writes receipts/d72_unit_sieve.json.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
P, Q = 9, 6
ALPHA, E1, E2 = (-3, -3, 1), (-1, -3, 1), (-1, 0, 2)


def mul(x, y, q):
    a, b, c = x
    d, e, f = y
    c0, c1, c2, c3, c4 = a * d, a * e + b * d, a * f + b * e + c * d, b * f + c * e, c * f
    return ((c0 + Q * c3) % q, (c1 + P * c3 + Q * c4) % q, (c2 + P * c4) % q)


def cycle(e, q):
    out, z = [], (1, 0, 0)
    while True:
        out.append(z)
        z = mul(z, e, q)
        if z == (1, 0, 0):
            return out
        assert len(out) < 100000


def main():
    rows = []
    for q in (3, 5, 7, 11, 13):
        p1, p2 = cycle(E1, q), cycle(E2, q)
        surv = 0
        for x in p1:
            base = mul(ALPHA, x, q)
            for y in p2:
                a, b, _ = mul(base, y, q)
                surv += b == 0 and (q % 3 != 0 or a == 0)
        rows.append({'q': q, 'periods': [len(p1), len(p2)], 'residue_pairs': len(p1) * len(p2),
                     'survivors': surv})
    out = {'label': 'MEASUREMENT: necessary lattice filters on the unit family, conditional on unit generation; '
                    'not completeness; moduli are correlated', 'moduli': rows}
    (ROOT / 'receipts' / 'd72_unit_sieve.json').write_text(json.dumps(out, indent=1) + '\n')
    for r in rows:
        print(f"q={r['q']}: periods {r['periods']}, {r['survivors']} of {r['residue_pairs']} residue pairs survive")


if __name__ == '__main__':
    main()
