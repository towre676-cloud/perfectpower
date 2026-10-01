"""Exponent bounds for the seven Thue classes of the shared field 756 (external certificate).

`K = Q(x)`, `x^3 = 6x + 2`, discriminant 756, `O_K = Z[x]`, `h = 1` (PARI `bnfcertify`).  The
classes are those of `field756_pilot.py`: D = 7 (0, 1, 2), D = 28 (18, 19, 20), D = 63 (50).

Per class `F = (c0, c1, c2, c3)`, `M`:
- PARI gives `phi = c0 θ` in `Z[x]` (`nfisisom`), the norm representatives `γ0` of `c0^2 M`
  (`bnfisintnorm`) and the fundamental units;
- `thue_bound.bound` gives `V0` and `H` (Matveev, then reduction) for every `(γ0, i0)`;
- the solutions with `|b| <= V0` are listed exactly, and PARI's own `thue` list is recorded for the
  comparison the Lean box check makes.

Run: /opt/sagevenv/bin/python crosscheck/thue_bound_field756.py   (needs PARI and mpmath)
Writes receipts/field756_bound.json, the input of python/make_lean_field756.py.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

from thue_bound import Field, bound, evalF  # noqa: E402

FIELD = 'x^3 - 6*x - 2'
P, Q = 6, 2


def coords(pari, z):
    """An element of Z[x] as (A, B, C)."""
    v = pari.lift(z) if 'Mod' in str(pari.type(z)) or str(pari.type(z)) == 't_POLMOD' else z
    c = [int(pari.polcoef(v, i)) for i in range(3)]
    return tuple(c)


def main():
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(10 ** 9)
    pilot = json.loads((ROOT / 'receipts' / 'field756_pilot.json').read_text())
    red = pari(FIELD)
    bnf = pari.bnfinit(red, 1)
    assert int(pari.bnfcertify(bnf)) == 1
    assert int(bnf.bnf_get_no()) == 1
    assert int(pari.nfdisc(red)) == int(pari.poldisc(red)) == 756, 'O_K = Z[x]'
    fu = [coords(pari, u) for u in bnf.bnf_get_fu()]
    K = Field(P, Q)
    rows = []
    for c in pilot['classes']:
        F, M = tuple(c['form']), c['M']
        c0, c1, c2, c3 = F
        g = pari.Pol([1, c1, c0 * c2, c0 * c0 * c3])
        phi = coords(pari, pari.nfisisom(g, red)[0])
        gammas = [coords(pari, gm) for gm in pari.bnfisintnorm(bnf, c0 * c0 * M)]
        thue = sorted((int(s[0]), int(s[1])) for s in pari.thue(pari.thueinit(pari.Pol([c0, c1, c2, c3]), 1), M))
        for a, b in thue:
            assert evalF(F, a, b) == M
        r = bound(K, F, M, phi, gammas, fu[0], fu[1])
        small = r['small_b_solutions']
        assert set(small) <= set(thue), 'exact small-b search found a solution PARI did not'
        rows.append({'class': c['class'], 'curves': c['curves'], 'form': list(F), 'M': M, 'phi': list(phi),
                     'gammas': [list(x) for x in gammas], 'pari_thue': [list(x) for x in thue],
                     'V0': r['V0'], 'H_bound': r['H_bound'], 'small_b_solutions': [list(x) for x in small],
                     'cases': r['cases']})
        print(f"class {c['class']:2d} D={c['curves']} M={M}: {len(gammas)} rep(s), V0={r['V0']}, "
              f"H <= {r['H_bound']} ({[x['H_reduced'] for x in r['cases']]}), small-b {small}, PARI {thue}")
    out = {'label': 'EXTERNAL certificate: structural input from PARI (bnfcertify, bnfisintnorm, nfisisom), '
                    'Matveev + interval reduction in Python (mpmath.iv, 900 bits); the box below the bound '
                    'is replayed in Lean (Generated/Field756.lean)',
           'field': FIELD, 'P': P, 'Q': Q, 'units': [list(u) for u in fu], 'classes': rows,
           'statement': 'for each class and each solution (a, b) of F(a, b) = M with |b| > V0: '
                        'c0 a - b phi = ±gamma0 eps1^e1 eps2^e2 for a listed gamma0, max |e_i| <= H_bound'}
    (ROOT / 'receipts' / 'field756_bound.json').write_text(json.dumps(out, indent=1) + '\n')


if __name__ == '__main__':
    main()
