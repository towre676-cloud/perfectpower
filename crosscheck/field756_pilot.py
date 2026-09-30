"""Shared cubic-field pilot: one field, several open Thue obligations (external, PARI).

Field K = Q(x), x^3 - 6x - 2 = 0, discriminant 756, totally real, class number 1, unit rank 2.
Seven GL_2(Z) classes of `receipts/thue_graph.json` live in K.  They come from three open curves:
D = 7 (classes 0, 1, 2), D = 28 (18, 19, 20) and D = 63 (50).

For a class F = (c0, c1, c2, c3) with right side M, phi = c0 * theta is an algebraic integer
(root of t^3 + c1 t^2 + c0 c2 t + c0^2 c3), and

    F(a, b) = M   <=>   N_K(c0 a - b phi) = c0^2 M,

so every solution gives alpha = c0 a - b phi = gamma * eps1^n1 * eps2^n2 * (+-1), with gamma from
the finite list `bnfisintnorm(K, c0^2 M)` (h = 1, so the list is complete up to units).  The
Thue equation is then the condition that alpha lies in the rank-2 sublattice Z*c0 + Z*phi.

**What is shared** is computed once: the certified `bnf` (units, class group, regulator) and the
embedding of each class's phi into K (`nfisisom`).  **What is per class** is only the norm list
for c0^2 M and the solutions' exponent vectors.

**What is not claimed.**  Effective completeness needs an explicit upper bound
max(|n1|, |n2|) <= B for each (class, gamma), via Baker/Matveev on the Siegel unit equation plus
LLL reduction; below B, the enumeration is finite and could be Lean-checked.  This script does
not compute B and nothing here is promoted.  It records the shared data, and it measures that
every known solution has tiny exponents.  That is the input a bound certificate would reduce
against.

Run: /opt/sagevenv/bin/python crosscheck/field756_pilot.py   (about 10 s)
Writes receipts/field756_pilot.json.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIELD = 'x^3 - 6*x - 2'


def main():
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(10 ** 9)
    fields = json.loads((ROOT / 'receipts' / 'thue_fields.json').read_text())
    graph = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    cls = {c['id']: c for c in graph['classes']}
    ids = next(f['classes'] for f in fields['fields'] if f['polredabs'] == FIELD)
    red = pari(FIELD)
    bnf = pari.bnfinit(red, 1)
    cert = int(pari.bnfcertify(bnf))
    units = [str(u) for u in bnf.bnf_get_fu()]
    rows = []
    for i in ids:
        c = cls[i]
        c0, c1, c2, c3 = c['representative']
        M = c['M']
        g = pari.Pol([1, c1, c0 * c2, c0 * c0 * c3])
        emb = pari.nfisisom(g, red)[0]          # phi as a polynomial in x
        N = c0 * c0 * M
        gammas = list(pari.bnfisintnorm(bnf, N))  # -1 has norm -1: signs are units
        sols = pari.thue(pari.thueinit(pari.Pol([c0, c1, c2, c3]), 1), M)
        exps = []
        for s in sols:
            a, b = int(s[0]), int(s[1])
            alpha = pari.Mod(c0 * a - b * emb, red)
            hit = None
            for j, gm in enumerate(gammas):
                q = alpha / pari.Mod(gm, red)
                if abs(int(pari.norm(q))) == 1:
                    e = pari.bnfisunit(bnf, q.lift())
                    if len(e):  # empty unless q is a unit
                        hit = {'gamma': j, 'unit_exponents': [int(e[0]), int(e[1])],
                               'sign_index': int(pari.lift(e[2]))}
                        break
            if hit is None:
                raise SystemExit(f'class {i}: solution {(a, b)} not matched to a norm representative')
            exps.append({'a': a, 'b': b, **hit})
        rows.append({'class': i, 'curves': c['curves'], 'form': c['representative'], 'M': M,
                     'phi_in_K': str(emb), 'norm_target': N, 'norm_representatives': len(gammas),
                     'solutions': exps,
                     'max_abs_exponent': max((max(map(abs, e['unit_exponents'])) for e in exps), default=0)})
    out = {'engine': 'PARI via passagemath cypari2 (bnfinit, bnfcertify, bnfisintnorm, thue)',
           'label': 'EXTERNAL pilot data; no exponent bound is computed or claimed; nothing promoted',
           'field': FIELD, 'disc': int(pari.nfdisc(red)), 'bnfcertify': cert,
           'class_number': int(bnf.bnf_get_no()), 'fundamental_units': units,
           'regulator': float(bnf.bnf_get_reg()), 'classes': rows,
           'shared_work': 'one bnfinit + bnfcertify for all 7 classes (3 curves); per class only '
                          'bnfisintnorm(c0^2 M) and nfisisom',
           'missing_for_completeness': 'explicit bound B on unit exponents per (class, gamma) '
                                       '(Baker-Matveev + LLL reduction), then a finite checked search'}
    (ROOT / 'receipts' / 'field756_pilot.json').write_text(json.dumps(out, indent=1) + '\n')
    for r in rows:
        print(f"class {r['class']:2d} D={r['curves']} M={r['M']}: {r['norm_representatives']} norm reps, "
              f"{len(r['solutions'])} solutions, max |exponent| {r['max_abs_exponent']}")


if __name__ == '__main__':
    main()
