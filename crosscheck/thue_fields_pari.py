"""Cubic-field fingerprints of the Thue obligations (external, PARI).

For each GL_2(Z) class of `receipts/thue_graph.json`, with representative
F(a, b) = c0 a^3 + c1 a^2 b + c2 a b^2 + c3 b^3 and theta a root of F(t, 1),

    F(a, b) = c0 N_{Q(theta)/Q}(a - b theta),

so the equation is a restricted norm equation in the cubic field Q(theta).  This script records
that field: a canonical defining polynomial (`polredabs`), the field discriminant, the signature,
the class number and the regulator (`bnfinit`, certified with `bnfcertify`).

**Sharing a field is not equivalence.**  Two classes in the same field can still differ in the
order containing a - b theta, the leading coefficient c0, and the right-hand side.  The field
groups only mark where unit and ideal computations could be reused.

Run: /opt/sagevenv/bin/python crosscheck/thue_fields_pari.py
Writes receipts/thue_fields.json.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(2 * 10 ** 9)
    g = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    rows, fields = [], {}
    for c in g['classes']:
        c0, c1, c2, c3 = c['representative']
        P = pari.Pol([c0, c1, c2, c3])
        red = pari.polredabs(P)
        key = str(red)
        if key not in fields:
            bnf = pari.bnfinit(red, 1)
            cert = int(pari.bnfcertify(bnf))
            fields[key] = {'polredabs': key, 'disc': int(pari.nfdisc(red)),
                           'signature': [int(x) for x in pari.nfinit(red)[1]],
                           'class_number': int(bnf.bnf_get_no()),
                           'regulator': float(bnf.bnf_get_reg()), 'bnfcertify': cert, 'classes': []}
        fields[key]['classes'].append(c['id'])
        rows.append({'class': c['id'], 'curves': c['curves'], 'field': key,
                     'order_index_sq': int(pari.poldisc(P) / pari.nfdisc(red)) if c0 != 0 else None})
    out = {'engine': 'PARI via passagemath cypari2 (bnfinit + bnfcertify)',
           'label': 'EXTERNAL: field identification only; not an equivalence of equations',
           'classes': len(rows), 'distinct_fields': len(fields),
           'fields': list(fields.values()), 'rows': rows}
    (ROOT / 'receipts' / 'thue_fields.json').write_text(json.dumps(out, indent=1) + '\n')
    print(f"{len(rows)} classes, {len(fields)} distinct cubic fields; "
          f"shared by more than one class: {sum(len(f['classes']) > 1 for f in fields.values())}")


if __name__ == '__main__':
    main()
