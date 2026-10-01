"""D = 72 residual unit equation: field, units, norm representatives, lattice filter (external, PARI).

`H(u, v) = -3u^3 + 9uv^2 - 2v^3 = ±1` (MORDELL_BRANCH.md §7.1).  With `β^3 - 27β - 18 = 0`
and `γ = -3u - βv`, `N(γ) = 9 H(u, v)` (`NormForm.d72_det`), so every solution gives

    γ = ζ · α_j · ε1^e1 · ε2^e2,   N(α_j) = ±9,   ζ = ±1,

with `γ` in the lattice `Λ = 3ℤ + βℤ`.  In the power basis `γ = A + Bβ + Cβ²`, membership means
`C = 0` and `3 | A`, and then `u = -A/3`, `v = -B`.

This script computes, with PARI (`bnfinit`, `bnfcertify`):
- the maximal order, the field discriminant, the class number, and a certified fundamental unit
  basis;
- the elements of norm ±9 up to units (`bnfisintnorm`; the list is complete because `h = 1`);
- for every representative and sign, the exponent box `|e1|, |e2| <= B`, enumerated exactly.
  Each element is reconstructed in the power basis of β and the lattice test applied; every
  survivor is checked against `H(u, v) = ±1`.

**The box is a search, not a bound.**  Finding nothing in it proves nothing about larger
exponents.  Completeness needs a proved `B` (Baker–Matveev on the unit equation, then
reduction), which is not computed here.  PARI's own `thue` (external, `thueinit(·, 1)`) reports
no solution at all.

Run: /opt/sagevenv/bin/python crosscheck/d72_unit_pilot.py [B]
Writes receipts/d72_unit_pilot.json.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    import cypari2
    pari = cypari2.Pari()
    pari.allocatemem(2 * 10 ** 9)
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    g = pari('x^3 - 27*x - 18')                 # β
    bnf = pari.bnfinit(g, 1)
    cert = int(pari.bnfcertify(bnf))
    units = list(bnf.bnf_get_fu())
    H = lambda u, v: -3 * u ** 3 + 9 * u * v ** 2 - 2 * v ** 3  # noqa: E731
    eps = [pari.Mod(u, g) for u in units]
    pows = []
    for e in eps:
        tab = {0: pari.Mod(1, g)}
        for k in range(1, B + 1):
            tab[k] = tab[k - 1] * e
            tab[-k] = tab[-(k - 1)] / e
        pows.append(tab)

    def enumerate_box(target):
        """Every γ = ζ α ε1^e1 ε2^e2 with N(α) = ±target, |e_i| <= B, lying in 3Z + βZ."""
        reps = list(pari.bnfisintnorm(bnf, target)) + list(pari.bnfisintnorm(bnf, -target))
        checked, hits = 0, []
        for j, a in enumerate(reps):
            A0 = pari.Mod(a, g)
            for z in (1, -1):
                for e1 in range(-B, B + 1):
                    base = A0 * z * pows[0][e1]
                    for e2 in range(-B, B + 1):
                        pol = pari.lift(base * pows[1][e2])
                        c = [pari.polcoef(pol, i) for i in range(3)]
                        checked += 1
                        if c[2] == 0 and pari.denominator(c[0]) == 1 and pari.denominator(c[1]) == 1 \
                                and int(c[0]) % 3 == 0:
                            u, v = -int(c[0]) // 3, -int(c[1])
                            hits.append({'rep': j, 'sign': z, 'e': [e1, e2], 'u': u, 'v': v, 'H': H(u, v)})
        return reps, checked, hits

    reps, checked, lattice_hits = enumerate_box(9)
    solutions = [[h['u'], h['v']] for h in lattice_hits if abs(h['H']) == 1]
    # positive control: H(1, 1) = 4, so N(γ) = 36 must recover (u, v) = (1, 1) from the same pipeline
    _, ctrl_checked, ctrl_hits = enumerate_box(36)
    control = {'target_H': 4, 'expected': [1, 1], 'checked': ctrl_checked,
               'found': sorted({(h['u'], h['v']) for h in ctrl_hits if h['H'] in (4, -4)}),
               'passed': any((h['u'], h['v']) == (1, 1) for h in ctrl_hits)}
    if not control['passed']:
        raise SystemExit('positive control failed: the pipeline does not recover (1, 1) for H = 4')
    thue = [list(map(int, s)) for s in pari.thue(pari.thueinit(pari.Pol([-3, 0, 9, -2]), 1), 1)] + \
           [list(map(int, s)) for s in pari.thue(pari.thueinit(pari.Pol([-3, 0, 9, -2]), 1), -1)]
    out = {'engine': 'PARI via passagemath cypari2 (bnfinit, bnfcertify, bnfisintnorm, thue)',
           'label': 'EXTERNAL pilot; the exponent box is a search, not a bound; nothing promoted',
           'beta_polynomial': str(g), 'polredabs': str(pari.polredabs(g)),
           'field_discriminant': int(pari.nfdisc(g)), 'polynomial_discriminant': int(pari.poldisc(g)),
           'class_number': int(bnf.bnf_get_no()), 'bnfcertify': cert,
           'fundamental_units': [str(u) for u in units], 'regulator': float(bnf.bnf_get_reg()),
           'norm_pm9_representatives': [str(r) for r in reps],
           'box': B, 'elements_checked': checked, 'lattice_hits': lattice_hits,
           'solutions_in_box': solutions, 'pari_thue_solutions_pm1': thue,
           'positive_control': control,
           'missing_for_completeness': 'a proved bound B on max(|e1|, |e2|) for every representative and sign'}
    (ROOT / 'receipts' / 'd72_unit_pilot.json').write_text(json.dumps(out, indent=1) + '\n')
    print(f"field disc {out['field_discriminant']}, h = {out['class_number']}, certify {cert}, "
          f"{len(reps)} norm ±9 reps; box |e| <= {B}: {checked} elements, {len(lattice_hits)} in the lattice, "
          f"{len(solutions)} solutions; PARI thue: {thue}; control (H = 4): {control['found']}")


if __name__ == '__main__':
    main()
