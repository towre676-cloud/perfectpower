"""The exponent bound for the D = 72 residual Thue equation (external certificate).

    H(u, v) = -3u^3 + 9uv^2 - 2v^3 = ±1        (MORDELL_BRANCH.md §7.1)

Field `K = Q(δ)`, `δ^3 = 9δ + 6`, `O_K = Z[δ]` (discriminant 1944).  The form is
`F = (-3, 0, 9, -2)` with `φ = β = 6 - δ^2` and `γ = -3u - βv`, so `N(γ) = 9 H(u, v)`
(`NormForm.d72_det_delta`).  The norm-9 representative is `α = δ^2 - 3δ - 3`, and `-α` covers
norm `-9`; the units are `ε1 = δ^2 - 3δ - 1`, `ε2 = 2δ^2 - 1`.

This is the general pipeline `thue_bound.py` (Siegel, Matveev, then the direct maximum-exponent
reduction with exact rational stages) applied to this field with `|M| = 1`.

Run: /opt/sagevenv/bin/python crosscheck/thue_bound_d72.py
Writes receipts/d72_thue_bound.json, an input of python/make_lean_unit_fields.py.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))

from thue_bound import Field, bound  # noqa: E402

FORM = (-3, 0, 9, -2)
PHI = (6, 0, -1)
ALPHA = (-3, -3, 1)
EPS1, EPS2 = (-1, -3, 1), (-1, 0, 2)


def main():
    K = Field(9, 6)
    r = bound(K, FORM, 1, PHI, [ALPHA], EPS1, EPS2)
    small = sorted(set(r['small_b_solutions']) | set(__import__('thue_bound').small_b(FORM, -1, r['V0'])))
    out = {'label': 'EXTERNAL certificate: structural input from PARI (bnfcertify; the norm-9 ideal), Matveev and '
                    'the conjugate estimates in mpmath interval arithmetic; the reduction stages are exact and '
                    'replayed by the Lean kernel (DirectReduction.chainCheck)',
           'equation': 'H(u,v) = -3u^3 + 9uv^2 - 2v^3 = ±1', 'field': 'x^3 - 9x - 6, O_K = Z[x], h = 1',
           'P': 9, 'Q': 6, 'form': list(FORM), 'phi': list(PHI), 'gammas': [list(ALPHA)],
           'units': [list(EPS1), list(EPS2)], 'cases': r['cases'], 'V0': r['V0'],
           'small_v_solutions': small, 'H_bound': r['H_bound'],
           'statement': f"every solution with |v| > {r['V0']} has gamma = ±alpha eps1^e1 eps2^e2 with "
                        f"max(|e1|,|e2|) <= {r['H_bound']}"}
    (ROOT / 'receipts' / 'd72_thue_bound.json').write_text(json.dumps(out, indent=1) + '\n')
    for c in r['cases']:
        print(f"i0={c['i0']}: V0={c['V0']} H0={c['H0']} -> {[s['B'] for s in c['steps']]} -> H <= {c['H_reduced']}")
    print(f"V0 = {r['V0']}, small-|v| solutions: {small}, H bound {r['H_bound']}")


if __name__ == '__main__':
    main()
