"""D = 72 residual: the unit box search in exact integer arithmetic (no PARI).

In `ℤ[δ]`, `δ³ = 9δ + 6` (`NormForm.mulD`), with
- the units `ε₁ = δ² − 3δ − 1` and `ε₂ = 2δ² − 1` (norm −1, `NormForm.d72_norm_eps1/2`);
- `α = δ² − 3δ − 3` (norm 9, `d72_norm_alpha`).

Every `±α ε₁^{e₁} ε₂^{e₂}` with `|eᵢ| ≤ B` is computed exactly (inverses from the norm: for a unit
`x`, `x⁻¹ = ±adj(M_x)` on the basis), and the lattice test `B = 0 ∧ 3 ∣ A` (`d72_lattice`) applied.
A sanity control starts the same search at `γ(1, 1)` (norm 36) and must read `(u, v) = (1, 1)` back.
It checks the ring arithmetic, the inverses and the lattice readout, not the completeness of the
representatives (the PARI pilot `crosscheck/d72_unit_pilot.py` has the representative-level control).

**This is a search, not a completeness proof**: that `ε₁, ε₂` generate the unit group, that the
norm representatives are complete, and that every solution lies in the box are all unproved.

Run: python3 python/d72_delta_box.py [B]     Writes receipts/d72_delta_box.json.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
P, Q = 9, 6


def mul(x, y):
    c = [0] * 5
    for i in range(3):
        for j in range(3):
            c[i + j] += x[i] * y[j]
    c[2] += P * c[4]
    c[1] += Q * c[4]
    c[1] += P * c[3]
    c[0] += Q * c[3]
    return (c[0], c[1], c[2])


def mat(x):
    cols = [mul(x, e) for e in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]
    return [[cols[j][i] for j in range(3)] for i in range(3)]


def det(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def unit_inverse(x):
    """x^{-1} for a unit: the first column of adj(M_x) / det, exact."""
    m = mat(x)
    d = det(m)
    assert d in (1, -1)
    cof = lambda i, j: ((-1) ** (i + j)) * det2([[m[a][b] for b in range(3) if b != j] for a in range(3) if a != i])  # noqa: E731
    inv = tuple(cof(0, i) * d for i in range(3))   # column 0 of adj = cofactors of row 0 transposed
    assert mul(x, inv) == (1, 0, 0)
    return inv


def det2(m):
    return m[0][0] * m[1][1] - m[0][1] * m[1][0]


def H(u, v):
    return -3 * u ** 3 + 9 * u * v ** 2 - 2 * v ** 3


def powers(x, B):
    xi = unit_inverse(x)
    tab = {0: (1, 0, 0)}
    for k in range(1, B + 1):
        tab[k] = mul(tab[k - 1], x)
        tab[-k] = mul(tab[-(k - 1)], xi)
    return tab


def search(alpha, B, e1, e2):
    p1, p2 = powers(e1, B), powers(e2, B)
    hits, n = [], 0
    for s in (1, -1):
        for a in range(-B, B + 1):
            base = mul(tuple(s * c for c in alpha), p1[a])
            for b in range(-B, B + 1):
                A_, B_, C_ = mul(base, p2[b])
                n += 1
                if B_ == 0 and A_ % 3 == 0:
                    u, v = -A_ // 3 - 2 * C_, C_
                    hits.append({'sign': s, 'e': [a, b], 'u': u, 'v': v, 'H': H(u, v)})
    return n, hits


def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    e1, e2, alpha = (-1, -3, 1), (-1, 0, 2), (-3, -3, 1)
    norms = {'eps1': det(mat(e1)), 'eps2': det(mat(e2)), 'alpha': det(mat(alpha))}
    assert norms == {'eps1': -1, 'eps2': -1, 'alpha': 9}
    n, hits = search(alpha, B, e1, e2)
    # positive control: gamma for (u, v) = (1, 1) has norm 9 H(1, 1) = 36; search from it with the
    # same units must find (1, 1) at exponent (0, 0)
    g11 = (-3 * 1 - 6 * 1, 0, 1)
    assert det(mat(g11)) == 9 * H(1, 1)
    _, ctrl = search(g11, 3, e1, e2)
    control = {'start': 'gamma(1, 1)', 'found_11': any((h['u'], h['v']) == (1, 1) for h in ctrl)}
    if not control['found_11']:
        raise SystemExit('positive control failed')
    out = {'label': 'exact integer search in Z[delta]; not a completeness proof (unit generation, '
                    'representative completeness and the exponent bound are unproved)',
           'delta_relation': 'delta^3 = 9 delta + 6', 'units': {'eps1': e1, 'eps2': e2}, 'alpha': alpha,
           'norms': norms, 'box': B, 'elements_checked': n, 'lattice_hits': hits,
           'solutions': [[h['u'], h['v']] for h in hits if abs(h['H']) == 1], 'sanity_control': control}
    (ROOT / 'receipts' / 'd72_delta_box.json').write_text(json.dumps(out, indent=1) + '\n')
    print(f"box |e| <= {B}: {n} elements, {len(hits)} lattice hits, {len(out['solutions'])} solutions; "
          f"control {control}")


if __name__ == '__main__':
    main()
