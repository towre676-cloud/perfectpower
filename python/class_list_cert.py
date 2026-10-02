"""Certificates for `ClassListProof.classList_of` (`PerfectPower/Generated/ClassLists.lean`).

For `y² = x³ + k` the class-list premise `ClassList k Gs` (every form `(a, 3b, 3c, d)` with
`Δ = 4k` is equivalent to a listed class) is proved in Lean from:
* rational parameters `s0, s1, H, M, amax` for `CubicReduction.int_bounds` at `|D| = 108k`
  (`ParamsOK`, checked by `norm_num`);
* integer box bounds `amax`, `bmax` with `M + amax ≤ 3 bmax`, `2M ≤ 3 bmax`, `4k ≤ bmax²`;
* a transport certificate `(F, G, p, q, r, s)`, `act G p q r s = F`, for every form `F` of the box
  with `Δ = 4k` (`ClassListProof.boxCertB`, checked by the kernel).

Run: python3 python/class_list_cert.py
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import positive_k as PK  # noqa: E402
from perfectpower import thue_graph as TG  # noqa: E402


def act(F, p, q, r, s):
    """Exact mirror of `MordellCubicForm.act` on `(a, b, c, d)` (shape `(a, 3b, 3c, d)`)."""
    a, b, c, d = F
    return (a * p ** 3 + 3 * b * p * p * r + 3 * c * p * r * r + d * r ** 3,
            a * p * p * q + b * (p * p * s + 2 * p * q * r) + c * (q * r * r + 2 * p * r * s) + d * r * r * s,
            a * p * q * q + b * (2 * p * q * s + q * q * r) + c * (p * s * s + 2 * q * r * s) + d * r * s * s,
            a * q ** 3 + 3 * b * q * q * s + 3 * c * q * s * s + d * s ** 3)


def delta(F):
    a, b, c, d = F
    return (a * d - b * c) ** 2 - 4 * (a * c - b * b) * (b * d - c * c)


def _rat_up(x, den=10 ** 6):
    return Fr(math.ceil(x * den), den)


def _rat_down(x, den=10 ** 6):
    return Fr(math.floor(x * den), den)


def params(k):
    """Rational parameters satisfying `ClassListProof.ParamsOK k` (verified exactly here)."""
    D = 108 * k
    s0 = _rat_down((27 / D ** 2) ** (1 / 3) * 0.999)
    s1 = _rat_up(2 / D ** 0.5 * 1.001)
    h = lambda s: Fr(9, 4) * s + Fr(3) / (D * s)          # noqa: E731
    H = _rat_up(float(max(h(s0), h(s1))) * 1.0001)
    M = _rat_up((D ** 2 * float(H) ** 3 / 27) ** 0.5 * 1.0001)
    amax_r = _rat_up((D ** 2 * float(s1) ** 3 / 27) ** 0.5 * 1.0001)
    assert 0 < s0 and D ** 2 * s0 ** 3 <= 27 and 4 <= D * s1 ** 2 and s0 <= s1
    assert 9 * s0 ** 2 * D + 12 <= 4 * H * s0 * D and 9 * s1 ** 2 * D + 12 <= 4 * H * s1 * D
    assert D ** 2 * H ** 3 <= 27 * M ** 2 and D ** 2 * s1 ** 3 <= 27 * amax_r ** 2
    amax = math.ceil(amax_r)
    bmax = max(math.ceil((M + amax_r) / 3), math.ceil(2 * M / 3), math.isqrt(4 * k - 1) + 1)
    assert M + amax_r <= 3 * bmax and 2 * M <= 3 * bmax and 4 * k <= bmax ** 2
    return {'s0': s0, 's1': s1, 'H': H, 'M': M, 'amax_r': amax_r, 'amax': amax, 'bmax': bmax}


def t_cands(al, be, ga):
    """Mirror of `ReducibleThue.tCands`."""
    if al != 0:
        disc = be * be - 4 * al * ga
        r = math.isqrt(disc) if disc >= 0 else 0
        return [(z - be) // (2 * al) for z in (r, -r) if (z - be) % (2 * al) == 0]
    if be != 0:
        return [-ga // be] if ga % be == 0 else []
    return []


def box_forms(k, amax, bmax):
    """Mirror of the loops of `ClassListProof.boxCertB`: the forms of the box with `Δ = 4k`."""
    out = []
    for a in range(-amax, amax + 1):
        for b in range(-bmax, bmax + 1):
            for c in range(-bmax, bmax + 1):
                al, be, ga = a * a, -2 * a * b * c - 4 * b * (a * c - b * b), b * b * c * c + 4 * c * c * (a * c - b * b) - 4 * k
                assert al != 0 or be != 0 or ga != 0
                for d in t_cands(al, be, ga):
                    if delta((a, b, c, d)) == 4 * k:
                        out.append((a, b, c, d))
    return out


def inverse(T):
    (p, q), (r, s) = T
    e = p * s - q * r
    assert e in (1, -1)
    return ((e * s, -e * q), (-e * r, e * p))


def certificate(F, Gs):
    """`(G, p, q, r, s)` with `G ∈ Gs` and `act G p q r s = F`."""
    std = (F[0], 3 * F[1], 3 * F[2], F[3])
    key, T = PK.canonical(std)                       # std ∘ T = key
    for G in Gs:
        Gstd = (G[0], 3 * G[1], 3 * G[2], G[3])
        if Gstd == key:
            S = inverse(T)                           # key ∘ T⁻¹ = std
            break
        U = PK.equivalent(key, Gstd)                 # key ∘ U = Gstd
        if U:
            S = TG.matmul(inverse(U), inverse(T))    # Gstd ∘ U⁻¹ = key, key ∘ T⁻¹ = std
            break
    else:
        raise AssertionError(f'no class for {F}')
    (p, q), (r, s) = S
    assert act(G, p, q, r, s) == F and (p * s - q * r) ** 2 == 1
    return (G, p, q, r, s)


def build(k, Gs):
    P = params(k)
    forms = box_forms(k, P['amax'], P['bmax'])
    certs = [(F,) + certificate(F, Gs) for F in forms]
    return P, certs


def _i(n):
    return f'({n})' if n < 0 else str(n)


def _q(x):
    return f'({x.numerator} / {x.denominator} : ℚ)'


def _f(F):
    return '(' + ', '.join(_i(v) for v in F) + ')'


def lean(ks):
    r = json.loads((ROOT / 'receipts' / 'positive_k.json').read_text())
    rows = {row['k']: row for row in r['curves']}
    out = ['import PerfectPower.ClassListProof\nimport PerfectPower.Generated.PositiveKComplete\n\n/-!\n'
           '# The class-list premise, proved (generated by `python/class_list_cert.py`)\n\n'
           'For each `k`, `ClassListProof.classList_of` proves `ClassList k Gs` for the classes of\n'
           '`Generated/PositiveKComplete.lean`.  The parameters are checked by `norm_num`, and the\n'
           'transport certificates for every form of the box by the kernel (`boxCertB`).  With them, the\n'
           'complete point lists of `PositiveKComplete` hold with no premise.\n-/\n\n'
           'namespace PerfectPower.Generated.ClassLists\n\n'
           'open PerfectPower MordellCubicForm ClassListProof Generated.PositiveKComplete\n']
    receipt = []
    for k in ks:
        Gs = [(c['form'][0], c['form'][1] // 3, c['form'][2] // 3, c['form'][3]) for c in rows[k]['class_detail']]
        P, certs = build(k, Gs)
        receipt.append({'k': k, 'amax': P['amax'], 'bmax': P['bmax'], 'box_forms': len(certs),
                        'params': {x: str(P[x]) for x in ('s0', 's1', 'H', 'M', 'amax_r')}})
        pts = rows[k]['census_points']
        L = '[' + ', '.join(f'({_i(x)}, {_i(y)})' for x, y in pts) + ']'
        items = [f'({_f(F)}, {_f(G)}, {_i(p)}, {_i(q)}, {_i(r)}, {_i(s)})' for F, G, p, q, r, s in certs]
        chunks = [items[i:i + 16] for i in range(0, len(items), 16)] or [[]]
        chunk_defs = ''.join(f"def certs{k}_{j} : List Cert := [{', '.join(ch)}]\n" for j, ch in enumerate(chunks))
        cl = ' ++ '.join(f'certs{k}_{j}' for j in range(len(chunks)))
        out.append(
            f"/-- Parameters for `k = {k}` (`|D| = {108 * k}`). -/\n"
            f"def P{k} : Params := ⟨{_q(P['s0'])}, {_q(P['s1'])}, {_q(P['H'])}, {_q(P['M'])}, {_q(P['amax_r'])}⟩\n\n"
            f"theorem P{k}_ok : ParamsOK {k} P{k} := by\n  simp only [ParamsOK, P{k}]; norm_num\n\n"
            f"{chunk_defs}\n"
            f"/-- The {len(certs)} forms of the box (`|a| ≤ {P['amax']}`, `|b|, |c| ≤ {P['bmax']}`) with their transports. -/\n"
            f"def certs{k} : List Cert := {cl}\n\n"
            f"set_option maxRecDepth 100000 in\n"
            f"set_option maxHeartbeats 4000000 in\n"
            f"theorem box{k} : boxCertB {k} {P['amax']} {P['bmax']} (cs_{k}.map Prod.fst) certs{k} = true := by\n"
            f"  decide +kernel\n\n"
            f"/-- **`ClassList {k}`, proved.** -/\n"
            f"theorem classList{k} : ClassList {k} (cs_{k}.map Prod.fst) :=\n"
            f"  classList_of (by norm_num) P{k}_ok (by simp only [P{k}]; norm_num) (by simp only [P{k}]; norm_num)\n"
            f"    (by simp only [P{k}]; norm_num) (by norm_num) (by norm_num) box{k}\n\n"
            f"/-- **`y² = x³ + {k}`: the integral points are exactly {L}** (no premise). -/\n"
            f"theorem plus{k} (x y : ℤ) : y ^ 2 = x ^ 3 + {k} ↔ (x, y) ∈ ({L} : List (ℤ × ℤ)) :=\n"
            f"  plus{k}_complete classList{k} x y\n")
    out.append('end PerfectPower.Generated.ClassLists\n')
    (ROOT / 'PerfectPower' / 'Generated' / 'ClassLists.lean').write_text('\n'.join(out))
    (ROOT / 'receipts' / 'class_lists.json').write_text(json.dumps(
        {'label': 'Box parameters and transport certificates for ClassListProof.classList_of', 'curves': receipt},
        indent=1) + '\n')
    return receipt


if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1:]] or json.loads(
        (ROOT / 'receipts' / 'positive_k.json').read_text())['summary']['complete_without_matveev']
    for row in lean(ks):
        print(row['k'], row['amax'], row['bmax'], row['box_forms'])
