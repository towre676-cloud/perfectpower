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


HEAD = ('import PerfectPower.ClassListProof\nimport PerfectPower.Generated.PositiveKComplete\n\n/-!\n'
        '# The class-list premise for `k = {k}`, proved (generated by `python/class_list_cert.py`)\n\n'
        '`ClassListProof.classList_of` proves `ClassList {k} Gs` for the classes of\n'
        '`Generated/PositiveKComplete.lean`: the parameters are checked by `norm_num`, and the transport\n'
        'certificates for every form of the box by the kernel (`boxCertB`).  With it, the complete point\n'
        'list of `PositiveKComplete.plus{k}_complete` holds with no premise.\n-/\n\n'
        'set_option Elab.async false\n\nnamespace PerfectPower.Generated.ClassLists.K{k}\n\n'
        'open PerfectPower MordellCubicForm ClassListProof Generated.PositiveKComplete\n')


def lean_one(k, row):
    Gs = [(c['form'][0], c['form'][1] // 3, c['form'][2] // 3, c['form'][3]) for c in row['class_detail']]
    P, certs = build(k, Gs)
    pts = row['census_points']
    L = '[' + ', '.join(f'({_i(x)}, {_i(y)})' for x, y in pts) + ']'
    items = [f'({_f(F)}, {_f(G)}, {_i(p)}, {_i(q)}, {_i(r)}, {_i(s)})' for F, G, p, q, r, s in certs]
    chunks = [items[i:i + 16] for i in range(0, len(items), 16)] or [[]]
    chunk_defs = ''.join(f"def certs_{j} : List Cert := [{', '.join(ch)}]\n" for j, ch in enumerate(chunks))
    cl = ' ++ '.join(f'certs_{j}' for j in range(len(chunks)))
    text = (HEAD.format(k=k) +
            f"/-- Parameters for `|D| = {108 * k}`. -/\n"
            f"def P : Params := ⟨{_q(P['s0'])}, {_q(P['s1'])}, {_q(P['H'])}, {_q(P['M'])}, {_q(P['amax_r'])}⟩\n\n"
            f"theorem P_ok : ParamsOK {k} P := by\n  simp only [ParamsOK, P]; norm_num\n\n"
            f"{chunk_defs}\n"
            f"/-- The {len(certs)} forms of the box (`|a| ≤ {P['amax']}`, `|b|, |c| ≤ {P['bmax']}`) with their transports. -/\n"
            f"def certs : List Cert := {cl}\n\n"
            + ''.join(f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
                      f"theorem slice_{i} : boxSliceB {k} {P['amax']} {P['bmax']} (cs_{k}.map Prod.fst) certs {i} = true := "
                      f"by decide +kernel\n" for i in range(2 * P['amax'] + 1)) +
            f"\ntheorem box : boxCertB {k} {P['amax']} {P['bmax']} (cs_{k}.map Prod.fst) certs = true :=\n"
            f"  boxCertB_of_slices fun i hi => by\n    simp only [show (2 * ({P['amax']} : ℤ) + 1).toNat = {2 * P['amax'] + 1} by rfl] at hi\n"
            f"    interval_cases i\n    exacts [{', '.join(f'slice_{i}' for i in range(2 * P['amax'] + 1))}]\n\n"
            f"/-- **`ClassList {k}`, proved.** -/\n"
            f"theorem classList : ClassList {k} (cs_{k}.map Prod.fst) :=\n"
            f"  classList_of (by norm_num) P_ok (by simp only [P]; norm_num) (by simp only [P]; norm_num)\n"
            f"    (by simp only [P]; norm_num) (by norm_num) (by norm_num) box\n\n"
            f"/-- **`y² = x³ + {k}`: the integral points are exactly {L}**, with no premise. -/\n"
            f"theorem plus{k} (x y : ℤ) : y ^ 2 = x ^ 3 + {k} ↔ (x, y) ∈ ({L} : List (ℤ × ℤ)) :=\n"
            f"  plus{k}_complete classList x y\n\n"
            f"end PerfectPower.Generated.ClassLists.K{k}\n")
    d = ROOT / 'PerfectPower' / 'Generated' / 'ClassLists'
    d.mkdir(exist_ok=True)
    (d / f'K{k}.lean').write_text(text)
    return {'k': k, 'amax': P['amax'], 'bmax': P['bmax'], 'box_forms': len(certs), 'points': pts,
            'params': {x: str(P[x]) for x in ('s0', 's1', 'H', 'M', 'amax_r')}}


def lean(ks):
    r = json.loads((ROOT / 'receipts' / 'positive_k.json').read_text())
    rows = {row['k']: row for row in r['curves']}
    receipt = [lean_one(k, rows[k]) for k in ks]
    (ROOT / 'receipts' / 'class_lists.json').write_text(json.dumps(
        {'label': 'Box parameters and transport certificates for ClassListProof.classList_of '
                  '(Lean: Generated/ClassLists/K*.lean)', 'curves': receipt}, indent=1) + '\n')
    return receipt


K2_HEAD = """import PerfectPower.ClassListProof
import PerfectPower.PositiveKCurve
import PerfectPower.Plus2

/-!
# `y² = x³ + 2`: the first curve with an irreducible positive-`k` source, with no premise
(generated by `python/class_list_cert.py k2`)

The two classes for `k = 2` (`positive_k.json`):
* `(−1, 0, −1, −2)`, i.e. `−u³ − 3uv² − 2v³ = 1`, is irreducible; its only solution `(−1, 0)` is
  `Plus2.source` (unit generation in `ℤ[z]`, `z³ + 3z + 2 = 0`, and the 3-adic zero set).
* `(0, −1, 0, −2)` is impossible modulo 9.

The class-list premise is proved by `ClassListProof.classList_of` (parameters by `norm_num`,
transports by the kernel), and `PositiveKCurve.complete_of_sols` reads off the points.
-/

set_option Elab.async false

namespace PerfectPower.Generated.ClassLists.K2

open PerfectPower MordellCubicForm ClassListProof PositiveKCurve

/-- The 2 classes for `k = 2` with their solution lists. -/
def cs_2 : List ((ℤ × ℤ × ℤ × ℤ) × List (ℤ × ℤ)) := [(((-1), 0, (-1), (-2)), [((-1), 0)]), ((0, (-1), 0, (-2)), [])]

/-- **The irreducible source**: `Plus2.source`. -/
theorem sols_irr : SolsIn ((-1), 0, (-1), (-2)) [((-1), 0)] := by
  intro u v h
  have h' : -u ^ 3 - 3 * u * v ^ 2 - 2 * v ^ 3 = 1 := by
    simp only [ev] at h; linear_combination h
  obtain ⟨rfl, rfl⟩ := (Plus2.source u v).mp h'
  simp

theorem sols_2 : ∀ c ∈ cs_2, SolsIn c.1 c.2 := by
  intro c hc
  simp only [cs_2, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  exacts [sols_irr, solsIn_of_loc (m := 9) (by norm_num) (by decide +kernel)]

"""


def lean_k2():
    """`Generated/ClassLists/K2.lean`: the class list for `k = 2` and the curve theorem."""
    k = 2
    Gs = [(-1, 0, -1, -2), (0, -1, 0, -2)]
    P, certs = build(k, Gs)
    items = [f'({_f(F)}, {_f(G)}, {_i(p)}, {_i(q)}, {_i(r)}, {_i(s)})' for F, G, p, q, r, s in certs]
    chunks = [items[i:i + 16] for i in range(0, len(items), 16)] or [[]]
    chunk_defs = ''.join(f"def certs_{j} : List Cert := [{', '.join(ch)}]\n" for j, ch in enumerate(chunks))
    cl = ' ++ '.join(f'certs_{j}' for j in range(len(chunks)))
    n = 2 * P['amax'] + 1
    text = (K2_HEAD +
            f"/-- Parameters for `|D| = {108 * k}`. -/\n"
            f"def P : Params := ⟨{_q(P['s0'])}, {_q(P['s1'])}, {_q(P['H'])}, {_q(P['M'])}, {_q(P['amax_r'])}⟩\n\n"
            f"theorem P_ok : ParamsOK {k} P := by\n  simp only [ParamsOK, P]; norm_num\n\n"
            f"{chunk_defs}\n"
            f"/-- The {len(certs)} forms of the box (`|a| ≤ {P['amax']}`, `|b|, |c| ≤ {P['bmax']}`) with their transports. -/\n"
            f"def certs : List Cert := {cl}\n\n"
            + ''.join(f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
                      f"theorem slice_{i} : boxSliceB {k} {P['amax']} {P['bmax']} (cs_{k}.map Prod.fst) certs {i} = true := "
                      f"by decide +kernel\n" for i in range(n)) +
            f"\ntheorem box : boxCertB {k} {P['amax']} {P['bmax']} (cs_{k}.map Prod.fst) certs = true :=\n"
            f"  boxCertB_of_slices fun i hi => by\n    simp only [show (2 * ({P['amax']} : ℤ) + 1).toNat = {n} by rfl] at hi\n"
            f"    interval_cases i\n    exacts [{', '.join(f'slice_{i}' for i in range(n))}]\n\n"
            f"/-- **`ClassList 2`, proved.** -/\n"
            f"theorem classList : ClassList {k} (cs_{k}.map Prod.fst) :=\n"
            f"  classList_of (by norm_num) P_ok (by simp only [P]; norm_num) (by simp only [P]; norm_num)\n"
            f"    (by simp only [P]; norm_num) (by norm_num) (by norm_num) box\n\n"
            f"/-- **`y² = x³ + 2`: the integral points are exactly `(−1, ±1)`**, with no premise. -/\n"
            f"theorem plus2 (x y : ℤ) : y ^ 2 = x ^ 3 + 2 ↔ (x, y) ∈ ([((-1), (-1)), ((-1), 1)] : List (ℤ × ℤ)) :=\n"
            f"  complete_of_sols classList sols_2 (by decide +kernel) x y\n\n"
            f"end PerfectPower.Generated.ClassLists.K2\n")
    (ROOT / 'PerfectPower' / 'Generated' / 'ClassLists' / 'K2.lean').write_text(text)
    return {'k': k, 'amax': P['amax'], 'bmax': P['bmax'], 'box_forms': len(certs)}


R1_HEAD = """import PerfectPower.ClassListProof
import PerfectPower.PositiveKCurve
{imports}

/-!
# `y² = x³ + {k}` through irreducible rank-one sources, with no premise
(generated by `python/class_list_cert.py rank1`)

The classes for `k = {k}` (`positive_k.json`):
{bullets}

The class-list premise is proved by `ClassListProof.classList_of` (parameters by `norm_num`,
transports by the kernel), and `PositiveKCurve.complete_of_sols` reads off the points.
-/

set_option Elab.async false

namespace PerfectPower.Generated.ClassLists.K{k}

open PerfectPower MordellCubicForm ClassListProof PositiveKCurve ReducibleThue

"""


def plus_root(k, L, Gs, sols_py):
    """The curve theorem through `PositiveKCurveRoot.complete_of_sols_root` (supplied square roots)."""
    if any(S is None for S in sols_py):
        raise ValueError(f'k = {k}: reducible classes with large points are not supported here')
    X = sorted({(G[1] ** 2 - G[0] * G[2]) * u * u + (G[1] * G[2] - G[0] * G[3]) * u * v + (G[2] ** 2 - G[1] * G[3]) * v * v
                for G, S in zip(Gs, sols_py) for u, v in S})
    XS = [(x, math.isqrt(max(x ** 3 + k, 0))) for x in X]
    xs = '[' + ', '.join(f'({_i(x)}, {_i(r)})' for x, r in XS) + ']'
    return (f"/-- **`y² = x³ + {k}`: the integral points are exactly {L}**, with no premise "
            f"(square roots supplied, `PositiveKCurveRoot`). -/\n"
            f"theorem plus{k} (x y : ℤ) : y ^ 2 = x ^ 3 + {k} ↔ (x, y) ∈ ({L} : List (ℤ × ℤ)) :=\n"
            f"  PositiveKCurveRoot.complete_of_sols_root (XS := {xs}) classList sols_{k} (by decide +kernel) x y\n\n")


# Curves whose box slices exhaust memory in one Lean process: the slices go to separate modules.
SPLIT = {97}
SLICES_PER_FILE = 4


def write_split(k, text):
    """Write `K{k}Data.lean` (classes, sources, parameters, certificates), `K{k}S{j}.lean` (a few box
    slices each) and `K{k}.lean` (box, class list, curve theorem), so each Lean process stays small."""
    d = ROOT / 'PerfectPower' / 'Generated' / 'ClassLists'
    ns = f'namespace PerfectPower.Generated.ClassLists.K{k}'
    i0 = text.index(ns)
    head_imports, rest = text[:i0], text[i0:]
    preamble = rest[:rest.index('\n\n', rest.index('open ')) + 2]   # namespace + open line
    body = rest[len(preamble):]
    mark = 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ntheorem slice_'
    a = body.index(mark)
    b = body.index('\ntheorem box')
    data, slices, tail = body[:a], body[a:b], body[b:]
    parts = [mark + x for x in slices.split(mark) if x]
    end = f'\nend PerfectPower.Generated.ClassLists.K{k}\n'
    tail = tail.replace(end, '')
    (d / f'K{k}Data.lean').write_text(head_imports.replace('# `y²', '# Data for `y²', 1) + preamble + data + end)
    groups = [parts[i:i + SLICES_PER_FILE] for i in range(0, len(parts), SLICES_PER_FILE)]
    for j, g in enumerate(groups):
        (d / f'K{k}S{j}.lean').write_text(
            f'import PerfectPower.Generated.ClassLists.K{k}Data\n\n/-! Box slices for `k = {k}` (part {j}). -/\n\n'
            'set_option Elab.async false\n\n' + preamble + ''.join(g) + end)
    (d / f'K{k}.lean').write_text(
        ''.join(f'import PerfectPower.Generated.ClassLists.K{k}S{j}\n' for j in range(len(groups))) +
        f'\n/-! The box, the class list and the curve theorem for `k = {k}` (data in `K{k}Data`). -/\n\n'
        'set_option Elab.async false\n\n' + preamble + tail.lstrip('\n') + end)


def lean_rank1(k, srcs, zsrcs=None, nsrcs=None):
    """`Generated/ClassLists/K{k}.lean` for a curve whose irreducible classes are all monic sources
    `F(u, v) = −N((u + hv) − vz)` certified in `RankOneSources.K{k}`; the other classes must be
    locally impossible or reducible."""
    row = next(r for r in json.loads((ROOT / 'receipts' / 'positive_k.json').read_text())['curves'] if r['k'] == k)
    src = {tuple(F): (i, P, Q, h, U) for i, (F, P, Q, h, U) in enumerate(srcs)}
    zsrc = {tuple(F): (i, P, Q, h, L) for i, (F, P, Q, h, L) in enumerate(zsrcs or [])}
    Gs, sols, proofs, bullets, irr, zirr, nirr = [], [], [], [], [], [], []
    for c in row['class_detail']:
        a, B, C, d = c['form']
        G = (a, B // 3, C // 3, d)
        Gs.append(G)
        if c['local_obstruction']:
            sols.append('[]')
            proofs.append(f"solsIn_of_loc (m := {c['local_obstruction']}) (by norm_num) (by decide +kernel)")
            bullets.append(f"* `({a}, {B}, {C}, {d})` is impossible modulo {c['local_obstruction']}.")
        elif c['reducible']:
            p_, q_, A_, B_, C_, h_, j_ = c['reducible']
            cert = f"⟨{_i(p_)}, {_i(q_)}, {_i(A_)}, {_i(B_)}, {_i(C_)}, {_i(h_)}, {_i(j_)}⟩"
            sols.append(f'redSols {cert}')
            proofs.append(f"solsIn_of_red (c := {cert}) (by decide +kernel)")
            bullets.append(f"* `({a}, {B}, {C}, {d})` is reducible, solved by `ReducibleThue` (factor, Bezout pair, "
                           f"integer square root).")
        elif (a, B, C, d) in (nsrcs or {}):
            assert c['representations'] == [], (k, c)
            sols.append('[]')
            proofs.append('sols_empty')
            nirr.append(G)
            bullets.append(f"* `({a}, {B}, {C}, {d})` is irreducible and nonmonic with no solution: its monic reduction gives "
                           f"an element of norm `a²` with `z²` coordinate `0`, which `RankOneNorm.K{k}.empty` excludes "
                           f"(norm representatives, unit generation and an orbit congruence).")
        elif (a, B, C, d) in zsrc:
            i, P, Q, h, Ls = zsrc[(a, B, C, d)]
            Lo = [(u - h * v, v) for u, v in Ls]
            assert sorted(map(tuple, c['representations'])) == sorted(Lo), (k, c)
            sols.append('[' + ', '.join(f'({_i(u)}, {_i(v)})' for u, v in Lo) + ']')
            proofs.append(f'sols_zirr{i}')
            zirr.append((i, G, P, Q, h, Ls, Lo))
            bullets.append(f"* `({a}, {B}, {C}, {d})` is irreducible with {len(Lo)} solutions: `F(u, v) = −N((u + {h}v) − vz)`, "
                           f"`z³ = ({P}) z + ({Q})`; the list comes from `RankOneZeros.K{k}.source{i}` (unit generation, "
                           f"and a finite zero set by recentred Skolem classes and auxiliary primes).")
        else:
            i, P, Q, h, U = src[(a, B, C, d)]
            proofs.append(f'sols_irr{i}')
            irr.append((i, G, P, Q, h, U))
            if U is None:
                assert c['representations'] == [[-1, 0]], (k, c)
                sols.append('[((-1), 0)]')
                bullets.append(f"* `({a}, {B}, {C}, {d})` is irreducible: `F(u, v) = −N((u + {h}v) − vz)` in `ℤ[z]`, "
                               f"`z³ = ({P}) z + ({Q})`. Its only solution `(−1, 0)` comes from "
                               f"`RankOneSources.K{k}.source{i}` (unit generation and the Skolem zero set).")
            else:
                (al, be), (ga, de) = U
                assert c['representations'] == [[-al, -ga]], (k, c)
                sols.append(f'[({_i(-al)}, {_i(-ga)})]')
                bullets.append(f"* `({a}, {B}, {C}, {d})` is irreducible and nonmonic. Its recorded point `({-al}, {-ga})` "
                               f"gives `U = ({al} {be}; {ga} {de})`, `det U = 1`, with `F ∘ U = −u³ + ({P}) u v² + ({Q}) v³` "
                               f"(witness normalization); `RankOneSources.K{k}.source{i}` proves that form has only "
                               f"`(−1, 0)`, so `F` has only `({-al}, {-ga})`.")
    assert len(irr) == len(srcs)
    cs = ', '.join(f'({_f(G)}, {S})' for G, S in zip(Gs, sols))
    P_, certs = build(k, Gs)
    pts = row['census_points']
    L = '[' + ', '.join(f'({_i(x)}, {_i(y)})' for x, y in pts) + ']'
    items = [f'({_f(F)}, {_f(G)}, {_i(p)}, {_i(q)}, {_i(r)}, {_i(s)})' for F, G, p, q, r, s in certs]
    chunks = [items[i:i + 16] for i in range(0, len(items), 16)] or [[]]
    chunk_defs = ''.join(f"def certs_{j} : List Cert := [{', '.join(ch)}]\n" for j, ch in enumerate(chunks))
    cl = ' ++ '.join(f'certs_{j}' for j in range(len(chunks)))
    n = 2 * P_['amax'] + 1
    def wit_thm(i, G, P, Q, U):
        (al, be), (ga, de) = U
        u, v = f'({_i(de)} * x - {_i(be)} * y)', f'({_i(-ga)} * x + {_i(al)} * y)'
        return (f"/-- **Irreducible source {i}** (witness normalization): `RankOneSources.K{k}.source{i}` at `U⁻¹(x, y)`. -/\n"
                f"theorem sols_irr{i} : SolsIn {_f(G)} [({_i(-al)}, {_i(-ga)})] := by\n"
                f"  intro x y h\n"
                f"  have h' : -{u} ^ 3 + {_i(P)} * {u} * {v} ^ 2 + {_i(Q)} * {v} ^ 3 = 1 := by\n"
                f"    simp only [ev] at h; linear_combination h\n"
                f"  obtain ⟨h1, h2⟩ := (Generated.RankOneSources.K{k}.source{i} _ _).mp h'\n"
                f"  obtain rfl : x = {_i(-al)} := by linear_combination {_i(al)} * h1 + {_i(be)} * h2\n"
                f"  obtain rfl : y = {_i(-ga)} := by linear_combination {_i(ga)} * h1 + {_i(de)} * h2\n"
                f"  simp\n\n")

    def z_thm(i, G, P, Q, h, Ls, Lo):
        Lt = '[' + ', '.join(f'({_i(u)}, {_i(v)})' for u, v in Lo) + ']'
        branches = ''.join(f"  · obtain rfl : u = {_i(uo)} := by linarith\n    simp\n" for (us, vs), (uo, vo) in zip(Ls, Lo))
        pat = ' | '.join(['⟨h1, rfl⟩'] * len(Ls))
        return (f"/-- **Irreducible source {i}** (several solutions): `RankOneZeros.K{k}.source{i}` at `u + {h}v`. -/\n"
                f"theorem sols_zirr{i} : SolsIn {_f(G)} {Lt} := by\n"
                f"  intro u v h\n"
                f"  have h' : -(u + {h} * v) ^ 3 + {_i(P)} * (u + {h} * v) * v ^ 2 + {_i(Q)} * v ^ 3 = 1 := by\n"
                f"    simp only [ev] at h; linear_combination h\n"
                f"  have hm := (Generated.RankOneZeros.K{k}.source{i} (u + {h} * v) v).mp h'\n"
                f"  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm\n"
                f"  rcases hm with {pat}\n" + branches + "\n")

    irr_thms = ''.join(
        f"/-- **The empty nonmonic source**: `RankOneNorm.K{k}.empty`. -/\n"
        f"theorem sols_empty : SolsIn {_f(G)} [] := by\n"
        f"  intro u v h\n"
        f"  exfalso\n"
        f"  exact Generated.RankOneNorm.K{k}.empty u v (by simp only [ev] at h; linear_combination h)\n\n"
        for G in nirr) + ''.join(z_thm(*z) for z in zirr) + ''.join(wit_thm(i, G, P, Q, U) for i, G, P, Q, h, U in irr if U is not None) + ''.join(
        f"/-- **Irreducible source {i}**: `RankOneSources.K{k}.source{i}` at `u + {h}v`. -/\n"
        f"theorem sols_irr{i} : SolsIn {_f(G)} [((-1), 0)] := by\n"
        f"  intro u v h\n"
        f"  have h' : -(u + {h} * v) ^ 3 + {_i(P)} * (u + {h} * v) * v ^ 2 + {_i(Q)} * v ^ 3 = 1 := by\n"
        f"    simp only [ev] at h; linear_combination h\n"
        f"  obtain ⟨h1, rfl⟩ := (Generated.RankOneSources.K{k}.source{i} (u + {h} * v) v).mp h'\n"
        f"  obtain rfl : u = -1 := by linarith\n"
        f"  simp\n\n" for i, G, P, Q, h, U in irr if U is None)
    # large points: the kernel's `Int.sqrt` overflows, so supply the roots (`PositiveKCurveRoot`)
    big = max([abs(y) for _, y in pts] or [0]) > 100
    sols_py = []
    for c in row['class_detail']:
        if c['local_obstruction']:
            sols_py.append([])
        else:
            sols_py.append([tuple(x) for x in c['representations']])
    imports = '\n'.join(([f'import PerfectPower.Generated.RankOneSources.K{k}'] if srcs else []) +
                        ([f'import PerfectPower.Generated.RankOneZeros.K{k}'] if zsrcs else []) +
                        ([f'import PerfectPower.Generated.RankOneNorm.K{k}'] if nsrcs else []) +
                        (['import PerfectPower.PositiveKCurveRoot'] if big else []))
    text = (R1_HEAD.replace('{imports}', imports).replace('{k}', str(k)).replace('{bullets}', '\n'.join(bullets)) +
            f"/-- The {len(Gs)} classes for `k = {k}` with their solution lists. -/\n"
            f"def cs_{k} : List ((ℤ × ℤ × ℤ × ℤ) × List (ℤ × ℤ)) := [{cs}]\n\n"
            + irr_thms +
            f"theorem sols_{k} : ∀ c ∈ cs_{k}, SolsIn c.1 c.2 := by\n"
            f"  intro c hc\n"
            f"  simp only [cs_{k}, List.mem_cons, List.not_mem_nil, or_false] at hc\n"
            f"  rcases hc with {' | '.join(['rfl'] * len(Gs))}\n"
            f"  exacts [{', '.join(proofs)}]\n\n"
            f"/-- Parameters for `|D| = {108 * k}`. -/\n"
            f"def P : Params := ⟨{_q(P_['s0'])}, {_q(P_['s1'])}, {_q(P_['H'])}, {_q(P_['M'])}, {_q(P_['amax_r'])}⟩\n\n"
            f"theorem P_ok : ParamsOK {k} P := by\n  simp only [ParamsOK, P]; norm_num\n\n"
            f"{chunk_defs}\n"
            f"/-- The {len(certs)} forms of the box (`|a| ≤ {P_['amax']}`, `|b|, |c| ≤ {P_['bmax']}`) with their transports. -/\n"
            f"def certs : List Cert := {cl}\n\n"
            + ''.join(f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
                      f"theorem slice_{i} : boxSliceB {k} {P_['amax']} {P_['bmax']} (cs_{k}.map Prod.fst) certs {i} = true := "
                      f"by decide +kernel\n" for i in range(n)) +
            f"\ntheorem box : boxCertB {k} {P_['amax']} {P_['bmax']} (cs_{k}.map Prod.fst) certs = true :=\n"
            f"  boxCertB_of_slices fun i hi => by\n    simp only [show (2 * ({P_['amax']} : ℤ) + 1).toNat = {n} by rfl] at hi\n"
            f"    interval_cases i\n    exacts [{', '.join(f'slice_{i}' for i in range(n))}]\n\n"
            f"/-- **`ClassList {k}`, proved.** -/\n"
            f"theorem classList : ClassList {k} (cs_{k}.map Prod.fst) :=\n"
            f"  classList_of (by norm_num) P_ok (by simp only [P]; norm_num) (by simp only [P]; norm_num)\n"
            f"    (by simp only [P]; norm_num) (by norm_num) (by norm_num) box\n\n"
            + (plus_root(k, L, Gs, sols_py) if big else
            f"/-- **`y² = x³ + {k}`: the integral points are exactly {L}**, with no premise. -/\n"
            f"theorem plus{k} (x y : ℤ) : y ^ 2 = x ^ 3 + {k} ↔ (x, y) ∈ ({L} : List (ℤ × ℤ)) :=\n"
            f"  complete_of_sols classList sols_{k} (by decide +kernel) x y\n\n") +
            f"end PerfectPower.Generated.ClassLists.K{k}\n")
    write_split(k, text) if k in SPLIT else (ROOT / 'PerfectPower' / 'Generated' / 'ClassLists' / f'K{k}.lean').write_text(text)
    return {'k': k, 'amax': P_['amax'], 'bmax': P_['bmax'], 'box_forms': len(certs), 'points': pts,
            'sources': len(srcs)}




if __name__ == '__main__':
    if sys.argv[1:2] == ['rank1']:
        ks = [int(a) for a in sys.argv[2:]]
        import rank_one_sources as R1
        by_k = {}
        for k, F, P, Q, h, _, *U in R1.TARGETS:
            by_k.setdefault(k, []).append((F, P, Q, h, U[0] if U else None))
        zby = {}
        for r in json.loads((ROOT / 'receipts' / 'rank_one_zeros.json').read_text())['sources']:
            if r['status'] == 'ok':
                zby.setdefault(r['k'], []).append((tuple(r['form']), r['P'], r['Q'], r['h'], r['solutions_shifted']))
        nby = {}
        f = ROOT / 'receipts' / 'rank_one_norm.json'
        if f.exists():
            for r in json.loads(f.read_text())['sources']:
                if r['status'] == 'empty':
                    nby.setdefault(r['k'], set()).add(tuple(r['form']))
        for k in sorted(set(by_k) | set(zby) | set(nby)):
            if (not ks and k in by_k) or k in ks:
                print(lean_rank1(k, by_k.get(k, []), zby.get(k), nby.get(k)))
        sys.exit(0)
    if sys.argv[1:] == ['k2']:
        print(lean_k2())
        sys.exit(0)
    ks = [int(a) for a in sys.argv[1:]] or json.loads(
        (ROOT / 'receipts' / 'positive_k.json').read_text())['summary']['complete_without_matveev']
    for row in lean(ks):
        print(row['k'], row['amax'], row['bmax'], row['box_forms'])
