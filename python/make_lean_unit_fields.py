"""Generate the unit-field certificates: `PerfectPower/Generated/Field756.lean` (the seven Thue
classes of the field of discriminant 756 and the curves `y^2 = x^3 - D`, `D = 7, 28, 63`) and
`PerfectPower/Generated/D72Unit.lean` (the `D = 72` residual `H(u, v) = ±1`).

Every theorem is stated under **three named premises** (`UnitPremises`):
- `unitGen` (one per field): the units are `±ε1^a ε2^b`;
- `normRep_i` (one per norm target): every element of norm `c0^2 M` is `γ0 · unit`;
- `analytic_i` (one per class): Siegel + Matveev, as rational enclosures and a first bound.
From these, the kernel checks the direct-`H` reduction chains (`DirectReduction.chainCheck`), the
norm identity, the exponent box, the small-`b` search and, for curves, the branch transport.

Inputs: `receipts/field756_bound.json`, `receipts/d72_thue_bound.json` (`crosscheck/thue_bound*.py`),
`receipts/unit_basis_witness.json`, `receipts/norm_rep_localization.json`, `receipts/thue_graph.json`.
Before emitting, this script replays in exact arithmetic: every reduction chain
(`perfectpower.reduction_check`), the unit inverses, the box (hits equal PARI's lists: a positive
control), the small-`b` search, and the curve points against the Sage census.

Run: python3 python/make_lean_unit_fields.py
Writes the two Lean files and receipts/unit_fields_certificate.json.
"""
from __future__ import annotations

import csv
import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower import reduction_check as RC  # noqa: E402
from perfectpower.branch_descent import compile_curve, lean_args  # noqa: E402
from perfectpower.descent import W1, W2  # noqa: E402


def _i(x):
    return f'({x})' if x < 0 else str(x)


def z3_lean(t):
    return '(' + ', '.join(_i(v) for v in t) + ')'


def form_lean(F):
    return '(' + ', '.join(_i(c) for c in F) + ')'


def mat_lean(T):
    return f'(({_i(T[0][0])}, {_i(T[0][1])}), ({_i(T[1][0])}, {_i(T[1][1])}))'


def pairs_lean(L):
    return '[' + ', '.join(f'({_i(a)}, {_i(b)})' for a, b in L) + ']'


def mul(P, Q, x, y):
    a, b, c = x
    d, e, f = y
    c0, c1, c2, c3, c4 = a * d, a * e + b * d, a * f + b * e + c * d, b * f + c * e, c * f
    return (c0 + Q * c3, c1 + P * c3 + Q * c4, c2 + P * c4)


def inverse(P, Q, u):
    """Inverse of a unit by solving the 3x3 multiplication matrix exactly."""
    from fractions import Fraction
    cols = [mul(P, Q, u, e) for e in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]
    A = [[Fraction(cols[j][i]) for j in range(3)] + [Fraction(int(i == 0))] for i in range(3)]
    for c in range(3):
        r = next(r for r in range(c, 3) if A[r][c] != 0)
        A[c], A[r] = A[r], A[c]
        A[c] = [x / A[c][c] for x in A[c]]
        for r in range(3):
            if r != c:
                A[r] = [x - A[r][c] * y for x, y in zip(A[r], A[c])]
    inv = tuple(A[i][3] for i in range(3))
    assert all(x.denominator == 1 for x in inv)
    inv = tuple(int(x) for x in inv)
    assert mul(P, Q, u, inv) == (1, 0, 0)
    return inv


def pw(P, Q, x, n):
    r = (1, 0, 0)
    for _ in range(n):
        r = mul(P, Q, r, x)
    return r


def fam(P, Q, g0, e1, e1i, e2, e2i, B):
    def zp(x, xi, i):
        return pw(P, Q, x, i - B) if i >= B else pw(P, Q, xi, B - i)
    return [mul(P, Q, mul(P, Q, g0, zp(e1, e1i, i)), zp(e2, e2i, j))
            for i in range(2 * B + 1) for j in range(2 * B + 1)]


def enc(c0, phi, a, b):
    return (c0 * a - b * phi[0], -(b * phi[1]), -(b * phi[2]))


def _tdiv(x, y):          # Lean `Int.ediv` (Euclidean), as `/` on ℤ
    q = x // y
    if (x - q * y) < 0:
        q += 1 if y < 0 else -1
    return q


def dec(c0, phi, g):
    b = -_tdiv(g[1], phi[1]) if phi[2] == 0 else -_tdiv(g[2], phi[2])
    return (_tdiv(g[0] + b * phi[0], c0), b)


def evalF(F, a, b):
    c0, c1, c2, c3 = F
    return c0 * a ** 3 + c1 * a * a * b + c2 * a * b * b + c3 * b ** 3


def small_hits(F, M, V):
    out = []
    for b in range(-V, V + 1):
        S = abs(F[1] * b) + abs(F[2] * b * b) + abs(F[3] * b ** 3 - M) + 1
        for a in range(-S, S + 1):
            if evalF(F, a, b) == M:
                out.append((a, b))
    return out


def icbrt(n):
    if n < 0:
        return -icbrt(-n)
    x = int(round(n ** (1 / 3)))
    while x ** 3 > n:
        x -= 1
    while (x + 1) ** 3 <= n:
        x += 1
    return x



def nrm(P, Q, g):
    a, b, c = g
    return (a * ((a + P * c) * (a + P * c) - (P * b + Q * c) * b) - Q * c * (b * (a + P * c) - (P * b + Q * c) * c)
            + Q * b * (b * b - (a + P * c) * c))


def q_lean(x: Fraction) -> str:
    return f'(({x.numerator} : ℚ) / {x.denominator})'


def case_lean(c) -> str:
    e = RC.enc_from_json(c['enclosure'])
    steps = '[' + ', '.join(f"({s['q']}, {s['B']}, {s['J']})" for s in c['steps']) + ']'
    return (f"{{ kl := {q_lean(e['kl'])}, ku := {q_lean(e['ku'])},\n      ml := {q_lean(e['ml'])}, mu := {q_lean(e['mu'])},\n"
            f"      cl := {q_lean(e['cl'])}, Au := {q_lean(e['Au'])},\n      M0 := {c['M0']}, steps := {steps} }}")


def check_cases(cases, B):
    for c in cases:
        enc = RC.enc_from_json(c['enclosure'])
        assert RC.chain_ok(enc, c['M0'], c['steps']), 'reduction chain does not replay'
        assert RC.chain_end(c['M0'], c['steps']) == c['H_reduced'] <= B
    return len(cases), sum(len(c['steps']) for c in cases)


def field_preamble(P, Q, e1, e2, witness):
    e1i, e2i = inverse(P, Q, e1), inverse(P, Q, e2)
    w = next(f for f in witness['fields'] if (f['P'], f['Q']) == (P, Q))
    a, b, c = w['coordinate_box']
    cands = [tuple(x['coordinates']) for x in w['candidates']]
    # the finite part replayed here too: every box triple of norm ±1 is a candidate
    for x in range(-a, a + 1):
        for y in range(-b, b + 1):
            for z in range(-c, c + 1):
                if abs(nrm(P, Q, (x, y, z))) == 1:
                    assert (x, y, z) in cands
    for g in cands:
        if g not in ((1, 0, 0), (-1, 0, 0)):
            assert any(x['coordinates'] == list(g) and x['excluded_from_centered_domain'] for x in w['candidates'])
    text = (f'/-- `ε₁`. -/\ndef e1 : Z3 := {z3_lean(e1)}\n/-- `ε₁⁻¹`. -/\ndef e1i : Z3 := {z3_lean(e1i)}\n'
            f'/-- `ε₂`. -/\ndef e2 : Z3 := {z3_lean(e2)}\n/-- `ε₂⁻¹`. -/\ndef e2i : Z3 := {z3_lean(e2i)}\n\n'
            f'theorem e1_inv : mul {P} {Q} e1 e1i = (1, 0, 0) := by decide\n'
            f'theorem e2_inv : mul {P} {Q} e2 e2i = (1, 0, 0) := by decide\n\n'
            f'/-- **The unit-generation premise** for `ℤ[x]`, `x³ = {P}x + {Q}`: every unit is `±ε₁^a ε₂^b`.\n'
            f'Evidence: the exact fundamental-domain witness (`python/unit_basis_witness.py`); its finite part\n'
            f'is `unit_box` below.  Not proved in Lean. -/\n'
            f'def unitGen : Prop := UnitPremises.UnitGen {P} {Q} e1 e1i e2 e2i\n\n'
            f'/-- The finite part of the unit-domain witness: the {(2*a+1)*(2*b+1)*(2*c+1)} triples with '
            f'`|A| ≤ {a}`, `|B| ≤ {b}`, `|C| ≤ {c}` include exactly {len(cands)} of norm `±1`, all listed (and\n'
            f'all but `±1` lie outside the centered parallelogram, by the exact log enclosures of the witness). -/\n'
            f'theorem unit_box : UnitPremises.unitBoxB {P} {Q} {a} {b} {c} '
            f'[{", ".join(z3_lean(g) for g in cands)}] = true := by decide +kernel\n')
    return text, e1i, e2i, {'box': [a, b, c], 'triples': (2*a+1)*(2*b+1)*(2*c+1), 'candidates': len(cands)}


def norm_rep_block(nname, P, Q, N, g0, labels):
    return (f"/-- **Norm-representative premise** (shared by {', '.join(labels)}): every element of norm "
            f"{N} is `{list(g0)}` times a unit.  Evidence: `python/norm_rep_localization.py`.  Not proved in "
            f"Lean. -/\n"
            f"def {nname} : Prop := UnitPremises.NormRep {P} {Q} {_i(N)} [{z3_lean(g0)}]\n\n")


def class_block(name, P, Q, F, M, phi, g0, cases, B, V, L, label, nname, neg_of=None):
    """One class theorem.  With `neg_of`, the class is the negated target of class `neg_of`: its
    representatives and cases are `negReps reps_{neg_of}`, and its premises are transported."""
    assert nrm(P, Q, g0) == F[0] ** 2 * M
    ncases, nsteps = check_cases(cases, B)
    if neg_of is None:
        cs = ',\n    '.join(case_lean(c) for c in cases)
        reps = (f"/-- The analytic cases of {label}: {ncases} cases, {nsteps} reduction steps, final bound {B}. -/\n"
                f"def reps_{name} : List (Z3 × List UnitPremises.Case) :=\n  [({z3_lean(g0)},\n   [{cs}])]\n\n"
                f"/-- **Analytic premise** for {label} (Siegel's identity, the conjugate estimates and Matveev's "
                f"theorem, `crosscheck/thue_bound.py`).  Not proved in Lean. -/\n"
                f"def analytic_{name} : Prop :=\n  UnitPremises.Analytic {form_lean(F)} {_i(M)} {P} {Q} {z3_lean(phi)} "
                f"e1 e1i e2 e2i {V} reps_{name}\n\n")
        reps += (f"/-- Negative control: every chain of {label} with its final bound lowered by one is rejected "
                 f"by the kernel. -/\n"
                 f"theorem forged_rejected_{name} : UnitPremises.forgedRejectedB reps_{name} = true := by decide +kernel\n\n")
        hyps = f"(hU : unitGen) (hN : {nname}) (hA : analytic_{name})"
        hN, hA = 'hN', 'hA'
    else:
        reps = (f"/-- The representatives and cases of {label}: those of `{neg_of}`, negated. -/\n"
                f"def reps_{name} : List (Z3 × List UnitPremises.Case) := UnitPremises.negReps reps_{neg_of}\n\n")
        hyps = f"(hU : unitGen) (hN : {nname}) (hA : analytic_{neg_of})"
        hN = 'UnitPremises.normRep_neg_of (reps := reps_' + neg_of + ') hN'
        hA = 'UnitPremises.analytic_neg_of hA'
    note = '' if neg_of is None else f"  Its norm and analytic premises are those of `{neg_of}`, transported by sign. "
    return (reps +
            f"/-- **{label}, complete under the three premises**: `{list(F)}` takes the value {M} exactly at "
            f"{len(L)} point(s).{note}  Kernel-checked: the reduction chains (to `H ≤ {B}`), the norm identity, "
            f"the box (`{2 * B + 1}²` elements) and the search `|b| ≤ {V}`. -/\n"
            f"theorem class_{name} {hyps} (u v : ℤ) :\n"
            f"    evalF {form_lean(F)} u v = {_i(M)} ↔ (u, v) ∈ ({pairs_lean(L)} : List (ℤ × ℤ)) :=\n"
            f"  thue_list {form_lean(F)} {_i(M)} {P} {Q} {z3_lean(phi)} (reps_{name}.map Prod.fst) e1 e1i e2 e2i {B} {V} "
            f"{pairs_lean(L)}\n    (by decide) (by decide)\n"
            f"    (UnitPremises.extBound_of _ _ _ _ _ _ _ _ _ _ _ reps_{name} hU ({hN})\n"
            f"      (fun a b => by simp only [UnitPremises.nrm, enc, evalF]; ring) ({hA}) (by decide +kernel))\n"
            f"    (by decide +kernel) (by decide +kernel) (by decide +kernel) u v\n")


def box_hits(P, Q, F, M, phi, g0, e1, e1i, e2, e2i, B):
    hits = set()
    for g in fam(P, Q, g0, e1, e1i, e2, e2i, B):
        for h in (g, tuple(-x for x in g)):
            d = dec(F[0], phi, h)
            if enc(F[0], phi, *d) == h and evalF(F, *d) == M:
                hits.add(d)
    return hits


def head(name, doc):
    return (f"import PerfectPower.UnitPremises\nimport PerfectPower.DescentThueList\n\n/-!\n{doc}\n-/\n\n"
            f"namespace PerfectPower.Generated.{name}\n\nopen PerfectPower ThueLocal UnitBox\n\n")


DOC756 = """# The field 756: seven Thue classes and three curves, under three named premises
(generated by `python/make_lean_unit_fields.py`)

`K = ℚ(x)`, `x³ = 6x + 2`, `O_K = ℤ[x]`, discriminant 756.  Seven GL₂(ℤ)-classes of open branch
equations of `y² = x³ − D`, `D ∈ {7, 28, 63}`, live in this field (`MORDELL_BRANCH.md` §7.3).

* **Premises, not proved in Lean:** `unitGen` (one for the field), one `normRep_N` per distinct
  norm representative (classes 20 and 50 share `normRep_64`), and one `analytic_i` per class.  See `UnitPremises` for their statements and evidence.
* **Kernel-checked:** the direct-`H` reduction chains, the exponent boxes, the small-`b` searches,
  the norm identities, and the branch transport.
* `class_i`: the complete solution list.  `minusD`: the complete list of integral points of
  `y² = x³ − D`, under the premises of that curve's classes."""

DOC72 = """# The `D = 72` residual `H(u, v) = −3u³ + 9uv² − 2v³ = ±1`, under three named premises
(generated by `python/make_lean_unit_fields.py`)

`K = ℚ(δ)`, `δ³ = 9δ + 6`, `O_K = ℤ[δ]`, discriminant 1944.  The form `(−3, 0, 9, −2)` has
`φ = β = 6 − δ²` (`NormForm.d72_beta_of_delta`), and `N(c₀u − βv) = 9 H(u, v)`.

* **Premises, not proved in Lean:** `unitGen`, `normRep_pos` (norm 9) and `analytic_pos`.  The
  target `H = −1` uses the same two, transported by sign (`UnitPremises.normRep_neg_of`,
  `analytic_neg_of`: the form, `enc` and the norm are odd).
* **Kernel-checked:** the reduction chains (`H ≤ 4`), the box of `9²` elements and the search
  `|v| ≤ 1`.  `class_pos`, `class_neg`: no solution."""


def main():
    f756 = json.loads((ROOT / 'receipts' / 'field756_bound.json').read_text())
    d72 = json.loads((ROOT / 'receipts' / 'd72_thue_bound.json').read_text())
    witness = json.loads((ROOT / 'receipts' / 'unit_basis_witness.json').read_text())
    local = json.loads((ROOT / 'receipts' / 'norm_rep_localization.json').read_text())
    graph = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    gcls = {c['id']: c for c in graph['classes']}
    localized = {(f['P'], f['Q'], t['N']) for f in local['fields'] for t in t_iter(f)}
    report = {'fields': []}

    # ---- field 756
    P, Q = f756['P'], f756['Q']
    e1, e2 = (tuple(u) for u in f756['units'])
    pre, e1i, e2i, wrep = field_preamble(P, Q, e1, e2, witness)
    out = [head('Field756', DOC756), pre]
    lists, rows = {}, []
    shared = {}
    for c in f756['classes']:
        key = (c['form'][0] ** 2 * c['M'], tuple(c['gammas'][0]))
        shared.setdefault(key, []).append(c['class'])
    nnames = {}
    for (N, g0), ids in shared.items():
        nname = f"normRep_{N}" if sum(k[0] == N for k in shared) == 1 else f"normRep_{N}_{ids[0]}"
        for i in ids:
            nnames[i] = nname
        out.append(norm_rep_block(nname, P, Q, N, g0, [f'class {i}' for i in ids]))
    for c in f756['classes']:
        i, F, M, phi = c['class'], tuple(c['form']), c['M'], tuple(c['phi'])
        assert len(c['gammas']) == 1
        g0 = tuple(c['gammas'][0])
        B, V = c['H_bound'], c['V0']
        L = sorted(tuple(x) for x in c['pari_thue'])
        assert tuple(gcls[i]['representative']) == F and gcls[i]['M'] == M
        assert phi[1] != 0 or phi[2] != 0
        assert (P, Q, F[0] ** 2 * M) in localized
        hits = box_hits(P, Q, F, M, phi, g0, e1, e1i, e2, e2i, B)
        assert hits <= set(L), f'class {i}: box hit outside the list: {hits - set(L)}'
        assert {x for x in L if abs(x[1]) > V} <= hits, f'class {i}: positive control failed'
        sm = set(small_hits(F, M, V))
        assert sm <= set(L) and {x for x in L if abs(x[1]) <= V} <= sm
        lists[i] = L
        rows.append({'class': i, 'curves': c['curves'], 'B': B, 'V': V, 'box_size': (2 * B + 1) ** 2,
                     'box_hits': sorted(hits), 'small_b_hits': sorted(sm), 'list': L,
                     'reduction_steps': sum(len(x['steps']) for x in c['cases'])})
        out.append(class_block(str(i), P, Q, F, M, phi, g0, c['cases'], B, V, L,
                               f"class {i} (`D ∈ {c['curves']}`, `M = {M}`)", nnames[i]))
    census = {}
    with open(ROOT / 'data' / 'mordell_census.csv') as f:
        for row in csv.DictReader(f):
            census[int(row['k'])] = sorted(int(v) for v in row['x_coordinates'].split())
    curves = []
    for D in (7, 28, 63):
        c = compile_curve(D)
        a = lean_args(c)
        ids = next(x for x in graph['curves'] if x['D'] == D)['classes']
        thuesL, ys = [], set(a['Ys'])
        for e in c['open']:
            mem, cid = next((m, cid) for cid in ids for m in gcls[cid]['members']
                            if (m['D'], m['k'], m['p'], m['q']) == (D, e['k'], e['p'], e['q']))
            T = mem['T']
            thuesL.append(f"({_i(e['k'])}, {_i(e['p'])}, {_i(e['q'])}, {mat_lean(T)})")
            k3 = e['k'] ** 3
            for (u, v) in lists[cid]:
                aa, bb = T[0][0] * u + T[0][1] * v, T[1][0] * u + T[1][1] * v
                W = e['p'] * W1(D, aa, bb) + D * e['q'] * W2(D, aa, bb)
                if W % k3 == 0:
                    ys.add(W // k3)
        ys = sorted(ys)
        pts = [(icbrt(y * y + D), y) for y in ys if icbrt(y * y + D) ** 3 == y * y + D]
        assert sorted({x for x, _ in pts}) == census.get(-D, []), f'D = {D}: disagrees with the Sage census'
        curves.append({'D': D, 'classes': ids, 'open_branches': len(c['open']), 'points': pts,
                       'candidate_ys': ys, 'agrees_with_sage': True})
        cubes = '[' + ', '.join('(' + ', '.join(_i(v) for v in t) + ')' for t in a['cubes']) + ']'
        mods = '[' + ', '.join('(' + ', '.join(_i(v) for v in t) + ')' for t in a['mods']) + ']'
        listed = '[' + ', '.join(
            f"({form_lean(gcls[i]['representative'])}, {gcls[i]['M']}, {pairs_lean(lists[i])})" for i in ids) + ']'
        nn = sorted({nnames[i] for i in ids})
        hyps = ('(hU : unitGen) ' + ' '.join(f'(h{n} : {n})' for n in nn) + ' '
                + ' '.join(f'(hA{i} : analytic_{i})' for i in ids))
        pat = ' | '.join(['rfl'] * len(ids))
        cases = ' '.join(f'| exact (class_{i} hU h{nnames[i]} hA{i} u v).mp' for i in ids)
        out.append(
            f"set_option maxHeartbeats 0 in\n"
            f"/-- **The integral points of `y^2 = x^3 - {D}`, under the premises of classes {ids}**: "
            f"{len(pts)} point(s).  {len(a['cubes'])} field-cube and {len(a['mods'])} local branches; "
            f"{len(thuesL)} branches transported to the listed classes. -/\n"
            f"theorem minus{D} {hyps}\n    (x y : ℤ) : y ^ 2 = x ^ 3 - {D} ↔ (x, y) ∈ ({pairs_lean(pts)} : List (ℤ × ℤ)) :=\n"
            f"  DescentThueList.complete_of_lists {D} (by norm_num) {c['r']} {c['t']} (by norm_num) (by norm_num)"
            f" {c['K']} {c['Q']}\n    (by norm_num) (by norm_num)\n"
            f"    {cubes}\n    {mods}\n    [] []\n    [{', '.join(thuesL)}]\n    {listed}\n"
            f"    (by simp)\n"
            f"    (by intro c hc u v; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc\n"
            f"        rcases hc with {pat} <;> first {cases})\n"
            f"    {'[' + ', '.join(_i(y) for y in ys) + ']'}\n"
            f"    {pairs_lean(pts)}\n    (by decide +kernel) (by decide +kernel) x y\n")
    out.append('end PerfectPower.Generated.Field756\n')
    (ROOT / 'PerfectPower' / 'Generated' / 'Field756.lean').write_text('\n'.join(out))
    report['fields'].append({'field': 'x^3 - 6x - 2', 'unit_witness': wrep, 'classes': rows, 'curves': curves})

    # ---- D = 72
    P, Q = d72['P'], d72['Q']
    e1, e2 = (tuple(u) for u in d72['units'])
    pre, e1i, e2i, wrep = field_preamble(P, Q, e1, e2, witness)
    out = [head('D72Unit', DOC72), pre]
    F, phi, g0 = tuple(d72['form']), tuple(d72['phi']), tuple(d72['gammas'][0])
    B, V = d72['H_bound'], d72['V0']
    rows = []
    out.append(norm_rep_block('normRep_pos', P, Q, F[0] ** 2, g0, ['`H = 1` (and, transported by sign, `H = -1`)']))
    for name, M, g in (('pos', 1, g0), ('neg', -1, tuple(-x for x in g0))):
        assert (P, Q, F[0] ** 2 * M) in localized
        hits = box_hits(P, Q, F, M, phi, g, e1, e1i, e2, e2i, B)
        assert not hits and not small_hits(F, M, V)
        rows.append({'M': M, 'B': B, 'V': V, 'box_size': (2 * B + 1) ** 2, 'box_hits': [],
                     'reduction_steps': sum(len(x['steps']) for x in d72['cases'])})
        out.append(class_block(name, P, Q, F, M, phi, g, d72['cases'], B, V, [], f'`H(u, v) = {M}`',
                               'normRep_pos', neg_of=None if M == 1 else 'pos'))
    out.append('end PerfectPower.Generated.D72Unit\n')
    (ROOT / 'PerfectPower' / 'Generated' / 'D72Unit.lean').write_text('\n'.join(out))
    report['fields'].append({'field': 'x^3 - 9x - 6', 'unit_witness': wrep, 'classes': rows})

    report['label'] = ('Lean theorems conditional on the named premises unitGen, normRep_i, analytic_i '
                       '(Generated/Field756.lean, Generated/D72Unit.lean); reduction chains, norm identities, '
                       'boxes, small-b searches and branch transport are kernel-checked')
    (ROOT / 'receipts' / 'unit_fields_certificate.json').write_text(json.dumps(report, indent=1, default=list) + '\n')
    for f in report['fields']:
        print(f"{f['field']}: unit box {f['unit_witness']}")
        for r in f['classes']:
            print(f"  {r.get('class', r.get('M'))}: B={r['B']} V={r['V']} box {r['box_size']} "
                  f"steps {r['reduction_steps']} hits {r['box_hits']}")
        for c in f.get('curves', []):
            print(f"  D={c['D']}: classes {c['classes']}, points {c['points']}")


def t_iter(f):
    return f['targets']


if __name__ == '__main__':
    main()
