"""Generate `PerfectPower/Generated/Minus23.lean`: the integral points of y^2 = x^3 - 23, under
Matveev's lower bound for two unit equations.

The three open classes of D = 23 (8, 9, 10; `receipts/thue_graph.json`) descend
(`python/descent_residual.py`) to two unit equations in the cubic field of discriminant 621:
  F1(u, v) = -u^3 - 3u^2 v + 6u v^2 + 4v^3 = 1   (classes 8, 9, 10),
  F2(u, v) = -u^3 - 6u^2 v + 69u v^2 + 46v^3 = 1  (class 10).
Both live in Z[x], x^3 = 6x + 3 (disc 621, maximal), with phi_1 = 5 + x - x^2 and
phi_2 = 14 + 3x - 3x^2 (`norm(c0 a - b phi) = c0^2 F(a, b)`, checked by `ring` in Lean).

Emitted, all checked by the kernel:
* unit generation for Z[x] (`UnitGenProof.unitGen_of_cert`), units eps1 = -2 - x, eps2 = -1 - 2x;
* norm representatives for norm 1: `NormRepProof.normRep_one` (the adjugate inverse);
* for F1 = 1 and F2 = 1: the analytic certificate (`AnalyticBridge.analytic_of_cert`), the
  reduction chains, the box and the small-b search: `class_u1`, `class_u2`, complete lists under
  `matveev_u1`, `matveev_u2`;
* for classes 8, 9, 10: solution-carrying descent certificates (`DescentLists.descL`, a prime per
  node, leaves carried from F1, F2 by unimodular maps), so `class_8` ... `class_10` are complete
  lists;
* `minus23`: the curve, by `DescentThueList.complete_of_lists`, agreeing with the Sage census.

Run: python3 python/make_lean_minus23.py
"""
from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))
sys.path.insert(0, str(ROOT))

import make_lean_unit_fields as U  # noqa: E402
from perfectpower import thue_graph as TG  # noqa: E402
from perfectpower.branch_descent import compile_curve, lean_args  # noqa: E402
from perfectpower.descent import W1, W2  # noqa: E402
from python.make_lean_thue_branch import lift_obstruction, line_mat, vp  # noqa: E402

P, Q = 6, 3
E1, E2 = (-2, -1, 0), (-1, -2, 0)
UNITS = [('u1', (-1, -3, 6, 4), (5, 1, -1)), ('u2', (-1, -6, 69, 46), (14, 3, -3))]
D = 23


def primes_of(n):
    n, out, p = abs(n), [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def neg(F):
    return tuple(-c for c in F)


def descent_tree(F, M, sources):
    """Nodes (F, M, kind) in BFS order (children after parents); kinds as tuples."""
    nodes = [[tuple(F), M, None]]
    k = 0
    while k < len(nodes):
        F, M, _ = nodes[k]
        if abs(M) == 1:
            H = F if M == 1 else neg(F)
            key, T0 = TG.canonical(H)
            c = next(i for i, (S, _) in enumerate(sources) if tuple(S) == tuple(key))
            T = TG.inverse(T0)
            assert TG.compose(sources[c][0], T) == tuple(M * x for x in F)
            nodes[k][2] = ('given', c, T, T0, M)
            k += 1
            continue
        p = primes_of(M)[0]
        zero, lines = None, []
        kids = []
        if M % p ** 3 == 0:
            kids.append(('zero', None, 3, tuple(F), M // p ** 3))
        roots = [l for l in range(p) if TG.evalF(F, l, 1) % p == 0]
        if F[0] % p == 0:
            roots.append(None)
        for lam in roots:
            H = TG.compose(F, line_mat(p, lam))
            s = min(min(vp(c, p) if c else 60 for c in H), vp(M, p))
            assert s >= 1
            kids.append(('line', lam, s, tuple(c // p ** s for c in H), M // p ** s))
        for kind, lam, s, K, N in kids:
            dead = None
            for q in (2, 3, 5, 7):
                if N % q:
                    r = lift_obstruction(K, N, q, 3)
                    if r:
                        dead = (q, r[0])
                        break
            j = len(nodes)
            nodes.append([K, N, ('leaf', dead[0], dead[1]) if dead else None])
            if kind == 'zero':
                zero = j
            else:
                lines.append((lam, s, j))
        nodes[k][2] = ('split', p, zero, lines)
        k += 1
        # skip already-decided leaves
        while k < len(nodes) and nodes[k][2] is not None:
            k += 1
    return [tuple(n) for n in nodes]


def app(T, uv):
    (a, b), (c, d) = T
    return (a * uv[0] + b * uv[1], c * uv[0] + d * uv[1])


def candidates(nodes, sources, i=0):
    F, M, kind = nodes[i]
    if kind[0] == 'leaf':
        return []
    if kind[0] == 'given':
        _, c, T, Tinv, s = kind
        return [app(Tinv, x) for x in sources[c][1]]
    _, p, zero, lines = kind
    out = []
    if zero is not None:
        out += [(p * a, p * b) for a, b in candidates(nodes, sources, zero)]
    for lam, s, j in lines:
        out += [app(line_mat(p, lam), x) for x in candidates(nodes, sources, j)]
    return out


def mat(T):
    (a, b), (c, d) = T
    return f"(({U._i(a)}, {U._i(b)}), ({U._i(c)}, {U._i(d)}))"


def kind_lean(k):
    if k[0] == 'leaf':
        return f"DescentLists.KindL.leaf {k[1]} {k[2]}"
    if k[0] == 'given':
        _, c, T, Tinv, s = k
        return f"DescentLists.KindL.given {c} {mat(T)} {mat(Tinv)} {U._i(s)}"
    _, p, zero, lines = k
    z = 'none' if zero is None else f'(some {zero})'
    ls = '[' + ', '.join(f"({'none' if lam is None else f'(some {lam})'}, {s}, {j})" for lam, s, j in lines) + ']'
    return f"DescentLists.KindL.split {p} {z} {ls}"


def node_lean(n):
    F, M, k = n
    return f"({U.form_lean(F)}, {U._i(M)}, {kind_lean(k)})"


def preamble():
    e1i, e2i = U.inverse(P, Q, E1), U.inverse(P, Q, E2)
    cert = U.ug_cert(P, Q, E1, E2)
    text = (f'/-- `ε₁ = −2 − x`. -/\ndef e1 : Z3 := {U.z3_lean(E1)}\n/-- `ε₁⁻¹`. -/\ndef e1i : Z3 := {U.z3_lean(e1i)}\n'
            f'/-- `ε₂ = −1 − 2x`. -/\ndef e2 : Z3 := {U.z3_lean(E2)}\n/-- `ε₂⁻¹`. -/\ndef e2i : Z3 := {U.z3_lean(e2i)}\n\n'
            f'theorem e1_inv : mul {P} {Q} e1 e1i = (1, 0, 0) := by decide\n'
            f'theorem e2_inv : mul {P} {Q} e2 e2i = (1, 0, 0) := by decide\n\n'
            f'/-- The unit-generation statement for `ℤ[x]`, `x³ = {P}x + {Q}`. -/\n'
            f'def unitGen : Prop := UnitPremises.UnitGen {P} {Q} e1 e1i e2 e2i\n\n'
            f'/-- The unit-generation certificate: root brackets, log witnesses, the bounds `Uᵢ`, the box '
            f'`{cert["ba"]}, {cert["bb"]}, {cert["bc"]}` and its {len(cert["reps"])} units as `±ε₁^x ε₂^y`. -/\n'
            f'def ugCert : UnitGenProof.UGCert :=\n  {U.ug_lean(cert)}\n\n'
            f'/-- **Unit generation, proved** (`UnitGenProof.unitGen_of_cert`). -/\n'
            f'theorem unitGen_proved : unitGen :=\n'
            f'  UnitGenProof.unitGen_of_cert {P} {Q} e1 e1i e2 e2i ugCert (by decide +kernel)\n\n'
            f'/-- Norm representatives for norm `1`. -/\n'
            f'def normRep_one : Prop := UnitPremises.NormRep {P} {Q} 1 [(1, 0, 0)]\n\n'
            f'/-- **Proved**: an element of norm `1` is a unit (`NormRepProof.normRep_one`). -/\n'
            f'theorem normRep_one_proved : normRep_one := NormRepProof.normRep_one {P} {Q}\n')
    return text, e1i, e2i, cert


DOC = """# `y² = x³ − 23`, under Matveev's bound for two unit equations
(generated by `python/make_lean_minus23.py`)

The three open classes of `D = 23` (8, 9, 10) descend to two unit equations in the cubic field of
discriminant 621, `ℤ[x]`, `x³ = 6x + 3`:
`F₁ = −u³ − 3u²v + 6uv² + 4v³ = 1` and `F₂ = −u³ − 6u²v + 69uv² + 46v³ = 1`.

* **Proved:** unit generation (`unitGen_proved`) and norm-`1` representatives (`normRep_one_proved`).
* **Proved:** the analytic statements `analytic_u1_proved`, `analytic_u2_proved` from Matveev's bound
  (`AnalyticBridge.analytic_of_cert`; the interval certificates are checked by the kernel).
* **Premises, not proved in Lean:** `matveev_u1`, `matveev_u2`.
* **Kernel-checked:** the reduction chains, boxes and small-`b` searches (`class_u1`, `class_u2`),
  the solution-carrying descent certificates of classes 8, 9, 10 (`desc_8`, `desc_9`, `desc_10`,
  a prime per node, leaves carried from `F₁`, `F₂` by unimodular maps), and the branch transport.
* `minus23`: the complete list of integral points of `y² = x³ − 23`, under `matveev_u1` and
  `matveev_u2`.  Classes 8 and 9 need only `matveev_u1`."""


def main():
    graph = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    gcls = {c['id']: c for c in graph['classes']}
    out = [U.head('Minus23', DOC).replace('import PerfectPower.DescentThueList\n',
                                           'import PerfectPower.DescentThueList\nimport PerfectPower.DescentLists\n')]
    pre, e1i, e2i, ugc = preamble()
    out.append(pre)
    report = {'field': {'P': P, 'Q': Q, 'disc': 621, 'units': [E1, E2],
                        'unit_box': [ugc['ba'], ugc['bb'], ugc['bc']], 'units_in_box': len(ugc['reps'])},
              'unit_equations': [], 'classes': []}
    sources = []
    for name, F, phi in UNITS:
        assert all(U.nrm(P, Q, U.enc(F[0], phi, a, b)) == F[0] ** 2 * U.evalF(F, a, b)
                   for a in range(-4, 5) for b in range(-4, 5))
        cert = U.analytic_cert(P, Q, F, 1, phi, (1, 0, 0), E1, E2, 0)
        V, cases = cert['V'], cert['cases_json']
        B = max(x['H_reduced'] for x in cases)
        hits = U.box_hits(P, Q, F, 1, phi, (1, 0, 0), E1, e1i, E2, e2i, B)
        sm = set(U.small_hits(F, 1, V))
        L = sorted(hits | sm)
        out.append(U.class_block(name, P, Q, F, 1, phi, (1, 0, 0), cases, B, V, L,
                                 f'`{list(F)} = 1`', 'normRep_one', cert=cert))
        sources.append((F, L))
        report['unit_equations'].append({'name': name, 'form': F, 'phi': phi, 'B': B, 'V': V,
                                         'list': L, 'analytic': cert['report']})
    src_names = {('u1',): 'src_1', ('u1', 'u2'): 'src_12'}
    out.append(f"/-- The source equation `F₁ = 1` with its complete list. -/\n"
               f"def src_1 : List (Form × List (ℤ × ℤ)) := [({U.form_lean(sources[0][0])}, {U.pairs_lean(sources[0][1])})]\n\n"
               f"/-- The source equations `F₁ = 1`, `F₂ = 1`. -/\n"
               f"def src_12 : List (Form × List (ℤ × ℤ)) :=\n  [({U.form_lean(sources[0][0])}, {U.pairs_lean(sources[0][1])}), "
               f"({U.form_lean(sources[1][0])}, {U.pairs_lean(sources[1][1])})]\n\n"
               f"theorem src_1_complete (hM1 : matveev_u1) : DescentLists.SourcesComplete src_1 :=\n"
               f"  DescentLists.sources_cons (fun a b h => (class_u1 hM1 a b).mp h) DescentLists.sources_nil\n\n"
               f"theorem src_12_complete (hM1 : matveev_u1) (hM2 : matveev_u2) : DescentLists.SourcesComplete src_12 :=\n"
               f"  DescentLists.sources_cons (fun a b h => (class_u1 hM1 a b).mp h)\n"
               f"    (DescentLists.sources_cons (fun a b h => (class_u2 hM2 a b).mp h) DescentLists.sources_nil)\n\n")
    lists = {}
    for cid in (8, 9, 10):
        c = gcls[cid]
        R, M = tuple(c['representative']), c['M']
        srcs = sources if cid == 10 else sources[:1]
        sname = 'src_12' if cid == 10 else 'src_1'
        nodes = descent_tree(R, M, srcs)
        used = {n[2][1] for n in nodes if n[2][0] == 'given'}
        assert used == set(range(len(srcs))), (cid, used)
        cand = candidates(nodes, srcs)
        L = sorted({x for x in cand if TG.evalF(R, *x) == M})
        brute = sorted((a, b) for a in range(-200, 201) for b in range(-200, 201) if TG.evalF(R, a, b) == M)
        assert set(brute) <= set(L), (cid, brute, L)
        lists[cid] = L
        rest = ',\n   '.join(node_lean(n) for n in nodes[1:])
        hyps = '(hM1 : matveev_u1) (hM2 : matveev_u2)' if cid == 10 else '(hM1 : matveev_u1)'
        comp = 'src_12_complete hM1 hM2' if cid == 10 else 'src_1_complete hM1'
        nl = sum(n[2][0] == 'leaf' for n in nodes)
        ng = sum(n[2][0] == 'given' for n in nodes)
        ns = sum(n[2][0] == 'split' for n in nodes)
        out.append(
            f"/-- The descent of class {cid} (`{list(R)} = {M}`): {len(nodes)} nodes, {ns} splits, {nl} lifting "
            f"leaves, {ng} leaves carried from the unit equations. -/\n"
            f"def kind_{cid} : DescentLists.KindL := {kind_lean(nodes[0][2])}\n\n"
            f"/-- The nodes of the descent of class {cid} after the root (children after parents). -/\n"
            f"def rest_{cid} : List (Form × ℤ × DescentLists.KindL) :=\n  [{rest}]\n\n"
            f"theorem desc_{cid} : DescentLists.descL {sname} (({U.form_lean(R)}, {U._i(M)}, kind_{cid}) :: rest_{cid}) = true := by\n"
            f"  decide +kernel\n\n"
            f"theorem root_{cid} : DescentLists.rootSet {sname} {U.form_lean(R)} {U._i(M)} kind_{cid} rest_{cid} =\n"
            f"    ({U.pairs_lean(L)} : List (ℤ × ℤ)).toFinset := by decide +kernel\n\n"
            f"/-- **Class {cid}, complete**: `{list(R)}` takes the value {M} exactly at {len(L)} point(s). -/\n"
            f"theorem class_{cid} {hyps} (u v : ℤ) :\n"
            f"    evalF {U.form_lean(R)} u v = {U._i(M)} ↔ (u, v) ∈ ({U.pairs_lean(L)} : List (ℤ × ℤ)) := by\n"
            f"  rw [DescentLists.root_iff {sname} ({comp}) _ _ kind_{cid} rest_{cid} desc_{cid}, root_{cid},\n"
            f"    List.mem_toFinset]\n")
        report['classes'].append({'class': cid, 'form': R, 'M': M, 'nodes': len(nodes), 'splits': ns,
                                  'lifting_leaves': nl, 'carried_leaves': ng, 'list': L,
                                  'primes': sorted({n[2][1] for n in nodes if n[2][0] == 'split'})})
    # the curve
    census = {}
    with open(ROOT / 'data' / 'mordell_census.csv') as f:
        for row in csv.DictReader(f):
            census[int(row['k'])] = sorted(int(v) for v in row['x_coordinates'].split())
    cc = compile_curve(D)
    a = lean_args(cc)
    ids = next(x for x in graph['curves'] if x['D'] == D)['classes']
    assert sorted(ids) == [8, 9, 10]
    thuesL, ys = [], set(a['Ys'])
    for e in cc['open']:
        mem, cid = next((m, cid) for cid in ids for m in gcls[cid]['members']
                        if (m['D'], m['k'], m['p'], m['q']) == (D, e['k'], e['p'], e['q']))
        T = mem['T']
        thuesL.append(f"({U._i(e['k'])}, {U._i(e['p'])}, {U._i(e['q'])}, {U.mat_lean(T)})")
        k3 = e['k'] ** 3
        for (u, v) in lists[cid]:
            aa, bb = T[0][0] * u + T[0][1] * v, T[1][0] * u + T[1][1] * v
            W = e['p'] * W1(D, aa, bb) + D * e['q'] * W2(D, aa, bb)
            if W % k3 == 0:
                ys.add(W // k3)
    ys = sorted(ys)
    pts = [(U.icbrt(y * y + D), y) for y in ys if U.icbrt(y * y + D) ** 3 == y * y + D]
    assert sorted({x for x, _ in pts}) == census.get(-D, []), ('disagrees with the Sage census', pts)
    cubes = '[' + ', '.join('(' + ', '.join(U._i(v) for v in t) + ')' for t in a['cubes']) + ']'
    mods = '[' + ', '.join('(' + ', '.join(U._i(v) for v in t) + ')' for t in a['mods']) + ']'
    listed = '[' + ', '.join(f"({U.form_lean(gcls[i]['representative'])}, {gcls[i]['M']}, {U.pairs_lean(lists[i])})"
                             for i in ids) + ']'
    out.append(
        f"set_option maxHeartbeats 0 in\n"
        f"/-- **The integral points of `y^2 = x^3 - 23`, under Matveev's bound for `F₁ = 1` and `F₂ = 1`**: "
        f"{len(pts)} point(s).  {len(a['cubes'])} field-cube and {len(a['mods'])} local branches; "
        f"{len(thuesL)} branches transported to classes 8, 9, 10. -/\n"
        f"theorem minus23 (hM1 : matveev_u1) (hM2 : matveev_u2)\n"
        f"    (x y : ℤ) : y ^ 2 = x ^ 3 - 23 ↔ (x, y) ∈ ({U.pairs_lean(pts)} : List (ℤ × ℤ)) :=\n"
        f"  DescentThueList.complete_of_lists 23 (by norm_num) {cc['r']} {cc['t']} (by norm_num) (by norm_num)"
        f" {cc['K']} {cc['Q']}\n    (by norm_num) (by norm_num)\n"
        f"    {cubes}\n    {mods}\n    [] []\n    [{', '.join(thuesL)}]\n    {listed}\n"
        f"    (by simp)\n"
        f"    (by intro c hc u v; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc\n"
        f"        rcases hc with rfl | rfl | rfl <;> first | exact (class_8 hM1 u v).mp | "
        f"exact (class_9 hM1 u v).mp | exact (class_10 hM1 hM2 u v).mp)\n"
        f"    {'[' + ', '.join(U._i(y) for y in ys) + ']'}\n"
        f"    {U.pairs_lean(pts)}\n    (by decide +kernel) (by decide +kernel) x y\n")
    out.append('end PerfectPower.Generated.Minus23\n')
    (ROOT / 'PerfectPower' / 'Generated' / 'Minus23.lean').write_text('\n'.join(out))
    report['curve'] = {'D': D, 'points': pts, 'candidate_ys': ys, 'agrees_with_sage': True,
                       'label': 'Lean theorem conditional on matveev_u1, matveev_u2 (Generated/Minus23.lean)'}
    (ROOT / 'receipts' / 'minus23_certificate.json').write_text(json.dumps(report, indent=1, default=list) + '\n')
    for r in report['classes']:
        print(f"class {r['class']}: {r['nodes']} nodes, primes {r['primes']}, list {r['list']}")
    for r in report['unit_equations']:
        print(f"{r['name']}: B={r['B']} V={r['V']} list {r['list']}")
    print('points', pts)


if __name__ == '__main__':
    main()
