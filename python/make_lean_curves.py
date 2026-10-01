"""Generate the curve certificates that run through solution-carrying descent:
`PerfectPower/Generated/Minus18.lean`, `Minus23.lean` and `Minus45.lean`.

Each curve is assembled from three separately checked layers.
1. **Field certificate.** `ℤ[x]`, `x³ = Px + Q`, with unit generation proved by
   `UnitGenProof.unitGen_of_cert` (or `unitGen_of_slices`), or imported from a shared order module
   (`'order'`: `Generated/Order1944.lean` serves `D = 72` and `D = 18`).
2. **Source equations** `F_j = 1`. Each one has:
   - a norm-representative proof, either `NormRepProof.normRep_one` (monic forms, norm `1`) or
     `NormRepProof.normRep_of_res`, a residue certificate for norm `c₀²` (nonmonic forms);
   - an analytic certificate (`AnalyticBridge.analytic_of_cert`) under `matveev_j`;
   - reduction chains, a box and a small-`b` search.
   The result is the complete list `F_j = 1 ⇔ (u, v) ∈ L_j` (`class_j`).
3. **Curve assembly.** Every open class of the curve descends, with a prime per node, to the
   source equations (`DescentLists.descL`, leaves carried by checked unimodular maps), and
   `DescentThueList.complete_of_lists` reads off the points.
The curve theorem keeps exactly the Matveev premises of the source equations that its classes use.

Run: python3 python/make_lean_curves.py
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

CURVES = {
    23: {'name': 'Minus23', 'P': 6, 'Q': 3, 'disc': 621, 'units': [(-2, -1, 0), (-1, -2, 0)],
         'sources': [{'name': 'u1', 'form': (-1, -3, 6, 4), 'phi': (5, 1, -1), 'normrep': ('one',)},
                     {'name': 'u2', 'form': (-1, -6, 69, 46), 'phi': (14, 3, -3), 'normrep': ('one',)}]},
    45: {'name': 'Minus45', 'P': 18, 'Q': 12, 'disc': 19440, 'units': [(-7, -3, 1), (-41, -51, 13)],
         'sources': [{'name': 'w1', 'form': (-2, -6, 3, 4), 'phi': (2, 1, 0),
                      'normrep': ('res', (4, 1, 0), 8)}]},
    # the order of the D = 72 residual: unit generation is imported, not re-checked
    18: {'name': 'Minus18', 'P': 9, 'Q': 6, 'disc': 1944, 'units': [(-1, -3, 1), (-1, 0, 2)], 'order': 'Order1944',
         'sources': [{'name': 'v1', 'form': (-1, -3, 6, 2), 'phi': (1, 1, 0), 'normrep': ('one',)},
                     {'name': 'v2', 'form': (-1, -9, 54, 54), 'phi': (3, 3, 0), 'normrep': ('one',)}]},
}


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




def z3txt(g):
    a, b, c = g
    parts = []
    for coef, mon in ((a, ''), (b, 'x'), (c, 'x²')):
        if coef:
            s = ('' if abs(coef) == 1 and mon else str(abs(coef))) + mon
            parts.append(('−' if coef < 0 else '+') + ' ' + s)
    t = ' '.join(parts).lstrip('+ ')
    return t.replace('− ', '−', 1) if t.startswith('− ') else t


def field_layer(cfg):
    P, Q = cfg['P'], cfg['Q']
    E1, E2 = cfg['units']
    e1i, e2i = U.inverse(P, Q, E1), U.inverse(P, Q, E2)
    cert = U.ug_cert(P, Q, E1, E2)
    if 'order' in cfg:
        o = cfg['order']
        return (f'/-! ### Layer 1: the field certificate (`ℤ[x]`, `x³ = {P}x + {Q}`)\n\n'
                f'Imported from `Generated/{o}.lean`, shared with the other certificates in this order: '
                f'`{o}.e1`, `{o}.e2`, `{o}.unitGen_proved` (`ε₁ = {z3txt(E1)}`, `ε₂ = {z3txt(E2)}`). -/\n'), e1i, e2i, cert
    text = (f'/-! ### Layer 1: the field certificate (`ℤ[x]`, `x³ = {P}x + {Q}`) -/\n\n'
            f'/-- `ε₁ = {z3txt(E1)}`. -/\ndef e1 : Z3 := {U.z3_lean(E1)}\n/-- `ε₁⁻¹`. -/\ndef e1i : Z3 := {U.z3_lean(e1i)}\n'
            f'/-- `ε₂ = {z3txt(E2)}`. -/\ndef e2 : Z3 := {U.z3_lean(E2)}\n/-- `ε₂⁻¹`. -/\ndef e2i : Z3 := {U.z3_lean(e2i)}\n\n'
            f'theorem e1_inv : mul {P} {Q} e1 e1i = (1, 0, 0) := by decide\n'
            f'theorem e2_inv : mul {P} {Q} e2 e2i = (1, 0, 0) := by decide\n\n'
            f'/-- The unit-generation statement for `ℤ[x]`, `x³ = {P}x + {Q}`. -/\n'
            f'def unitGen : Prop := UnitPremises.UnitGen {P} {Q} e1 e1i e2 e2i\n\n'
            f'/-- The unit-generation certificate: root brackets, log witnesses, the bounds `Uᵢ`, the box '
            f'`{cert["ba"]}, {cert["bb"]}, {cert["bc"]}` and its {len(cert["reps"])} units as `±ε₁^x ε₂^y`. -/\n'
            f'def ugCert : UnitGenProof.UGCert :=\n  {U.ug_lean(cert)}\n\n'
            )
    size = (2 * cert['ba'] + 1) * (2 * cert['bb'] + 1) * (2 * cert['bc'] + 1)
    if size <= 20000:
        text += (f'/-- **Unit generation, proved** (`UnitGenProof.unitGen_of_cert`). -/\n'
                 f'theorem unitGen_proved : unitGen :=\n'
                 f'  UnitGenProof.unitGen_of_cert {P} {Q} e1 e1i e2 e2i ugCert (by decide +kernel)\n')
        return text, e1i, e2i, cert
    # a large box: the same check in slices of the first coordinate, one kernel evaluation each
    w = max(1, 2000 // ((2 * cert['bb'] + 1) * (2 * cert['bc'] + 1)))
    n = -(-(2 * cert['ba'] + 1) // w)
    text += (f'/-- The certificate without the box enumeration (`UnitGenProof.ugCore`). -/\n'
             f'theorem ugCore_ok : UnitGenProof.ugCore {P} {Q} e1 e1i e2 e2i ugCert = true := by decide +kernel\n\n'
             f'/-- The {len(cert["reps"])} units of the box. -/\n'
             f'def ugCands : List Z3 := ugCert.reps.map (UnitGenProof.evalRep {P} {Q} e1 e1i e2 e2i)\n\n')
    for t in range(n):
        text += (f'theorem ugSlice_{t} : UnitGenProof.unitBoxSlice {P} {Q} {cert["ba"]} {cert["bb"]} {cert["bc"]} '
                 f'ugCands {w} {t} = true := by decide +kernel\n')
    text += (f'\n/-- **Unit generation, proved** (`UnitGenProof.unitGen_of_slices`: the box of {size} triples in '
             f'{n} slices of width {w}). -/\n'
             f'theorem unitGen_proved : unitGen :=\n'
             f'  UnitGenProof.unitGen_of_slices {P} {Q} e1 e1i e2 e2i ugCert (w := {w}) (n := {n}) ugCore_ok\n'
             f'    (by norm_num) (by decide)\n'
             f'    (fun (t : ℕ) (ht : t < {n}) => by\n      interval_cases t\n      exacts [{", ".join(f"ugSlice_{t}" for t in range(n))}])\n')
    return text, e1i, e2i, cert


def normrep_layer(cfg, s):
    P, Q = cfg['P'], cfg['Q']
    F = s['form']
    N = F[0] ** 2
    nm = f"normRep_{s['name']}"
    if s['normrep'][0] == 'one':
        assert N == 1
        return nm, (1, 0, 0), (f"/-- Norm representatives for `{s['name']}`: norm `1`. -/\n"
                               f"def {nm} : Prop := UnitPremises.NormRep {P} {Q} 1 [(1, 0, 0)]\n\n"
                               f"/-- **Proved**: an element of norm `1` is a unit (`NormRepProof.normRep_one`). -/\n"
                               f"theorem {nm}_proved : {nm} := NormRepProof.normRep_one {P} {Q}\n\n")
    _, g, m = s['normrep']
    assert U.nrm(P, Q, g) == N, (g, U.nrm(P, Q, g), N)
    return nm, g, (f"/-- Norm representatives for `{s['name']}`: every element of norm `{N}` (`= c₀²`) is "
                   f"`{z3txt(g)}` times a unit. -/\n"
                   f"def {nm} : Prop := UnitPremises.NormRep {P} {Q} {N} [{U.z3_lean(g)}]\n\n"
                   f"/-- **Proved by a residue certificate modulo {m}** (`NormRepProof.normRep_of_res`): every "
                   f"residue class of norm `≡ {N}` is divisible by `{z3txt(g)}`, and the quotient has norm `±1`. -/\n"
                   f"theorem {nm}_proved : {nm} :=\n  NormRepProof.normRep_of_res (m := {m}) (by norm_num) (by decide +kernel)\n\n")


def doc(cfg, D, lists_info):
    srcs = ', '.join(f"`{s['name']}`: `{list(s['form'])} = 1`" for s in cfg['sources'])
    return (f"# `y² = x³ − {D}`, under Matveev's bound for its source equations\n"
            f"(generated by `python/make_lean_curves.py`)\n\n"
            f"The open classes of `D = {D}` ({lists_info}) descend to the source equations {srcs}, in\n"
            f"`ℤ[x]`, `x³ = {cfg['P']}x + {cfg['Q']}` (discriminant {cfg['disc']}).\n\n"
            f"* **Layer 1, proved:** unit generation (`unitGen_proved`"
            f"{', imported from `Generated/' + cfg['order'] + '.lean`' if 'order' in cfg else ''}).\n"
            f"* **Layer 2:** for each source equation, norm representatives (`normRep_*_proved`), the analytic\n"
            f"  statement from Matveev's bound (`analytic_*_proved`), reduction chains, box and small-`b` search\n"
            f"  (`class_*`).  **Premises, not proved in Lean:** the `matveev_*`.\n"
            f"* **Layer 3, kernel-checked:** the solution-carrying descent certificates (`desc_*`, `root_*`,\n"
            f"  `class_*`) and the branch transport.\n"
            f"* `minus{D}`: the complete list of integral points, under the Matveev premises it uses.")


def build(D):
    cfg = CURVES[D]
    P, Q = cfg['P'], cfg['Q']
    E1, E2 = cfg['units']
    graph = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    gcls = {c['id']: c for c in graph['classes']}
    ids = sorted(next(x for x in graph['curves'] if x['D'] == D)['classes'])
    name = cfg['name']
    hd = U.head(name, doc(cfg, D, ', '.join(map(str, ids)))).replace(
        'import PerfectPower.DescentThueList\n', 'import PerfectPower.DescentThueList\nimport PerfectPower.DescentLists\n')
    if 'order' in cfg:
        hd = hd.replace('import PerfectPower.UnitGen\n', f"import PerfectPower.Generated.{cfg['order']}\n").replace(
            'open PerfectPower ThueLocal UnitBox\n', f"open PerfectPower ThueLocal UnitBox {cfg['order']}\n")
    out = [hd]
    # the kernel evaluations are large; check them one at a time to bound memory
    out.append('set_option Elab.async false\n')
    pre, e1i, e2i, ugc = field_layer(cfg)
    out.append(pre)
    report = {'curve': D, 'field': {'P': P, 'Q': Q, 'disc': cfg['disc'], 'units': [E1, E2],
                                    'unit_box': [ugc['ba'], ugc['bb'], ugc['bc']], 'units_in_box': len(ugc['reps'])},
              'sources': [], 'classes': []}
    out.append('/-! ### Layer 2: the source equations -/\n')
    sources = []
    for s in cfg['sources']:
        F, phi = s['form'], s['phi']
        assert all(U.nrm(P, Q, U.enc(F[0], phi, a, b)) == F[0] ** 2 * U.evalF(F, a, b)
                   for a in range(-4, 5) for b in range(-4, 5))
        nm, g0, nrtext = normrep_layer(cfg, s)
        out.append(nrtext)
        cert = U.analytic_cert(P, Q, F, 1, phi, g0, E1, E2, 0)
        V, cases = cert['V'], cert['cases_json']
        B = max(x['H_reduced'] for x in cases)
        hits = U.box_hits(P, Q, F, 1, phi, g0, E1, e1i, E2, e2i, B)
        sm = set(U.small_hits(F, 1, V))
        L = sorted(hits | sm)
        out.append(U.class_block(s['name'], P, Q, F, 1, phi, g0, cases, B, V, L,
                                 f'`{list(F)} = 1`', nm, cert=cert))
        sources.append((s['name'], F, L))
        report['sources'].append({'name': s['name'], 'form': F, 'phi': phi, 'normrep': list(s['normrep']),
                                  'gamma0': g0, 'B': B, 'V': V, 'list': L,
                                  'canonical': list(TG.canonical(F)[0]), 'analytic': cert['report']})
    out.append('/-! ### Layer 3: descent and curve assembly -/\n')
    lists, src_defs, uses = {}, {}, {}
    for cid in ids:
        c = gcls[cid]
        R, M = tuple(c['representative']), c['M']
        nodes = descent_tree(R, M, [(F, L) for _, F, L in sources])
        used = sorted({n[2][1] for n in nodes if n[2][0] == 'given'})
        # re-index the tree on the used sources only, so each class keeps only its own premises
        remap = {u: k for k, u in enumerate(used)}
        nodes = [(F, N, (k[0], remap[k[1]]) + tuple(k[2:]) if k[0] == 'given' else k) for F, N, k in nodes]
        srcs = [sources[u] for u in used]
        key = '_'.join(s[0] for s in srcs)
        if key not in src_defs:
            body = ', '.join(f"({U.form_lean(F)}, {U.pairs_lean(L)})" for _, F, L in srcs)
            hyps = ' '.join(f"(hM_{n} : matveev_{n})" for n, _, _ in srcs)
            proof = 'DescentLists.sources_nil'
            for n, _, _ in reversed(srcs):
                proof = f"(DescentLists.sources_cons (fun a b h => (class_{n} hM_{n} a b).mp h) {proof})"
            src_defs[key] = (hyps, ' '.join(f"hM_{n}" for n, _, _ in srcs))
            out.append(f"/-- The source equations {', '.join(s[0] for s in srcs)} with their complete lists. -/\n"
                       f"def src_{key} : List (Form × List (ℤ × ℤ)) := [{body}]\n\n"
                       f"theorem src_{key}_complete {hyps} : DescentLists.SourcesComplete src_{key} :=\n"
                       f"  {proof}\n")
        hyps, args = src_defs[key]
        uses[cid] = [s[0] for s in srcs]
        cand = candidates(nodes, [(F, L) for _, F, L in srcs])
        L = sorted({x for x in cand if TG.evalF(R, *x) == M})
        brute = sorted((a, b) for a in range(-200, 201) for b in range(-200, 201) if TG.evalF(R, a, b) == M)
        assert set(brute) <= set(L), (cid, brute, L)
        lists[cid] = L
        rest = ',\n   '.join(node_lean(n) for n in nodes[1:])
        nl = sum(n[2][0] == 'leaf' for n in nodes)
        ng = sum(n[2][0] == 'given' for n in nodes)
        ns = sum(n[2][0] == 'split' for n in nodes)
        out.append(
            f"/-- The descent of class {cid} (`{list(R)} = {M}`): {len(nodes)} nodes, {ns} splits, {nl} lifting "
            f"leaves, {ng} leaves carried from the source equations. -/\n"
            f"def kind_{cid} : DescentLists.KindL := {kind_lean(nodes[0][2])}\n\n"
            f"/-- The nodes of the descent of class {cid} after the root (children after parents). -/\n"
            f"def rest_{cid} : List (Form × ℤ × DescentLists.KindL) :=\n  [{rest}]\n\n"
            f"theorem desc_{cid} : DescentLists.descL src_{key} (({U.form_lean(R)}, {U._i(M)}, kind_{cid}) :: rest_{cid}) = true := by\n"
            f"  decide +kernel\n\n"
            f"theorem root_{cid} : DescentLists.rootSet src_{key} {U.form_lean(R)} {U._i(M)} kind_{cid} rest_{cid} =\n"
            f"    ({U.pairs_lean(L)} : List (ℤ × ℤ)).toFinset := by decide +kernel\n\n"
            f"/-- **Class {cid}, complete**: `{list(R)}` takes the value {M} exactly at {len(L)} point(s). -/\n"
            f"theorem class_{cid} {hyps} (u v : ℤ) :\n"
            f"    evalF {U.form_lean(R)} u v = {U._i(M)} ↔ (u, v) ∈ ({U.pairs_lean(L)} : List (ℤ × ℤ)) := by\n"
            f"  rw [DescentLists.root_iff src_{key} (src_{key}_complete {args}) _ _ kind_{cid} rest_{cid} desc_{cid}, root_{cid},\n"
            f"    List.mem_toFinset]\n")
        report['classes'].append({'class': cid, 'form': R, 'M': M, 'nodes': len(nodes), 'splits': ns,
                                  'lifting_leaves': nl, 'carried_leaves': ng, 'list': L, 'sources': uses[cid],
                                  'primes': sorted({n[2][1] for n in nodes if n[2][0] == 'split'})})
    census = {}
    with open(ROOT / 'data' / 'mordell_census.csv') as f:
        for row in csv.DictReader(f):
            census[int(row['k'])] = sorted(int(v) for v in row['x_coordinates'].split())
    cc = compile_curve(D)
    a = lean_args(cc)
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
    needed = sorted({n for cid in ids for n in uses[cid]})
    hyps = ' '.join(f"(hM_{n} : matveev_{n})" for n in needed)
    alts = ' | '.join(f"exact (class_{cid} {' '.join('hM_' + n for n in uses[cid])} u v).mp" for cid in ids)
    pat = ' | '.join(['rfl'] * len(ids))
    out.append(
        f"set_option maxHeartbeats 0 in\n"
        f"/-- **The integral points of `y^2 = x^3 - {D}`, under Matveev's bound for "
        f"{', '.join('`' + n + '`' for n in needed)}**: {len(pts)} point(s).  {len(a['cubes'])} field-cube and "
        f"{len(a['mods'])} local branches; {len(thuesL)} branches transported to classes {ids}. -/\n"
        f"theorem minus{D} {hyps}\n"
        f"    (x y : ℤ) : y ^ 2 = x ^ 3 - {D} ↔ (x, y) ∈ ({U.pairs_lean(pts)} : List (ℤ × ℤ)) :=\n"
        f"  DescentThueList.complete_of_lists {D} (by norm_num) {cc['r']} {cc['t']} (by norm_num) (by norm_num)"
        f" {cc['K']} {cc['Q']}\n    (by norm_num) (by norm_num)\n"
        f"    {cubes}\n    {mods}\n    [] []\n    [{', '.join(thuesL)}]\n    {listed}\n"
        f"    (by simp)\n"
        f"    (by intro c hc u v; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc\n"
        f"        rcases hc with {pat} <;> first | {alts})\n"
        f"    {'[' + ', '.join(U._i(y) for y in ys) + ']'}\n"
        f"    {U.pairs_lean(pts)}\n    (by decide +kernel) (by decide +kernel) x y\n")
    out.append(f'end PerfectPower.Generated.{name}\n')
    (ROOT / 'PerfectPower' / 'Generated' / f'{name}.lean').write_text('\n'.join(out))
    report['curve_points'] = pts
    report['premises'] = [f'matveev_{n}' for n in needed]
    report['label'] = f'Lean theorem conditional on {", ".join(report["premises"])} (Generated/{name}.lean)'
    (ROOT / 'receipts' / f'minus{D}_certificate.json').write_text(json.dumps(report, indent=1, default=list) + '\n')
    for r in report['classes']:
        print(f"D={D} class {r['class']}: {r['nodes']} nodes, primes {r['primes']}, sources {r['sources']}, list {r['list']}")
    for r in report['sources']:
        print(f"D={D} {r['name']}: B={r['B']} V={r['V']} gamma0={r['gamma0']} list {r['list']}")
    print(f"D={D} points {pts}")
    return report


def main():
    for D in sorted(CURVES):
        build(D)


if __name__ == '__main__':
    main()
