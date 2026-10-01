"""Price the unresolved curves before proving them: `receipts/order_cost.json`.

For each unresolved curve `D`, `J_D` is the set of unregistered unit equations its unresolved
classes descend to (`receipts/descent_coverage.json`).  The estimated kernel work is

    C(D) = Σ_{new orders R} C_UnitGen(R) + Σ_{j ∈ J_D} C_source(j) + C_assembly(D).

* **Order.** A unit equation `F = (c₀, c₁, c₂, c₃)` encodes as `N(c₀u − vφ) = c₀²F(u, v)`, where `φ`
  has characteristic polynomial `s³ + c₁s² + c₀c₂s + c₀²c₃`.  With `3 ∣ c₁` (true for all of the
  workload) `φ = −c₁/3 + x`, `x³ = Px + Q`.  When `k²∣P` and `k³∣Q` the element `x/k` is integral, so the
  equation lives in the larger order `ℤ[x/k]` with `φ = −c₁/3 + kθ`; the largest such `k` is taken,
  and equations whose orders coincide share one unit-generation proof.  This misses coincidences
  between orders not related by scaling.
* **C_UnitGen.** Units by `find_units` (quotients of small elements of equal norm; no PARI).  The
  basis is chosen by `best_basis` over `GL₂(ℤ)` (entries `|Uᵢⱼ| ≤ 2`) to minimize the proved
  enumeration: the box size, or the slab cost (`UnitGenProof.unitGen_of_slab`: lattice points + 3
  per row).  Orders already proved in Lean cost 0.  An order whose units are not found is UNPRICED.
* **C_source.** Monic equations (norm `1`): the analytic certificate's reduced bound `B`, so the box
  `(2B + 1)²`, plus the reduction steps.  Nonmonic equations need a residue norm-representative
  certificate first; they are reported without a source price (`normrep: residue`).
* **C_assembly.** The number of descent nodes of the curve's unresolved classes.
* **Transports.** With the Lean-checked order maps (`receipts/order_transports.json`,
  `Generated/OrderMaps.lean`), an order may be replaced by a proved or cheaper target; each target is
  charged once per curve (`C_unitgen_transported`).  The sources must then be re-encoded and their
  analytic certificates recomputed in the target, so `C_sources` stays the estimate in the own order.
  `C` (the sort key) uses original orders only; `C_transported_proxy` and `ranking_transported_proxy`
  mix the two and are labeled proxies.  The target is chosen per order, not per curve: a shared
  target that no single order prefers can be cheaper for the curve (a later refinement).

These are estimates of kernel work, not proofs.  Run: python3 python/order_cost.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))
sys.path.insert(0, str(ROOT))

import make_lean_unit_fields as U  # noqa: E402
import make_lean_curves as C  # noqa: E402

# orders whose unit generation is already a Lean theorem (field 756, 1944, 621, 19440, 9612)
PROVED = {(6, 2): 'Generated/Field756.lean', (9, 6): 'Generated/Order1944.lean',
          (6, 3): 'Generated/Minus23.lean', (18, 12): 'Generated/Minus45.lean',
          (15, 12): 'Generated/Minus89.lean', (12, 10): 'Generated/Minus39.lean',
          (36, 82): 'Generated/Minus47.lean', (12, 14): 'Generated/Minus60.lean'}


def order_of(F):
    """`(P, Q, k, φ)`: the order `ℤ[θ]`, `θ³ = Pθ + Q`, containing `φ = (a, k, 0) = a + kθ`."""
    c0, c1, c2, c3 = F
    assert c1 % 3 == 0
    a = -c1 // 3
    # s = x + a with s³ + c₁s² + c₀c₂s + c₀²c₃ = 0
    P = -(3 * a * a + 2 * c1 * a + c0 * c2)
    Q = -(a ** 3 + c1 * a * a + c0 * c2 * a + c0 * c0 * c3)
    k = 1
    for m in range(2, int(abs(P) ** 0.5) + 2 if P else 2):
        while P % (m * m) == 0 and Q % (m ** 3) == 0 and (P, Q) != (0, 0):
            P, Q, k = P // (m * m), Q // m ** 3, k * m
    if P < 0:
        raise ValueError('not totally real')
    phi = (a, k, 0)
    assert all(U.nrm(P, Q, U.enc(c0, phi, u, v)) == c0 * c0 * U.evalF(F, u, v)
               for u in range(-3, 4) for v in range(-3, 4))
    return P, Q, k, phi


def price_order(P, Q):
    if (P, Q) in PROVED:
        return {'P': P, 'Q': Q, 'disc': 4 * P ** 3 - 27 * Q ** 2, 'status': 'PROVED', 'module': PROVED[(P, Q)],
                'cost': 0}
    u = U.find_units(P, Q)
    if u is None:
        return {'P': P, 'Q': Q, 'disc': 4 * P ** 3 - 27 * Q ** 2, 'status': 'UNPRICED', 'cost': None}
    e1, e2, reg = u
    try:
        b = U.best_basis(P, Q, e1, e2)
    except (AssertionError, TypeError):
        return {'P': P, 'Q': Q, 'disc': 4 * P ** 3 - 27 * Q ** 2, 'status': 'UNPRICED', 'cost': None,
                'units': [e1, e2]}
    return {'P': P, 'Q': Q, 'disc': 4 * P ** 3 - 27 * Q ** 2, 'status': 'PRICED', 'units': [e1, e2],
            'regulator': round(reg, 3), 'basis_change': b['U'], 'basis': [b['e1'], b['e2']],
            'method': b['method'], 'cost': b['cost'], 'box': b['box'], 'slab_points': b['slab_points'],
            'slab_rows': b['slab_rows'], 'bounds': b['bounds']}


def price_source(F, order):
    P, Q, k, phi = order_of(F)
    out = {'form': list(F), 'P': P, 'Q': Q, 'phi': list(phi)}
    if abs(F[0]) != 1:
        return dict(out, normrep='residue', cost=None)
    o = order
    if o['status'] == 'UNPRICED':
        return dict(out, normrep='one', cost=None)
    if o['status'] == 'PROVED':
        e1, e2 = PROVED_UNITS[(P, Q)]
    else:
        e1, e2 = o['basis']
    try:
        cert = U.analytic_cert(P, Q, tuple(F), 1, phi, (1, 0, 0), tuple(e1), tuple(e2), 0)
    except (AssertionError, ZeroDivisionError, ValueError) as ex:
        return dict(out, normrep='one', cost=None, analytic_error=str(ex)[:80])
    B = max(c['H_reduced'] for c in cert['cases_json'])
    steps = sum(len(c['steps']) for c in cert['cases_json'])
    return dict(out, normrep='one', B=B, V=cert['V'], steps=steps, cost=(2 * B + 1) ** 2 + steps)


PROVED_UNITS = {(9, 6): ((-1, -3, 1), (-1, 0, 2)),
                (6, 3): ((-2, -1, 0), (-1, -2, 0)), (18, 12): ((-7, -3, 1), (-41, -51, 13)),
                (15, 12): ((37, 55, 13), (-131, -125, 37)), (12, 10): ((-11, -1, 1), (-3, -1, 0)),
                (36, 82): ((-3, -1, 0), (-411, -72, 19)), (12, 14): ((-5, -5, -1), (-11, -12, -3))}


def main():
    f756 = json.loads((ROOT / 'receipts' / 'field756_bound.json').read_text())
    PROVED_UNITS[(f756['P'], f756['Q'])] = tuple(tuple(u) for u in f756['units'])
    cov = json.loads((ROOT / 'receipts' / 'descent_coverage.json').read_text())
    graph = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    gcls = {c['id']: c for c in graph['classes']}
    allsrc = [(tuple(e['form']), []) for e in cov['unit_equations']]
    needed = [e for e in cov['unit_equations'] if e['needed']]
    orders, sources = {}, {}
    for e in needed:
        F = tuple(e['form'])
        P, Q, k, phi = order_of(F)
        if (P, Q) not in orders:
            orders[(P, Q)] = price_order(P, Q)
        sources[F] = price_source(F, orders[(P, Q)])
        print(F, (P, Q), orders[(P, Q)]['status'], orders[(P, Q)]['cost'], sources[F].get('cost'), flush=True)
    # order maps (receipts/order_transports.json, Lean: Generated/OrderMaps.lean): an order with a map
    # into a proved or cheaper order is charged at the target, and a target is charged once per curve
    tr = json.loads((ROOT / 'receipts' / 'order_transports.json').read_text())['embeddings']
    priced = dict(orders)
    effective = {}
    for o in orders:
        best = (orders[o]['cost'], o, None) if orders[o]['cost'] is not None else None
        for k, e in enumerate(tr):
            if tuple(e['domain']) != o:
                continue
            t = tuple(e['codomain'])
            if t not in priced:
                priced[t] = price_order(*t)
            c = priced[t]['cost']
            if c is not None and (best is None or c < best[0]):
                best = (c, t, k)
        effective[o] = best
    curves = []
    for w in cov['curves_unresolved_workload']:
        forms = [tuple(f) for f in w['forms']]
        ords = sorted({(sources[F]['P'], sources[F]['Q']) for F in forms})
        nodes = 0
        for cid in w['unresolved_classes']:
            R, M = tuple(gcls[cid]['representative']), gcls[cid]['M']
            try:
                nodes += len(C.descent_tree(R, M, allsrc))
            except StopIteration:
                nodes = None
                break
        parts = [orders[o]['cost'] for o in ords] + [sources[F]['cost'] for F in forms]
        total = None if any(p is None for p in parts) or nodes is None else sum(parts) + nodes
        shared = {F: [x['D'] for x in cov['curves_unresolved_workload']
                      if x['D'] != w['D'] and list(F) in x['forms']] for F in forms}
        targets = {}
        for o in ords:
            if effective[o] is not None:
                targets[effective[o][1]] = effective[o][0]
        via = {str(list(o)): {'target': list(effective[o][1]), 'map': effective[o][2]}
               for o in ords if effective[o] is not None and effective[o][2] is not None}
        unit_t = None if any(effective[o] is None for o in ords) else sum(targets.values())
        src_c = [sources[F]['cost'] for F in forms]
        proxy = (None if unit_t is None or nodes is None or any(c is None for c in src_c)
                 else unit_t + sum(src_c) + nodes)
        curves.append({'D': w['D'], 'classes': w['unresolved_classes'], 'sources': [list(F) for F in forms],
                       'C_unitgen_transported': unit_t, 'transports': via,
                       'C_transported_proxy': proxy,
                       'orders': [list(o) for o in ords],
                       'new_orders': [list(o) for o in ords if orders[o]['status'] != 'PROVED'],
                       'C_unitgen': sum(orders[o]['cost'] or 0 for o in ords),
                       'C_sources': sum(sources[F]['cost'] or 0 for F in forms),
                       'C_assembly': nodes, 'C': total,
                       'unpriced': [list(F) for F in forms if sources[F]['cost'] is None],
                       'sources_shared_with': {str(list(F)): v for F, v in shared.items() if v}})
    curves.sort(key=lambda c: (c['C'] is None, c['C'] or 0, c['D']))
    proxy_rank = [[c['D'], c['C_transported_proxy']] for c in
                  sorted(curves, key=lambda c: (c['C_transported_proxy'] is None, c['C_transported_proxy'] or 0, c['D']))]
    out = {'label': 'ESTIMATED kernel work (lattice points, box sizes, descent nodes) for the unresolved '
                    'curves; not a proof. Orders already proved in Lean are charged 0.',
           'row_weight': 3,
           'ranking_transported_proxy': proxy_rank,
           'proxy_note': 'C_transported_proxy mixes the transported unit-generation cost with source costs '
                         'estimated in the original orders; the sources must be re-encoded and re-priced in '
                         'the target before it is a price. C (the sort key of curves) uses original orders only.',
           'orders': [dict(v, key=list(k)) for k, v in sorted(orders.items())],
           'sources': list(sources.values()), 'curves': curves}
    (ROOT / 'receipts' / 'order_cost.json').write_text(json.dumps(out, indent=1, default=list) + '\n')
    for c in curves:
        print(c['D'], c['C'], c['C_unitgen'], c['C_unitgen_transported'], c['C_sources'], c['C_assembly'],
              c['new_orders'], c['transports'], len(c['unpriced']))


if __name__ == '__main__':
    main()
