"""Coverage of the Thue workload, derived from the registered Lean theorems (not maintained by hand).

The raw workload is `receipts/descent_residual.json` (64 classes without a descent certificate,
189 unit leaves, 109 distinct unit equations) and `receipts/thue_graph.json` (79 classes, 23 open
curves).  This script classifies every class and every unit equation:

* `LOCALLY_DISCHARGED`: the class has a Lean p-adic descent certificate (it has no solution;
  `ThueLocal.descB` / `descM`).
* `CONDITIONALLY_COMPLETE`: a Lean class theorem gives its complete list under named Matveev
  premises.  This holds directly for field 756 (`Generated/Field756.lean`), or through
  solution-carrying descent to registered source equations (`Generated/Minus*.lean`,
  `receipts/minus*_certificate.json`).  The two point-free classes of `D = 72` are covered by
  `D72Residual.residual_empty`.
* `UNRESOLVED`: everything else.

A unit equation is `REGISTERED` when a Lean source theorem (`class_<name>` of a curve
certificate, or `D72Unit.class_pos` / `class_neg` for the `D = 72` residual) proves its complete
list; the match is by GL₂(ℤ)-canonical form.  Curves are
`CONDITIONALLY_COMPLETE` when a Lean curve theorem exists (`minus7`, `minus28`, `minus63`,
`minus18`, `minus23`, `minus45`, `minus89`).

`unit_equations_unregistered` counts every unit equation without a source theorem, including the
leaves of classes already complete by another route.  The workload worth minimizing is
`U_needed`: the union, over UNRESOLVED classes C, of the unit leaves of C that are not registered
(`unit_equations_needed`; each row carries `needed` and the unresolved classes it `blocks`).

Run: python3 python/descent_coverage.py   Writes receipts/descent_coverage.json.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower import thue_graph as TG  # noqa: E402


def main():
    rec = lambda n: json.loads((ROOT / 'receipts' / n).read_text())   # noqa: E731
    graph, resid = rec('thue_graph.json'), rec('descent_residual.json')
    f756 = rec('field756_bound.json')
    certs = sorted((ROOT / 'receipts').glob('minus*_certificate.json'))
    curve_certs = [json.loads(p.read_text()) for p in certs]
    registered = {}
    for c in curve_certs:
        for s in c['sources']:
            key = tuple(TG.canonical(tuple(s['form']))[0])
            registered[key] = {'source': s['name'], 'curve': c['curve'], 'premise': f"matveev_{s['name']}",
                               'list': s['list']}
    d72 = rec('d72_thue_bound.json')        # the D = 72 residual H = ±1: D72Unit.class_pos / class_neg
    for sgn, nm in ((1, 'pos'), (-1, 'neg')):
        key = tuple(TG.canonical(tuple(sgn * x for x in d72['form']))[0])
        registered.setdefault(key, {'source': f'D72Unit.class_{nm}', 'curve': 72, 'premise': 'matveev_pos',
                                    'list': []})
    status, via = {}, {}
    for cl in graph['classes']:
        if 'descent' in cl:
            status[cl['id']] = 'LOCALLY_DISCHARGED'
    for cl in f756['classes']:
        status[cl['class']] = 'CONDITIONALLY_COMPLETE'
        via[cl['class']] = 'Generated/Field756.lean (direct, matveev_{})'.format(cl['class'])
    for cid in (56, 57):          # D = 72's point-free classes: the residual H(u, v) = ±1
        status[cid] = 'CONDITIONALLY_COMPLETE'
        via[cid] = 'D72Residual.residual_empty (matveev_pos)'
    for c in curve_certs:
        for cl in c['classes']:
            status[cl['class']] = 'CONDITIONALLY_COMPLETE'
            via[cl['class']] = f"Generated/Minus{c['curve']}.lean (descent to {', '.join(cl['sources'])})"
    rows = []
    for cl in graph['classes']:
        s = status.get(cl['id'], 'UNRESOLVED')
        rows.append({'class': cl['id'], 'curves': cl['curves'], 'M': cl['M'], 'status': s,
                     'via': via.get(cl['id'])})
    eqs = []
    for u in resid['unit_equations']:
        key = tuple(u['form'])
        r = registered.get(key)
        eqs.append({'form': u['form'], 'classes': u['classes'],
                    'status': 'REGISTERED' if r else 'UNREGISTERED', **({'source': r} if r else {})})
    unresolved = {r['class'] for r in rows if r['status'] == 'UNRESOLVED'}
    needed = [e for e in eqs if e['status'] == 'UNREGISTERED' and unresolved & set(e['classes'])]
    for e in eqs:
        e['needed'] = e in needed
        e['blocks'] = sorted(unresolved & set(e['classes'])) if e['status'] == 'UNREGISTERED' else []
    # how many unresolved classes each needed equation would unblock (a priority order)
    needed_hist = {}
    for e in needed:
        k = str(len(e['blocks']))
        needed_hist[k] = needed_hist.get(k, 0) + 1
    complete_curves = sorted({7, 28, 63} | {c['curve'] for c in curve_certs})
    open_curves = [c['D'] for c in graph['curves'] if c['status'] != 'COMPLETE']
    # per unresolved curve: the unregistered unit equations its unresolved classes descend to
    cls_of = {c['D']: c['classes'] for c in graph['curves']}
    workload = []
    for d in open_curves:
        if d in complete_curves:
            continue
        cs = sorted(set(cls_of[d]) & unresolved)
        eq = [e['form'] for e in needed if set(e['blocks']) & set(cs)]
        workload.append({'D': d, 'unresolved_classes': cs, 'unit_equations_needed': len(eq), 'forms': eq})
    workload.sort(key=lambda w: (w['unit_equations_needed'], w['D']))
    count = lambda s: sum(r['status'] == s for r in rows)   # noqa: E731
    out = {'label': 'DERIVED from registered Lean theorems; the raw workload is descent_residual.json and '
                    'thue_graph.json (unchanged)',
           'classes_total': len(rows),
           'classes_locally_discharged': count('LOCALLY_DISCHARGED'),
           'classes_conditionally_complete': count('CONDITIONALLY_COMPLETE'),
           'classes_unresolved': count('UNRESOLVED'),
           'unit_equations_total': len(eqs),
           'unit_equations_registered': sum(e['status'] == 'REGISTERED' for e in eqs),
           'unit_equations_unregistered': sum(e['status'] == 'UNREGISTERED' for e in eqs),
           'unit_equations_unregistered_note': 'unregistered source equations, including leaves of classes '
                                               'already completed by another route (field 756, D = 72)',
           'unit_equations_needed': len(needed),
           'unit_equations_needed_note': 'U_needed = union over UNRESOLVED classes C of (unit leaves of C minus '
                                         'registered): the workload that still blocks a class',
           'needed_by_class_count': needed_hist,
           'open_curves_raw': len(open_curves),
           'curves_conditionally_complete': complete_curves,
           'curves_unresolved': [d for d in open_curves if d not in complete_curves],
           'curves_unresolved_workload': workload,
           'classes': rows, 'unit_equations': eqs}
    (ROOT / 'receipts' / 'descent_coverage.json').write_text(json.dumps(out, indent=1) + '\n')
    print({k: v for k, v in out.items() if not isinstance(v, list) or k.startswith('curves')})


if __name__ == '__main__':
    main()
