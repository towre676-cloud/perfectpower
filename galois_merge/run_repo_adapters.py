"""Run the package's two adapters on this repository's real data (not the package's synthetic inputs).

* branch adapter: the 316 actual Thue obligations of `receipts/thue_graph.json` (form, rhs, and,
  in the restricted run, the readout restriction (D, k, p, q)).  Bounded matrix search (entries
  |.| <= height), every edge rechecked exactly by the package's own `check_transport`.
* corpus adapter: the committed unmodified `.seq` files in `data/oeis/`.

The result is compared with the repository's 79 computed GL_2(Z) classes: every bounded edge must
stay inside one class.  This is a **consistency check**, not a proof that the classes are
complete: the adapter searches small matrices only, and the repository's inequivalence claim
rests on the classical reduction theory of binary cubic forms, which is not formalized here.

Run: python3 galois_merge/run_repo_adapters.py   (about 10 s)
Writes receipts/galois_adapters.json.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE / 'src'))
from arithmetic import check_transport, discover_edges, intern_obligations, match_shift, parse_seq  # noqa: E402


def nodes(restricted):
    g = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    rows = []
    for c in g['classes']:
        for m in c['members']:
            rows.append({'form': m['F'], 'rhs': c['M'],
                         'restrictions': {'readout': [m['D'], m['k'], m['p'], m['q']]} if restricted else {},
                         'my_class': c['id']})
    return rows, len(g['classes'])


def components(n, edges):
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for e in edges:
        parent[find(e['source_index'])] = find(e['target_index'])
    return len({find(i) for i in range(n)})


def main():
    rows, nclasses = nodes(False)
    edges = discover_edges(rows, 2)
    assert all(check_transport(e['certificate']) for e in edges)
    crossing = [e for e in edges if rows[e['source_index']]['my_class'] != rows[e['target_index']]['my_class']]
    rrows, _ = nodes(True)
    redges = discover_edges(rrows, 2)
    seq = []
    for p in sorted((ROOT / 'data' / 'oeis').rglob('*.seq')):
        e = parse_seq(p.read_text())
        s = match_shift(e, 20)
        if s:
            seq.append({'id': e['id'], 'offset': e['offset'], 'B_index_shifts': s,
                        'status': 'finite_term_agreement_only'})
    nseq = len(list((ROOT / 'data' / 'oeis').rglob('*.seq')))
    out = {
        'label': 'EXTERNAL package adapters (galois_merge) on the repository data; bounded search, exact edge checks',
        'branch_adapter': {
            'obligations': len(rows), 'height': 2, 'edges_found': len(edges),
            'edges_crossing_repo_classes': len(crossing),
            'components_from_edges': components(len(rows), edges), 'repo_classes': nclasses,
            'exact_unique_obligations': intern_obligations(rows)['unique_count'],
            'restricted_run_edges': len(redges),
            'restricted_note': 'the adapter refuses unrestricted maps between restricted nodes; restrictions '
                               'pull back along T (PerfectPower.Interfaces.restricted_transport)',
            'global_canonicalization_claim': False},
        'corpus_adapter': {'seq_files': nseq, 'B_index_matches': seq, 'promotion_allowed': False},
    }
    (ROOT / 'receipts' / 'galois_adapters.json').write_text(json.dumps(out, indent=1) + '\n')
    b = out['branch_adapter']
    print(f"branch adapter: {b['edges_found']} edges, {b['edges_crossing_repo_classes']} cross repo classes, "
          f"{b['components_from_edges']} components vs {nclasses} classes; restricted edges {b['restricted_run_edges']}")
    print(f"corpus adapter: {nseq} .seq files, B-index matches {[(m['id'], m['B_index_shifts']) for m in seq]}")
    if crossing or b['components_from_edges'] != nclasses:
        raise SystemExit('adapter disagrees with the repository classes')


if __name__ == '__main__':
    main()
