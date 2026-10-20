#!/usr/bin/env python3
"""Recompute the finite Coxeter proof receipts, shared table and live summary.

Historical deep-period result identities are preserved; the new proofs have
their own source-bound child receipts. This does not update native engines.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'python'))
REGISTRY = 'data/coxeter_research_equations.json'
MONOGRAPH = 'docs/COXETER_RESEARCH_FRONTIERS.md'
SUMMARY = 'receipts/period_bridge_deep/summary.json'
NORMALIZER = 'receipts/period_bridge_deep/trace_normalizer.json'
RECONSTRUCTION = 'receipts/period_bridge_deep/coxeter_reconstruction.json'
SCHEMA = 'pp-coxeter-research-publication/1'


def _sha(raw):
    return hashlib.sha256(raw).hexdigest()


def _encoded(packet):
    return json.dumps(packet, indent=2, sort_keys=True, ensure_ascii=False)+'\n'


def _hashes(root, paths):
    return {p: _sha((root/p).read_bytes()) for p in sorted(paths)}


def _cell(value):
    return str(value).replace('|', '\\|').replace('\n', ' ')


def _monograph(root, registry):
    lines = [
        '# Coxeter research frontiers: arithmetic symmetry and finite recovery', '',
        '**Source-derived proof monograph, '+registry['research_date']+' UTC.**', '',
        'This continuation of the [deep-period monograph](PERIOD_BRIDGE_DEEP_MONOGRAPH.md) '
        'and the [integral Coxeter–Raghava bridge](RAGHAVA_COXETER_UNIFICATION.md) records '
        'two exact mathematical extensions. The arithmetic trace form reconstructs '
        'every integral isometry normalizing the supplied Coxeter cycle: its normalizer '
        'has order 240 and its extension by the eight Galois actions is nonsplit. '
        'The finite positive-moment theorem identifies the folded E₈ reflection spectrum '
        'from mass and eight Raghava moments, without a competitor conductor bound. '
        'An explicit positive rational counterexample proves the eight-coordinate '
        'boundary, and four absolutely convergent odd Mellin observations recover orientation.', '',
        'The shared equation IDs below agree exactly with the [PerfectJet canonical '
        'research registry]('+registry['canonical_registry']+'). Common equations do '
        'not imply that the two packages contain identical executable engines. '
        'The proofs and exact rational replay add no Lean theorem, historical-priority '
        'claim, inference of a Lie bracket from spectra, or identification based on '
        'equal cardinalities.', '', '## Shared equation table', '',
        '| ID | Mathematical statement | Status and precise scope |',
        '|---|---|---|',
    ]
    for row in registry['equations']:
        lines.append('| '+_cell(row['id'])+' | **'+_cell(row['title'])+'**: `'
                     +_cell(row['equation'])+'` | '+_cell(row['status'])+'. '
                     +_cell(row['assumptions'])+' |')
    lines += ['', '## Reproduction and proof boundaries', '',
        'Run `python scripts/export_coxeter_research.py`, then '
        '`python scripts/export_coxeter_research.py --check` to recompute the two '
        'source-bound child receipts, this full proof monograph and the live summary. '
        'The second command requires byte-identical deterministic output. Focused '
        'verification is `PYTHONPATH=python python -m unittest '
        'python/tests/test_coxeter_normalizer.py python/tests/test_coxeter_reconstruction.py -v`.', '',
        'The [normalizer receipt](../'+NORMALIZER+') contains the exact trace form, '
        'all eight lift fibers and the nonsplitting witness. The [spectral receipt]('
        '../'+RECONSTRUCTION+') contains the positive Hankel certificates, complete '
        'sharpness counterexample and oriented reflection and adjoint checks. '
        'Their source hashes and the scoped research block in the summary identify '
        'these fresh computations separately from the historical deep-period '
        '`results_sha256`, result path, source-parent identity and proof statuses.', '',
        'Reflection uses nine even coordinates including mass and four odd coordinates. '
        'Adjoint uses 33 even coordinates including mass and 14 odd coordinates. '
        'The sharpness claim concerns the nine-even-coordinate reflection certificate '
        'among nonnegative rationally weighted profiles. Minimality among actual '
        'dimension-eight integer representations, and minimality of the combined '
        'even-plus-odd scheme, are not established. These spectral observations do '
        'not reconstruct an integral lattice or Lie bracket.', '',
        'The complete proof chapters follow. Equation labels TN1–TN9 and FR1–FR9 '
        'remain local to their respective chapters.', '']
    for path in ('docs/COXETER_TRACE_NORMALIZER.md', 'docs/COXETER_RECONSTRUCTION.md'):
        lines += [(root/path).read_text().rstrip(), '']
    return '\n'.join(lines)


def build(root=ROOT):
    from perfectpower.coxeter_normalizer import receipt as normalizer_receipt
    from perfectpower.coxeter_reconstruction import receipt as reconstruction_receipt
    root = Path(root)
    registry = json.loads((root/REGISTRY).read_text())
    rows = registry.get('equations', [])
    if registry.get('schema') != 'pp-coxeter-research-equations/1':
        raise ValueError('unexpected Coxeter research registry schema')
    if [r['id'] for r in rows] != [f'PJ-E{i}' for i in range(465, 478)]:
        raise ValueError('the thirteen shared equation IDs must be retained')
    digest = _sha(json.dumps(rows, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode())
    if digest != registry['canonical_subset_sha256']:
        raise ValueError('canonical equation subset digest mismatch')
    normalizer, reconstruction = normalizer_receipt(), reconstruction_receipt()
    outputs = {MONOGRAPH: _monograph(root, registry)}
    shared = [REGISTRY, 'scripts/export_coxeter_research.py', 'python/perfectpower/e8_periods.py']
    ns = shared+['python/perfectpower/coxeter_normalizer.py', 'python/perfectpower/exact_linear.py',
                 'python/tests/test_coxeter_normalizer.py', 'scripts/verify_coxeter_normalizer.py',
                 'docs/COXETER_TRACE_NORMALIZER.md']
    rs = shared+['python/perfectpower/coxeter_reconstruction.py', 'python/perfectpower/raghava_coxeter.py',
                 'python/perfectpower/period_transport.py', 'python/tests/test_coxeter_reconstruction.py',
                 'scripts/verify_coxeter_reconstruction.py', 'docs/COXETER_RECONSTRUCTION.md']
    normalizer['source_sha256'], reconstruction['source_sha256'] = _hashes(root, ns), _hashes(root, rs)
    outputs[NORMALIZER], outputs[RECONSTRUCTION] = _encoded(normalizer), _encoded(reconstruction)
    children = {Path(p).name: _sha(outputs[p].encode()) for p in (NORMALIZER, RECONSTRUCTION)}
    summary = json.loads((root/SUMMARY).read_text())
    if summary.get('schema') != 'pp-period-bridge-deep/1':
        raise ValueError('retained deep-period summary required')
    highlights = [
        dict(id='coxeter-finite-positive-recovery', label='Finite spectral recovery',
             value='nine even coordinates; exact positive sharpness',
             detail='Mass and eight Raghava moments certify the folded reflection profile '
                    'without a competitor conductor bound. A positive rational conductor-30 '
                    'profile matches the first eight coordinates. Four odd Mellin traces recover orientation.'),
        dict(id='coxeter-nonsplit-normalizer', label='Arithmetic Coxeter symmetry',
             value='240 integral isometries; nonsplit normalizer',
             detail='The trace form and all eight Galois-lift fibers are recomputed. '
                    'Every lift of exponent 7 has nonidentity fourth power. Classical '
                    'arithmetic framework; no priority or new Lean claim.'),
    ]
    ids = {h['id'] for h in highlights}
    summary['highlights'] = highlights+[h for h in summary.get('highlights', []) if h.get('id') not in ids]
    limits = ['Finite moment completeness requires nonnegative weights and identifies '
              'the folded spectrum, not its integral lattice or Lie bracket.',
              'The sharpness counterexample has rational weights; integer dimension-eight '
              'minimality and minimality of the combined even-plus-odd scheme remain open.',
              'The new trace-form, nonsplit-normalizer and finite-recovery proofs add '
              'no Lean theorem or historical-priority claim.']
    summary['limits'] = list(dict.fromkeys(summary.get('limits', [])+limits))
    summary.setdefault('child_receipts', {}).update(children)
    summary.setdefault('counts', {}).update(coxeter_research_equations=13,
        coxeter_normalizer_order=240, coxeter_centralizer_order=30,
        reflection_finite_even_coordinates=9, reflection_orientation_odd_coordinates=4,
        adjoint_finite_even_coordinates=33, adjoint_orientation_odd_coordinates=14)
    summary['coxeter_research'] = dict(schema=SCHEMA, equations=REGISTRY,
        equation_ids=[r['id'] for r in rows], equation_registry_sha256=_sha((root/REGISTRY).read_bytes()),
        monograph=MONOGRAPH, monograph_sha256=_sha(outputs[MONOGRAPH].encode()),
        preceding_monograph='docs/PERIOD_BRIDGE_DEEP_MONOGRAPH.md', child_receipts=children,
        source_sha256=_hashes(root, set(ns+rs)), formal_kernel_verified=False,
        new_lean_theorems=0, live_data_is_executable_upgrade=False,
        scope='Mathematical proofs and exact finite rational replay. Historical deep-period identities remain separate.')
    outputs[SUMMARY] = _encoded(summary)
    # A dedicated mathematical feed can be published independently of the
    # shared application feed and its unrelated empirical datasets.
    payload = dict(schema='pp-coxeter-research-payload/1', equations=rows,
                   normalizer=normalizer, reconstruction=reconstruction,
                   monograph=MONOGRAPH, monograph_sha256=_sha(outputs[MONOGRAPH].encode()),
                   scope=summary['coxeter_research']['scope'],
                   new_lean_theorems=0, live_data_is_executable_upgrade=False)
    encoded = json.dumps(payload, sort_keys=True, separators=(',', ':'), ensure_ascii=False)
    outputs['data/coxeter_research_live.json'] = _encoded(dict(
        schema='pp-coxeter-research-live/1', payload_json=encoded,
        payload_sha256=_sha(encoded.encode())))
    return outputs


def export(root=ROOT, check=False):
    root, mismatches = Path(root), []
    outputs = build(root)
    for path, content in outputs.items():
        raw, target = content.encode(), root/path
        if check:
            if not target.is_file() or target.read_bytes() != raw:
                mismatches.append(path)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
    if mismatches:
        raise ValueError('research exports differ: '+', '.join(mismatches))
    return dict(schema=SCHEMA, equations=13, normalizer_order=240,
                reflection_even_coordinates=9, monograph=MONOGRAPH,
                monograph_sha256=_sha(outputs[MONOGRAPH].encode()),
                summary_sha256=_sha(outputs[SUMMARY].encode()), check=check)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    print(json.dumps(export(args.root, args.check), sort_keys=True))
