#!/usr/bin/env python3
"""Select fresh family extensions using frozen structural rules, never timings."""
import argparse
import hashlib
import json
import tarfile
from collections import defaultdict
from pathlib import Path
from profile_counting_structure import profile
from trace_counting_origins import identity, text, members, header
from perfectpower.model_counting import CNF

ROOT = Path(__file__).resolve().parent.parent
SEEDS = {f'mc2025_track1_{i:03}.cnf' for i in (43,69,71,73,74)} | {
    f'mc2024_track1_{i:03}.cnf' for i in (10,13,54,85,86,90,91,96)}


def family(member):
    return member.split('/')[1].split('!')[0]


def round_robin(rows, cap):
    grouped = defaultdict(list)
    for row in rows:
        grouped[row['family']].append(row)
    for values in grouped.values():
        values.sort(key=lambda r: (r['sha256'], r['member']))
    selected = []
    while len(selected) < cap:
        added = False
        for key in sorted(grouped):
            if grouped[key] and len(selected) < cap:
                selected.append(grouped[key].pop(0))
                added = True
        if not added:
            break
    return selected


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--origins', type=Path, required=True)
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--corpus', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--selection', type=Path, required=True)
    a = p.parse_args()
    if a.output.exists() or a.selection.exists():
        raise ValueError('fresh outputs required')
    origins = json.loads(a.origins.read_text())
    families = {family(r['member']) for r in origins['matches'] if SEEDS & set(r['competition_names'])}
    resolved = {n for r in origins['matches'] for n in r['competition_names']} & SEEDS
    known = set(origins['known_normalized_hashes'])
    oversized_n = set()
    for file in ('manifest.json', 'mc2025_manifest.json'):
        for r in json.loads((ROOT/'data/model_counting'/file).read_text())['instances']:
            if r['name'] in origins['known_byte_limit_exclusions']:
                oversized_n.add(int(r['header'].split()[2]))
    selection = {'schema': 'pp-cnf-advantage-selection/1',
                 'protocol_sha256': hashlib.sha256((ROOT/'docs/MODEL_COUNTING_ADVANTAGE_PROTOCOL.md').read_bytes()).hexdigest(),
                 'source_identities': {name: hashlib.sha256((ROOT/'python'/name).read_bytes()).hexdigest()
                                       for name in ('select_counting_advantage.py','trace_counting_origins.py','profile_counting_structure.py')},
                 'counter_sha256': hashlib.sha256((ROOT/'native/model_counting/counter.cpp').read_bytes()).hexdigest(),
                 'origins_sha256': hashlib.sha256(a.origins.read_bytes()).hexdigest(),
                 'families': sorted(families), 'resolved_seeds': sorted(resolved),
                 'unresolved_seeds': sorted(SEEDS-resolved), 'inventory': [], 'selected': [], 'completed': False}
    candidates, normalized_seen = [], set()
    a.corpus.mkdir(parents=True, exist_ok=True)
    with tarfile.open(a.archive) as archive:
        for name, raw in members(archive):
            if not name.endswith(('.cnf','.cnf.xz','.cnf.gz','.cnf.bz2')) or family(name) not in families:
                continue
            row = {'member': name, 'family': family(name)}
            t = text(raw, name)
            row['compressed_sha256'] = hashlib.sha256(raw).hexdigest()
            if t is None:
                row['status'] = 'BYTE_PROFILE_LIMIT'
            else:
                row['sha256'] = hashlib.sha256(t.encode()).hexdigest()
                try:
                    formula = CNF.parse(t)
                    key = identity(t)
                    row['normalized_sha256'] = key
                    if key in known:
                        row['status'] = 'KNOWN_NORMALIZED_MATCH'
                    elif formula.variables in oversized_n:
                        row['status'] = 'CONSERVATIVE_KNOWN_UNNORMALIZED_UNIVERSE_EXCLUSION'
                    elif key in normalized_seen:
                        row['status'] = 'COLLECTION_NORMALIZED_DUPLICATE'
                    else:
                        normalized_seen.add(key)
                        metrics = profile(t)
                        row['profile'] = metrics
                        if metrics.get('unit_contradiction'):
                            row['status'] = 'UNIT_CONTRADICTION'
                        elif metrics.get('all_components_accepted') and metrics.get('largest_component',0)>256:
                            row['status'] = 'PREDICTED_TRACTABLE'
                        elif metrics.get('graph_status')=='PROFILED' and not metrics.get('all_components_accepted'):
                            row['status'] = 'REJECTED_CONTROL'
                        else:
                            row['status'] = 'OUTSIDE_SELECTION_RULE'
                        if row['status'] in ('PREDICTED_TRACTABLE','REJECTED_CONTROL'):
                            candidates.append(row)
                except (ValueError, RuntimeError) as e:
                    row['status'] = 'INPUT_UNSUPPORTED'
                    row['reason'] = str(e)
            selection['inventory'].append(row)
            if len(selection['inventory']) % 50 == 0:
                print('profiled', len(selection['inventory']), 'candidates', len(candidates), flush=True)
    selected = round_robin([r for r in candidates if r['status']=='PREDICTED_TRACTABLE'],24) + round_robin([r for r in candidates if r['status']=='REJECTED_CONTROL'],12)
    by_member = {r['member']:r for r in selected}
    manifest = {'schema':'pp-mc-corpus/1', 'dataset':'Structurally selected fresh MC2024 collected-family extensions',
                'archive_url':origins['archive_url'], 'archive_sha256':origins['archive_sha256'],
                'selection':'Frozen structural labels, family round robin and SHA256 order before timing; known-family extension, not blind family holdout',
                'instances':[]}
    with tarfile.open(a.archive) as archive:
        for member_name, raw in members(archive):
            if member_name not in by_member:
                continue
            row = by_member[member_name]
            t = text(raw, member_name)
            assert hashlib.sha256(t.encode()).hexdigest()==row['sha256']
            name = f'advantage_fresh_{selected.index(row):03}.cnf'
            (a.corpus/name).write_text(t)
            dimensions = header(raw, member_name)
            manifest['instances'].append({'name':name,'sha256':row['sha256'],'bytes':len(t.encode()),
                                          'header':f'p cnf {dimensions[0]} {dimensions[1]}',
                                          'source_member':member_name, 'family':row['family'],
                                          'structural_group':row['status'], 'normalized_sha256':row['normalized_sha256']})
            selection['selected'].append(dict(row, name=name))
    manifest['instances'].sort(key=lambda r:r['name'])
    selection['selected'].sort(key=lambda r:r['name'])
    selection['completed'] = True
    selection['selected_group_counts'] = {label:sum(r['status']==label for r in selected)
                                          for label in ('PREDICTED_TRACTABLE','REJECTED_CONTROL')}
    a.output.write_text(json.dumps(manifest,indent=2)+'\n')
    selection['manifest_sha256'] = hashlib.sha256(a.output.read_bytes()).hexdigest()
    a.selection.write_text(json.dumps(selection,indent=2)+'\n')
    print(selection['selected_group_counts'], flush=True)


if __name__=='__main__':
    main()
