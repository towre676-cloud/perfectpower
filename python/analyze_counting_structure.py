#!/usr/bin/env python3
"""Describe structural strata without substituting them for full-corpus scores."""
import argparse
import collections
import hashlib
import json
import statistics
from pathlib import Path


def analyze(profiles, receipt):
    if not profiles['completed'] or not receipt['completed']:
        raise ValueError('completed inputs required')
    ix = {r['name']: r for r in profiles['results']}
    if set(ix) != set(receipt['instances']):
        raise ValueError('complete profile scope required')
    groups = collections.defaultdict(list)
    for row in receipt['results']:
        p = ix[row['name']]
        if p['sha256'] != row['sha256']:
            raise ValueError('input identities differ')
        label = ('accepted' if p.get('all_components_accepted') else
                 'rejected' if p.get('graph_status') == 'PROFILED' else 'limited')
        groups[label].append(row)
    result = {}
    for label, rows in sorted(groups.items()):
        stats = {}
        for solver in receipt['solver_scope']:
            values = [r['solvers'][solver] for r in rows]
            stats[solver] = {'exact_queries': sum(v['status']=='EXACT' for v in values),
                             'total_queries':len(values),
                             'par2_seconds':sum(v['seconds'] if v['status']=='EXACT' else 2*receipt['timeout_seconds'] for v in values)}
        result[label] = {'instances':len({r['name'] for r in rows}), 'solvers':stats}
    return result


def fresh_analysis(selection, receipt):
    if not selection['completed'] or not receipt['completed']:
        raise ValueError('completed inputs required')
    labels = {r['name']:r for r in selection['selected']}
    if set(receipt['instances']) - set(labels):
        raise ValueError('unknown selected case')
    by_name = collections.defaultdict(list)
    for row in receipt['results']:
        if row['sha256'] != labels[row['name']]['sha256']:
            raise ValueError('input identity differs')
        by_name[row['name']].append(row)
    groups = collections.defaultdict(list)
    cases = []
    for name, rows in sorted(by_name.items()):
        info = labels[name]
        medians = {}
        for solver in receipt['solver_scope']:
            values = [r['solvers'][solver] for r in rows]
            exact = sum(v['status']=='EXACT' for v in values)
            medians[solver] = {'exact_trials':exact, 'total_trials':len(values),
                               'median_seconds':statistics.median(v['seconds'] for v in values),
                               'all_trials_exact':exact==len(values)}
        ratios = {}
        pp = medians['perfectpower']
        for solver in receipt['solver_scope']:
            if solver=='perfectpower' or not pp['all_trials_exact']:
                continue
            ref=medians[solver]
            if ref['all_trials_exact']:
                ratios[solver]={'type':'measured_ratio','value':ref['median_seconds']/pp['median_seconds']}
            elif ref['exact_trials']==0:
                ratios[solver]={'type':'deadline_lower_bound','value':receipt['timeout_seconds']/pp['median_seconds']}
            else:
                ratios[solver]={'type':'mixed_completed_and_censored','value':None}
        item={'name':name,'family':info['family'],'group':info['status'],
              'medians':medians,'ratios':ratios}
        cases.append(item)
        groups[info['status']].extend(rows)
    strata={}
    for label, rows in groups.items():
        strata[label]={'instances':len({r['name'] for r in rows}), 'queries':len(rows), 'solvers':{}}
        for solver in receipt['solver_scope']:
            values=[r['solvers'][solver] for r in rows]
            strata[label]['solvers'][solver]={'exact_queries':sum(v['status']=='EXACT' for v in values),
                                            'par2_seconds':sum(v['seconds'] if v['status']=='EXACT' else 2*receipt['timeout_seconds'] for v in values)}
    return {'strata':strata,'cases':cases,
            'scope':'Structurally selected known-family extensions; no independent all-corpus or unseen-family ranking'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profiles',type=Path)
    p.add_argument('--selection',type=Path)
    p.add_argument('--receipt',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if bool(a.profiles)==bool(a.selection):
        p.error('exactly one of profiles or selection required')
    source=a.profiles or a.selection
    receipt=json.loads(a.receipt.read_text());data=json.loads(source.read_text())
    report={'schema':'pp-cnf-structural-strata/1',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'profile_or_selection_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'receipt_sha256':hashlib.sha256(a.receipt.read_bytes()).hexdigest(),
            'analysis':analyze(data,receipt) if a.profiles else fresh_analysis(data,receipt)}
    a.output.write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':
    main()
