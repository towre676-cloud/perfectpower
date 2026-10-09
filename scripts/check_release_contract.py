"""Reject missing feature checks and ambiguous current frontier declarations."""
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]


def check(root=ROOT):
    features=json.loads((root/'contracts/release_features.json').read_text())
    frontier=json.loads((root/'contracts/current_frontier.json').read_text())
    rows=frontier['findings']
    if [r['id'] for r in rows]!=list(range(1,26)):
        raise ValueError('current frontier must account for each of the 25 findings exactly once')
    for row in rows:
        if row['status'] not in {'open','implemented','mitigated','bounded_route_delivered'}:
            raise ValueError('invalid frontier status')
        if not row['contract'] or not (root/row['evidence']).is_file():
            raise ValueError('frontier evidence missing: '+str(row['id']))
    names=[]
    for feature in features['features']:
        names.append(feature['name'])
        if not feature['tests']:raise ValueError('feature without regression checks')
        for name in feature['files']:
            if not (root/name).is_file():raise ValueError('missing feature source: '+name)
        for name in feature['tests']:
            if not (root/'python/tests'/name).is_file():raise ValueError('missing feature test: '+name)
    if len(set(names))!=len(names):raise ValueError('duplicate release feature')
    return dict(features=len(names),findings=len(rows),
                research_obligations=sum(r['status']=='open' for r in rows))


if __name__=='__main__':print(json.dumps(check(),sort_keys=True))
