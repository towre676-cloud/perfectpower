#!/usr/bin/env python3
"""Fetch omitted ELSTER files from pinned Git blobs on a network-enabled machine."""
import argparse
import base64
import hashlib
import json
import os
import pathlib
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parents[1]

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir',type=pathlib.Path,default=ROOT/'expanded_elster')
    p.add_argument('--limit',type=int,default=0,help='0 means all omitted files')
    a = p.parse_args()
    if a.limit < 0:
        p.error('limit must be nonnegative')
    full = json.loads((ROOT/'provenance/elster_full_index.json').read_text())
    bundled = json.loads((ROOT/'provenance/upstream.json').read_text())
    selected = {r['upstream_path'] for r in bundled if r['repository']=='SMT-LIB/benchmark-submission'}
    remaining = sorted((r for r in full if r['upstream_path'] not in selected),key=lambda r:r['upstream_path'])
    if a.limit:
        remaining = remaining[:a.limit]
    headers = {'Accept':'application/vnd.github+json','User-Agent':'perfectpower-independent-nia-handoff'}
    token = os.environ.get('GITHUB_TOKEN')
    if token:
        headers['Authorization'] = 'Bearer '+token
    for row in remaining:
        url = 'https://api.github.com/repos/SMT-LIB/benchmark-submission/git/blobs/'+row['git_blob_sha1']
        request = urllib.request.Request(url,headers=headers)
        with urllib.request.urlopen(request,timeout=60) as response:
            blob = json.load(response)
        if blob.get('encoding') != 'base64':
            raise RuntimeError('Unexpected blob encoding')
        b = base64.b64decode(blob['content'])
        assert len(b)==row['upstream_bytes'],row['upstream_path']+' length'
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob_sha1'],row['upstream_path']+' hash'
        dest = a.output_dir/row['upstream_path']
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(b)
        print(row['upstream_path'],len(b),flush=True)
    print('Fetched',len(remaining),'omitted files. Keep this expanded set separate from the sealed handoff.')

if __name__ == '__main__':
    main()
