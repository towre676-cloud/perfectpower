#!/usr/bin/env python3
"""Verify byte-exact upstream files and optional package-wide SHA256 manifest."""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

def main():
    rows = json.loads((ROOT/'provenance/upstream.json').read_text())
    for row in rows:
        b = (ROOT/row['local_path']).read_bytes()
        assert len(b) == row['upstream_bytes'], row['local_path']+' length'
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest() == row['git_blob_sha1'], row['local_path']+' git blob'
        assert hashlib.sha256(b).hexdigest() == row['sha256'], row['local_path']+' sha256'
    package = ROOT/'provenance/package_sha256.json'
    n = 0
    if package.exists():
        for path, sha in json.loads(package.read_text()).items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == sha, path+' package hash'
            n += 1
    print(f'PASS: {len(rows)} byte-exact upstream files; {n} package SHA256 entries.')

if __name__ == '__main__':
    main()
