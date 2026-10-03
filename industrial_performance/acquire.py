"""Acquire the pinned industrial corpus and verify every Git blob."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

REVISION = 'bdae77b0a144895098f82b51a531bc2b566df9e6'
PREFIX = 'incremental/QF_NIA/20260619-elster'
URL = 'https://github.com/SMT-LIB/benchmark-submission.git'


def acquire(destination):
    destination = Path(destination).resolve()
    def git(*args):
        return subprocess.check_output(['git', '-C', str(destination), *args])
    if not destination.exists():
        subprocess.run(['git', 'clone', '--filter=blob:none', '--no-checkout', URL, str(destination)], check=True)
    git('sparse-checkout', 'set', '--cone', PREFIX)
    git('checkout', '--detach', REVISION)
    entries = []
    for line in git('ls-tree', '-r', REVISION, '--', PREFIX).decode().splitlines():
        meta, name = line.split('\t')
        _, kind, expected = meta.split()
        if kind != 'blob' or not name.endswith('.smt2'):
            continue
        data = (destination / name).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if actual != expected:
            raise ValueError(f'Git blob mismatch: {name}')
        entries.append(dict(path=name, bytes=len(data), blob_sha=expected, sha256=hashlib.sha256(data).hexdigest()))
    if len(entries) != 181:
        raise ValueError(f'Expected 181 files, got {len(entries)}')
    manifest = dict(repository=URL, revision=REVISION, prefix=PREFIX, files=entries)
    (destination / 'acquisition.json').write_text(json.dumps(manifest, indent=2) + '\n')
    return manifest


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--destination', required=True)
    args = p.parse_args()
    m = acquire(args.destination)
    print(json.dumps(dict(files=len(m['files']), bytes=sum(f['bytes'] for f in m['files']))))
