#!/usr/bin/env python3
"""Trace competition formulas to named sources by canonical CNF identity.

Declarations of free variables are retained. This matches clause/literal
reordering and duplicates, not arbitrary semantic equivalence or renaming.
Archive members are read without extracting archive-controlled paths.
"""
import argparse
import bz2
import gzip
import hashlib
import io
import json
import lzma
import tarfile
from pathlib import Path


def identity(text):
    n, m, clauses, current = None, None, [], []
    for line in text.splitlines():
        t = line.split()
        if not t or t[0] == 'c':
            continue
        if t[0] == 'p':
            if n is not None or len(t) != 4 or t[1] != 'cnf':
                raise ValueError('CNF header')
            n, m = map(int, t[2:])
            continue
        if t == ['%']:
            break
        for x in map(int, t):
            if x:
                if n is None or abs(x) > n:
                    raise ValueError('literal range')
                current.append(x)
            else:
                clauses.append(tuple(sorted(set(current))))
                current = []
    if n is None or current or len(clauses) != m:
        raise ValueError('CNF dimensions')
    cleaned = set()
    for c in clauses:
        literals = set(c)
        if not any(-x in literals for x in c):
            cleaned.add(c)
    clauses = sorted(cleaned)
    return hashlib.sha256(json.dumps([n, clauses], separators=(',', ':')).encode()).hexdigest()


def stream(raw, name):
    if name.endswith('.xz'):
        return lzma.LZMAFile(io.BytesIO(raw))
    if name.endswith('.gz'):
        return gzip.GzipFile(fileobj=io.BytesIO(raw))
    if name.endswith('.bz2'):
        return bz2.BZ2File(io.BytesIO(raw))
    return io.BytesIO(raw)


def header(raw, name):
    with stream(raw, name) as f:
        prefix = f.read(65536).decode('utf8')
    for line in prefix.splitlines():
        t = line.split()
        if t[:2] == ['p', 'cnf'] and len(t) == 4:
            return tuple(map(int, t[2:]))
    return None


def text(raw, name, cap=8*1024**2):
    with stream(raw, name) as f:
        blob = f.read(cap+1)
    return None if len(blob) > cap else blob.decode('utf8')


def members(archive, prefix='', depth=0):
    """Read nested tar members without writing untrusted paths to disk."""
    if depth > 3:
        raise ValueError('archive nesting limit')
    for member in archive:
        if not member.isfile() or Path(member.name).name.startswith('._'):
            continue
        name = prefix + member.name
        if member.name.endswith(('.tar','.tar.gz','.tgz','.tar.xz')):
            with tarfile.open(fileobj=archive.extractfile(member),mode='r|*') as nested:
                yield from members(nested,name+'!',depth+1)
        elif member.name.endswith(('.cnf','.cnf.xz','.cnf.gz','.cnf.bz2')) or Path(member.name).name.startswith('00_'):
            yield name, archive.extractfile(member).read()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--archive-url', default='https://zenodo.org/records/14969231/files/mc2024-track1-mc_collected.tar')
    p.add_argument('--expected-md5', default='d2976e44c6a678404c01da779cb09007')
    p.add_argument('--mc2024', type=Path, required=True)
    p.add_argument('--mc2025', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--metadata', type=Path, required=True)
    p.add_argument('--known-cache', type=Path)
    a = p.parse_args()
    if a.output.exists():
        raise ValueError('fresh output required')
    known, dimensions = {}, set()
    excluded = []
    if a.known_cache:
        cache = json.loads(a.known_cache.read_text())
        known = cache['known_normalized_hashes']
        excluded = cache['known_byte_limit_exclusions']
    for corpus in (a.mc2024, a.mc2025):
        for f in sorted(corpus.glob('*.cnf')):
            if f.stat().st_size > 8*1024**2:
                excluded.append(f.name)
                continue
            raw = f.read_bytes()
            h = header(raw, f.name)
            dimensions.add(h)
            if not a.known_cache:
                known.setdefault(identity(raw.decode()), []).append(f.name)
    report = {'schema': 'pp-cnf-origin-trace/1',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'archive_sha256': hashlib.sha256(a.archive.read_bytes()).hexdigest(),
              'archive_md5': hashlib.md5(a.archive.read_bytes()).hexdigest(),
              'archive_url': a.archive_url,
              'known_normalized_hashes': known, 'known_byte_limit_exclusions': excluded,
              'index': [], 'matches': [], 'completed': False}
    assert report['archive_md5'] == a.expected_md5
    a.metadata.mkdir(parents=True, exist_ok=True)
    with tarfile.open(a.archive) as archive:
        for name, raw in members(archive):
            if Path(name.split('!')[-1]).name.startswith('00_') and len(raw) < 1024**2:
                blob = raw
                key = hashlib.sha256(name.encode()).hexdigest()[:16]
                dest = a.metadata / (key+'_'+Path(name).name)
                dest.write_bytes(blob)
                report.setdefault('metadata', []).append({'member': name, 'saved_name': dest.name,
                                                         'sha256': hashlib.sha256(blob).hexdigest()})
                continue
            if not name.endswith(('.cnf', '.cnf.xz', '.cnf.gz','.cnf.bz2')):
                continue
            try:
                h = header(raw, name)
            except (ValueError, UnicodeError, EOFError, lzma.LZMAError) as e:
                report.setdefault('parse_exclusions', []).append({'member':name,'reason':str(e)})
                continue
            row = {'member': name, 'header': list(h) if h else None,
                   'compressed_sha256': hashlib.sha256(raw).hexdigest(), 'compressed_bytes': len(raw)}
            report['index'].append(row)
            if h in dimensions:
                try:
                    t = text(raw, name)
                    if t is not None:
                        key = identity(t)
                        if key in known:
                            report['matches'].append(dict(row, normalized_sha256=key,
                                                          competition_names=known[key]))
                            print(name, known[key], flush=True)
                except (ValueError, UnicodeError, EOFError, lzma.LZMAError) as e:
                    report.setdefault('parse_exclusions', []).append({'member':name,'reason':str(e)})
    report['completed'] = True
    a.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
