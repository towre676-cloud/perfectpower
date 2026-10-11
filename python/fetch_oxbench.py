#!/usr/bin/env python3
"""Refetch pinned original archive and reproduce byte-identical retained subset."""
import argparse,gzip,hashlib,io,json,tarfile,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];DATA=ROOT/'data/oxbench'
def main():
    p=argparse.ArgumentParser();p.add_argument('--archive',type=Path);a=p.parse_args()
    manifest=json.loads((DATA/'manifest.json').read_text())
    if a.archive:raw=a.archive.read_bytes()
    else:
        with urllib.request.urlopen(manifest['url'],timeout=60) as response:
            raw=response.read(100_000_001)
    if len(raw)>100_000_000 or hashlib.sha256(raw).hexdigest()!=manifest['archive_sha256']:
        raise ValueError('archive exceeds limit or differs from pinned release; existing dataset preserved')
    with tarfile.open(fileobj=io.BytesIO(raw)) as t:
        files={m.name:t.extractfile(m).read() for m in t.getmembers() if m.isfile() and m.name in manifest['files']}
    if {k:hashlib.sha256(v).hexdigest() for k,v in files.items()}!=manifest['files']:
        raise ValueError('retained source inventory differs')
    target=io.BytesIO()
    with gzip.GzipFile(fileobj=target,filename='source.tar',mode='wb',mtime=0) as z:
        with tarfile.open(fileobj=z,mode='w') as t:
            for name,contents in sorted(files.items()):
                m=tarfile.TarInfo(name);m.size=len(contents);t.addfile(m,io.BytesIO(contents))
    if hashlib.sha256(target.getvalue()).hexdigest()!=manifest['retained_sha256']:raise ValueError('subset reconstruction differs')
    (DATA/'source.tar.gz').write_bytes(target.getvalue());print('Pinned complete ox subset reproduced')
if __name__=='__main__':main()
