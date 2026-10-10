#!/usr/bin/env python3
"""Fetch the entire pinned Track 1 corpus, without trusting tar extraction paths."""
import argparse,hashlib,json,lzma,tarfile,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
    p=argparse.ArgumentParser();p.add_argument('destination',type=Path);p.add_argument('--archive',type=Path);args=p.parse_args()
    manifest=json.loads((ROOT/'data/model_counting/manifest.json').read_text());args.destination.mkdir(parents=True,exist_ok=True)
    archive=args.archive or args.destination/'mc2024-track1.tar'
    if not archive.exists():
        part=archive.with_suffix('.part')
        with urllib.request.urlopen(manifest['archive_url'],timeout=60) as response,part.open('wb') as out:
            while block:=response.read(1024**2):out.write(block)
        part.replace(archive)
    if hashlib.sha256(archive.read_bytes()).hexdigest()!=manifest['archive_sha256']:raise ValueError('competition archive hash differs')
    expected={r['name']+'.xz':r for r in manifest['instances']};seen=set()
    with tarfile.open(archive) as entries:
        for entry in entries:
            name=Path(entry.name).name
            if name not in expected:continue
            if not entry.isfile() or name in seen:raise ValueError('duplicate/nonregular corpus member')
            row=expected[name];compressed=entries.extractfile(entry).read()
            if hashlib.sha256(compressed).hexdigest()!=row['compressed_sha256']:raise ValueError('compressed instance differs')
            raw=lzma.decompress(compressed)
            if hashlib.sha256(raw).hexdigest()!=row['sha256'] or hashlib.sha1(raw).hexdigest()!=row['source_sha1']:raise ValueError('instance differs')
            (args.destination/row['name']).write_bytes(raw);seen.add(name)
    if seen!=set(expected):raise ValueError('incomplete corpus')
    print(f'Verified all {len(seen)} original instances in {args.destination}')
if __name__=='__main__':main()
