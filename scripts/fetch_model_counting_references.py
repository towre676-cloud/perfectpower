#!/usr/bin/env python3
"""Download pinned upstream reference binaries; do not redistribute them as ours."""
import argparse,hashlib,json,tarfile,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest(path,algorithm='sha256'):
    h=hashlib.new(algorithm)
    with path.open('rb') as stream:
        while block:=stream.read(1024**2):h.update(block)
    return h.hexdigest()
def fetch(url,path):
    if path.exists():return
    part=path.with_suffix('.part')
    with urllib.request.urlopen(url,timeout=60) as response,part.open('wb') as stream:
        while block:=response.read(1024**2):stream.write(block)
    part.replace(path)
def main():
    p=argparse.ArgumentParser();p.add_argument('destination',type=Path);p.add_argument('--solver',choices=['all','ganak','d4'],default='all');args=p.parse_args();args.destination.mkdir(parents=True,exist_ok=True)
    refs=json.loads((ROOT/'data/model_counting/references.json').read_text())
    for name in ['ganak','d4']:
        if args.solver not in ('all',name):continue
        spec=refs[name];archive=args.destination/(name+('.tar.gz' if name=='ganak' else '.tar.xz'))
        fetch(spec['release_url'] if name=='ganak' else spec['archive_url'],archive)
        if digest(archive,'sha256' if name=='ganak' else 'md5')!=spec['archive_sha256' if name=='ganak' else 'archive_md5']:raise ValueError('reference archive differs')
        with tarfile.open(archive,mode='r|*') as t:
            for member in t:
                if member.name!=('ganak' if name=='ganak' else spec['member']):continue
                if not member.isfile():raise ValueError('nonregular reference binary')
                binary=args.destination/name;binary.write_bytes(t.extractfile(member).read());binary.chmod(0o755);break
            else:raise ValueError('reference binary missing')
        if digest(binary)!=spec['binary_sha256']:raise ValueError('reference binary differs')
        print(f'{name}: verified {binary}')
if __name__=='__main__':main()
