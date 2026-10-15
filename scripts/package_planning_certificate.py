"""Publish a complete explicit Git snapshot plus the full checked trace.
Every packaged source byte and the compressed trace are checked after writing.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile
ROOT=Path(__file__).resolve().parents[1]


def stream_hash(stream):
    h=hashlib.sha256()
    for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
    return h.hexdigest()


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    if subprocess.check_output(['git','status','--porcelain'],cwd=ROOT):raise RuntimeError('Commit source before packaging')
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    receipt=json.loads((ROOT/'receipts/planning/independent/certificate50.json').read_text())
    with args.certificate.open('rb') as f:certificate_hash=stream_hash(f)
    if certificate_hash!=receipt['certificate_sha256']:raise RuntimeError('Certificate does not match checked receipt')
    files=subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0')[:-1]
    entries=[]
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(args.output,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6,allowZip64=True) as archive:
        for name in files:
            raw=(ROOT/name).read_bytes();target='perfectpower/'+name
            archive.writestr(target,raw)
            entries.append({'path':target,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
        target='perfectpower/certs/planning/petersen50.trace.xz'
        archive.write(args.certificate,target,compress_type=zipfile.ZIP_STORED)
        entries.append({'path':target,'bytes':args.certificate.stat().st_size,'sha256':certificate_hash})
        manifest={'schema':'pp-planning-certificate-package/1','commit':head,'entries':entries,
                  'uncompressed_trace_sha256':receipt['uncompressed_sha256'],
                  'full_unrestricted_population_kernel_proved':False}
        archive.writestr('PACKAGE_MANIFEST.json',json.dumps(manifest,indent=2)+'\n')
    with zipfile.ZipFile(args.output) as archive:
        if set(archive.namelist())!={x['path'] for x in entries}|{'PACKAGE_MANIFEST.json'}:raise RuntimeError('Archive file set mismatch')
        for entry in entries:
            with archive.open(entry['path']) as f:
                if stream_hash(f)!=entry['sha256']:raise RuntimeError('Archive byte mismatch: '+entry['path'])
    with args.output.open('rb') as f:archive_hash=stream_hash(f)
    result={'schema':'pp-planning-certificate-package-result/1','commit':head,'source_files':len(files),
            'every_source_byte_and_full_compressed_trace_checked':True,'bytes':args.output.stat().st_size,
            'sha256':archive_hash,'file':str(args.output.resolve()),
            'full_unrestricted_population_kernel_proved':False}
    args.output.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
