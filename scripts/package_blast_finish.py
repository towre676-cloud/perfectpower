#!/usr/bin/env python3
"""Package the complete committed checkout as ordinary ZIPs below 25 MiB."""
import argparse
from hashlib import sha256
import html
import json
from pathlib import Path
import re
import subprocess
import zipfile
import zlib

ROOT=Path(__file__).resolve().parents[1]

def render_markdown(text):
    # Dependency-free rendering for these prose monographs. Code remains literal.
    sections=[]
    for block in re.split(r'\n\s*\n',text.strip()):
        escaped=html.escape(block)
        if block.startswith('#'):
            line=block.split('\n')[0];n=len(line)-len(line.lstrip('#'))
            sections.append(f'<h{min(n,4)}>{html.escape(line[n:].strip())}</h{min(n,4)}>')
        else:
            escaped=re.sub(r'`([^`]+)`',r'<code>\1</code>',escaped)
            sections.append('<p>'+escaped.replace('\n',' ')+'</p>')
    return '\n'.join(sections)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',required=True)
    args=parser.parse_args();out=Path(args.output).resolve();out.mkdir(parents=True,exist_ok=True)
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    files=subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0')[:-1]
    if subprocess.check_output(['git','status','--porcelain'],cwd=ROOT):raise RuntimeError('Commit the source snapshot before packaging')
    rows=[]
    for name in files:
        raw=(ROOT/name).read_bytes();rows.append({'path':'perfectpower/'+name,'sha256':sha256(raw).hexdigest(),'bytes':len(raw)})
    manifest={'schema':'pp-blast-complete-package/1','head':head,'base':'367147ef8931ce77648da553adcebc2e62d291d4','files':rows,'instructions':'Extract all ZIP parts into the same parent directory. No toolchains or build caches included. Git bundle needs the published base commit.'}
    (out/'PACKAGE_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    bundle=out/'BLAST_PENDING.bundle'
    subprocess.run(['git','bundle','create',str(bundle),'HEAD','^367147ef8931ce77648da553adcebc2e62d291d4'],cwd=ROOT,check=True)
    subprocess.run(['git','bundle','verify',str(bundle)],cwd=ROOT,check=True,capture_output=True)
    text='\n\n'.join((ROOT/'docs'/name).read_text() for name in ['BLAST_FINISH_RELEASE.md','BLAST_CERTIFICATION_MONOGRAPH.md','BLAST_OXBENCH_MONOGRAPH.md'])
    publication=json.loads((ROOT/'receipts/blast/finish/publication.json').read_text())
    status=('The BLAST code and evidence are published on GitHub at '+html.escape(publication['published_code_commit'])+'.' if publication['published'] else 'GitHub publication was pending at this source snapshot; see the publication receipt for the observed status.')
    page='<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>PerfectPower BLAST completion monograph</title><style>body{background:#f5f3ef;color:#192b3b;font:18px/1.7 system-ui;margin:0}main{max-width:900px;margin:0 auto;padding:48px 24px}h1,h2,h3{line-height:1.2;margin-top:2em}h1{font-size:2.2em}code{font-size:.86em;background:#e6e9ec;padding:2px 5px;overflow-wrap:anywhere}p{overflow-wrap:anywhere}.status{padding:20px;background:#fff;border-left:5px solid #b76a28}@media print{body{background:white;font-size:11pt}main{padding:0}h1{break-before:page}}</style><main><p class="status"><strong>Local release '+head[:12]+'</strong>. Validation is complete. '+status+' This document separates executable replay, literal kernel acceptance, biological evaluation and publication status.</p>'+render_markdown(text)+'</main></html>'
    monograph=out/'PerfectPower_BLAST_Completion_Monograph.html';monograph.write_text(page)
    recovery=out/'RECOVERY.txt';recovery.write_text('Extract every ZIP into the same parent directory to reconstruct perfectpower/.\nThe SHA-256 inventory is PACKAGE_MANIFEST.json.\nTo recover the committed history in a clone containing published base 367147e:\n  git bundle verify BLAST_PENDING.bundle\n  git fetch BLAST_PENDING.bundle HEAD:codex/blast-finish-recovered\n  git switch codex/blast-finish-recovered\nPublication destination: towre676-cloud/perfectpower, codex/blast-mining-machinery-20261011.\nInspect the current remote head before publishing; never overwrite a concurrent update.\n')
    extras=[(p.name,p.read_bytes()) for p in [bundle,monograph,recovery,out/'PACKAGE_MANIFEST.json']]
    entries=[(r['path'],(ROOT/r['path'].removeprefix('perfectpower/')).read_bytes()) for r in rows]+extras
    part=1;estimated=0;archive=None;paths=[]
    try:
        for name,raw in entries:
            size=len(zlib.compress(raw,6))+len(name.encode())*2+160
            if size>24_000_000:raise RuntimeError('A single entry exceeds the part budget: '+name)
            if archive is None or estimated+size>24_000_000:
                if archive:archive.close()
                path=out/f'PerfectPower_BLAST_Complete_part{part}.zip';part+=1;paths.append(path)
                archive=zipfile.ZipFile(path,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6);estimated=0
            info=zipfile.ZipInfo(name,date_time=(2026,10,11,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED
            if name.startswith('perfectpower/') and (ROOT/name.removeprefix('perfectpower/')).stat().st_mode&0o111:info.external_attr=0o100755<<16
            else:info.external_attr=0o100644<<16
            archive.writestr(info,raw,compress_type=zipfile.ZIP_DEFLATED,compresslevel=6);estimated+=size
    finally:
        if archive:archive.close()
    actual={}
    for path in paths:
        if path.stat().st_size>=25_000_000:raise RuntimeError('ZIP exceeds budget')
        with zipfile.ZipFile(path) as archive:
            if archive.testzip() is not None:raise RuntimeError('ZIP CRC failure')
            for name in archive.namelist():
                if name in actual:raise RuntimeError('Duplicate archived path')
                actual[name]=sha256(archive.read(name)).hexdigest()
    if any(actual.get(r['path'])!=r['sha256'] for r in rows):raise RuntimeError('Source package differs from manifest')
    result={'head':head,'files':len(rows),'parts':[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha256(p.read_bytes()).hexdigest()} for p in paths],'monograph':str(monograph),'all_file_hashes_checked':True,'bundle_verified':True}
    (out/'package-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
