"""Package and byte-check all committed source files in ordinary ZIP parts."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile
import zlib

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    out = Path(args.output).resolve(); out.mkdir(parents=True, exist_ok=True)
    if subprocess.check_output(['git','status','--porcelain'], cwd=ROOT):
        raise RuntimeError('Commit the source before packaging')
    head = subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip()
    files = subprocess.check_output(['git','ls-files','-z'], cwd=ROOT).decode().split('\0')[:-1]
    manifest = {'schema':'pp-independent-planning-package/1', 'commit':head, 'files':[]}
    paths = []; archive = None; estimated = 0
    try:
        for name in files:
            raw = (ROOT/name).read_bytes()
            manifest['files'].append({'path':'perfectpower/'+name, 'bytes':len(raw), 'sha256':hashlib.sha256(raw).hexdigest()})
            estimate = len(zlib.compress(raw,6))+len(name.encode())*2+200
            if estimate > 24000000:
                raise RuntimeError('One source file exceeds part budget: '+name)
            if archive is None or estimated+estimate > 24000000:
                if archive: archive.close()
                path = out/f'PerfectPower_Independent_Complete_part{len(paths)+1}.zip'
                paths.append(path);archive=zipfile.ZipFile(path,'w',zipfile.ZIP_DEFLATED,compresslevel=6);estimated=0
            info=zipfile.ZipInfo('perfectpower/'+name,date_time=(2026,10,12,0,0,0))
            info.external_attr=(0o100755 if (ROOT/name).stat().st_mode&0o111 else 0o100644)<<16
            archive.writestr(info,raw,compress_type=zipfile.ZIP_DEFLATED,compresslevel=6);estimated+=estimate
    finally:
        if archive: archive.close()
    hashes={}
    for path in paths:
        if path.stat().st_size >= 25000000: raise RuntimeError('Part exceeds budget')
        with zipfile.ZipFile(path) as archive:
            for name in archive.namelist():
                if name in hashes: raise RuntimeError('Duplicate path')
                hashes[name]=hashlib.sha256(archive.read(name)).hexdigest()
    assert len(hashes)==len(files)
    assert all(hashes[r['path']]==r['sha256'] for r in manifest['files'])
    (out/'PACKAGE_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
    monograph=out/'PerfectPower_Independent_Population_Monograph.md'
    monograph.write_bytes((ROOT/'docs/INDEPENDENT_PLANNING_MONOGRAPH.md').read_bytes())
    result={'commit':head,'source_files':len(files),'every_source_byte_checked':True,
            'parts':[{'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths],
            'monograph':str(monograph),'instructions':'Extract all ordinary ZIP parts into the same folder.'}
    (out/'package-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))


if __name__=='__main__':main()
