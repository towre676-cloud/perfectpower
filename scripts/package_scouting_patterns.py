#!/usr/bin/env python3
"""Complete pattern release on top of the full source and frozen-data package."""
import argparse,hashlib,json,shutil,zipfile
from pathlib import Path
from package_scouting_identity import package as base_package
ROOT=Path(__file__).resolve().parents[1]
def sha(raw):return hashlib.sha256(raw).hexdigest()
def package(patterns,**options):
    out=options['out'];out.mkdir(parents=True,exist_ok=True)
    base_options=dict(options);base_options['out']=out/'identity_base';base=base_package(**base_options)
    target=out/'PerfectPower_Scouting_Patterns_Complete.zip';shutil.copyfile(base_options['out']/'PerfectPower_Scouting_Identity_Complete.zip',target)
    entries={}
    with zipfile.ZipFile(target,'a',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        for p in sorted(patterns.iterdir()):
            if p.suffix not in ('.pkl','.jsonl'):continue
            raw=p.read_bytes();name='patterns-derived/'+p.name
            if name in z.namelist():raise ValueError('duplicate pattern member')
            z.writestr(name,raw);entries[name]={'sha256':sha(raw),'bytes':len(raw)}
        z.writestr('SCOUTING_PATTERNS_CONTENTS.json',json.dumps(entries,indent=2)+'\n')
    with zipfile.ZipFile(target) as z:
        if z.testzip() is not None:raise ValueError('CRC failure')
        originals=json.loads(z.read('mobile/ORIGINAL_FILES.json'))['files']
        for name,digest in originals.items():
            if sha(z.read(name))!=digest:raise ValueError('source byte mismatch '+name)
        for name,entry in entries.items():
            if sha(z.read(name))!=entry['sha256']:raise ValueError('pattern byte mismatch '+name)
    receipt={'schema':'pp-scouting-patterns-complete-package/1','engine_snapshot':base['source_bundle']['snapshot'],'source_tree':base['source_bundle']['source_tree'],'original_files_verified':len(originals),
      'public_archives_verified':base['public_archives_verified'],'base_replay_files_verified':base['added_files_verified'],'pattern_outputs_verified':entries,
      'archive_bytes':target.stat().st_size,'archive_sha256':sha(target.read_bytes()),'restricted_movement_rows_included':False,'native_executable_upgrade':False}
    (out/'Scouting_Patterns_Package_Receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    shutil.copyfile(ROOT/'docs/SCOUTING_PATTERNS_MONOGRAPH.md',out/'Scouting_Patterns_Monograph.md');print(json.dumps(receipt));return receipt
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('cache','players','derived','aggregate','patterns','out','ui'):p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--predictions',nargs=3,type=Path,required=True);p.add_argument('--ref',default='HEAD');package(**vars(p.parse_args()))
