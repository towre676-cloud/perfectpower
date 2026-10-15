#!/usr/bin/env python3
"""Complete source/data/replay ZIP from an explicit engine snapshot.

Explicit source allowlists exclude restricted movement tracking. Publication
receipts may be committed after the pinned source snapshot without changing it.
"""
import argparse,hashlib,importlib.util,json,shutil,subprocess,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def sha(raw):return hashlib.sha256(raw).hexdigest()
def package(cache,players,predictions,derived,aggregate,out,ui,ref):
    out.mkdir(parents=True,exist_ok=True)
    spec=importlib.util.spec_from_file_location('mobile_package',ROOT/'mobile/android/package_assets.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    source=module.package(ROOT,ref=ref,ui=ui,output=out/'source_bundle')
    target=out/'PerfectPower_Scouting_Identity_Complete.zip';shutil.copyfile(out/'source_bundle/repository.zip',target)
    sources=json.loads((ROOT/'receipts/scouting_depth/source_audit.json').read_text())['public_sources'];payload={}
    for row in sources:
        p=cache/row['name'];raw=p.read_bytes()
        if sha(raw)!=row['sha256'] or len(raw)!=row['bytes']:raise ValueError('changed public source '+p.name)
        payload['scouting-public-inputs/'+p.name]=raw
    for name in ('acquisition.json','acquisition_depth.json','acquisition_evaluation.json'):payload['scouting-public-inputs/'+name]=(cache/name).read_bytes()
    payload['identity-replay/prospects.pkl']=players.read_bytes()
    for name,path in zip(('target_predictions.pkl','receiving_efficiency_predictions.pkl','pressure_target_predictions.pkl'),predictions):payload['identity-replay/'+name]=path.read_bytes()
    for path in sorted(derived.iterdir()):
        if path.suffix in ('.jsonl','.pkl'):payload['identity-derived/'+path.name]=path.read_bytes()
    for path in sorted(aggregate.glob('*.pkl')):payload['identity-aggregate/'+path.name]=path.read_bytes()
    contents={name:{'bytes':len(raw),'sha256':sha(raw)} for name,raw in payload.items()}
    contents_raw=(json.dumps({'schema':'pp-scouting-identity-package-contents/1','engine_snapshot':source['snapshot'],'source_tree':source['source_tree'],'files':contents,'restricted_movement_tracking_included':False},indent=2)+'\n').encode()
    with zipfile.ZipFile(target,'a',zipfile.ZIP_DEFLATED,compresslevel=6) as archive:
        for name,raw in sorted(payload.items()):
            if name in archive.namelist():raise ValueError('would overwrite source '+name)
            entry=zipfile.ZipInfo(name,date_time=(1980,1,1,0,0,0));entry.compress_type=zipfile.ZIP_DEFLATED;entry.external_attr=0o100644<<16;archive.writestr(entry,raw)
        archive.writestr('SCOUTING_IDENTITY_CONTENTS.json',contents_raw)
    with zipfile.ZipFile(target) as archive:
        if archive.testzip() is not None:raise ValueError('CRC failure')
        originals=json.loads(archive.read('mobile/ORIGINAL_FILES.json'))['files']
        for name,digest in originals.items():
            if sha(archive.read(name))!=digest:raise ValueError('source byte mismatch '+name)
        for name,record in contents.items():
            if sha(archive.read(name))!=record['sha256']:raise ValueError('input byte mismatch '+name)
    receipt={'schema':'pp-scouting-identity-complete-package/1','source_bundle':source,'source_files_verified':len(originals),'added_files_verified':len(contents),'public_archives_verified':len(sources),'archive_bytes':target.stat().st_size,'archive_sha256':sha(target.read_bytes()),'restricted_movement_tracking_included':False,'native_executable_upgrade':False}
    (out/'Scouting_Identity_Package_Receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');shutil.copyfile(ROOT/'docs/SCOUTING_IDENTITY_MONOGRAPH.md',out/'Scouting_Identity_Monograph.md');print(json.dumps(receipt));return receipt
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ('cache','players','derived','aggregate','out','ui'):p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--predictions',type=Path,nargs=3,required=True);p.add_argument('--ref',default='HEAD');a=p.parse_args();package(**vars(a))
