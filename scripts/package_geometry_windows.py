#!/usr/bin/env python3
"""Refresh a complete Windows ZIP from a public runtime seed and pinned engine archive."""
import argparse,hashlib,json,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def digest(raw):return hashlib.sha256(raw).hexdigest()
def package(seed,engine,manifest,output):
 source=json.loads(Path(manifest).read_text());records={};original={}
 def add(archive,name,raw):
  archive.writestr(name,raw);records[name]={'bytes':len(raw),'sha256':digest(raw)}
 with zipfile.ZipFile(seed) as old,zipfile.ZipFile(engine) as source_zip,zipfile.ZipFile(output,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as target:
  for item in old.infolist():
   if item.is_dir() or item.filename.startswith('resources/app/repository/') or item.filename in ('PACKAGE_MANIFEST.json','SOURCE_SNAPSHOT.json','READ-ME.txt','resources/app/package.json'):continue
   add(target,item.filename,old.read(item))
  for item in source_zip.infolist():
   if item.is_dir() or item.filename.startswith('desktop/explorer/dist/') or item.filename.startswith('mobile-native/'):continue
   raw=source_zip.read(item);add(target,'resources/app/repository/'+item.filename,raw)
   if item.filename in source['files']:original[item.filename]=digest(raw)
  for path in (ROOT/'desktop/explorer/dist').iterdir():
   if path.is_file():add(target,'resources/app/repository/desktop/explorer/dist/'+path.name,path.read_bytes())
  add(target,'resources/app/package.json',json.dumps({'name':'perfectpower-explorer','version':'1.3.0','main':'main.cjs'}).encode())
  add(target,'READ-ME.txt',b'PerfectPower Explorer 1.3 - Geometric Observatory\n\nExtract the entire ZIP and open PerfectPower-Explorer.exe.\nThe original Windows runtime is preserved. Saved runs use the same application identity and private state directory.\nFresh numerical queries run locally; geometric views follow their exact results.\nWindows machine execution has not been exercised in this build environment.\n')
  add(target,'SOURCE_SNAPSHOT.json',json.dumps({'commit':source['snapshot'],'source_tree':source['source_tree'],'original_source_files':len(original),'original_source_bytes_verified':original==source['files']},indent=2).encode())
  assert original==source['files'],'Original source bytes changed or missing'
  target.writestr('PACKAGE_MANIFEST.json',json.dumps(records,sort_keys=True,indent=2))
 with zipfile.ZipFile(output) as check:assert check.testzip() is None
 return {'engine_snapshot':source['snapshot'],'original_source_files':len(original),'original_source_bytes':'all identical','files':len(records),'zip_bytes':Path(output).stat().st_size,'zip_sha256':digest(Path(output).read_bytes()),'runtime_seed_sha256':digest(Path(seed).read_bytes()),'native_windows_execution':'not exercised'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--seed',type=Path,required=True);p.add_argument('--engine',type=Path,required=True);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=package(a.seed,a.engine,a.manifest,a.output);(ROOT/'receipts/planning/explorer/geometry-windows.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
