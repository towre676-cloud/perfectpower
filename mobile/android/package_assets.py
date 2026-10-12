"""Build a deterministic complete Android repository bundle from an explicit Git commit."""
import argparse, hashlib, json, subprocess, tarfile, tempfile, zipfile
from pathlib import Path
BASE=Path(__file__).resolve().parent
ROOT=BASE.parents[1]
def digest(raw):return hashlib.sha256(raw).hexdigest()
def package(root=ROOT,ref='HEAD',ui=None,output=None):
 root=Path(root);ui=Path(ui or BASE/'ui/dist');output=Path(output or BASE/'app/src/main/assets');output.mkdir(parents=True,exist_ok=True)
 snapshot=subprocess.check_output(['git','rev-parse',ref+'^{commit}'],cwd=root,text=True).strip()
 tree=subprocess.check_output(['git','rev-parse',snapshot+'^{tree}'],cwd=root,text=True).strip()
 catalog=json.loads((root/'desktop/explorer/dist/catalog.json').read_text())
 if catalog['commit']!=snapshot:raise ValueError('Generate the catalogue from the selected snapshot first')
 originals={};files={}
 with tempfile.TemporaryFile() as source_tar:
  subprocess.run(['git','archive','--format=tar',snapshot],cwd=root,stdout=source_tar,check=True);source_tar.seek(0)
  with tarfile.open(fileobj=source_tar) as source:
   for member in source:
    if member.isfile():
     raw=source.extractfile(member).read();files[member.name]=raw;originals[member.name]=digest(raw)
 manifest={'snapshot':snapshot,'source_tree':tree,'original_file_count':len(originals),'files':originals}
 manifest_raw=(json.dumps(manifest,sort_keys=True,separators=(',',':'))+'\n').encode();output.joinpath('original-files.json').write_bytes(manifest_raw)
 for path in ui.iterdir():
  if path.is_file():files['desktop/explorer/dist/'+path.name]=path.read_bytes()
 for name in ('mobile.css','mobile-ui.js'):files['desktop/explorer/dist/'+name]=(BASE/name).read_bytes()
 for path in (BASE/'native').rglob('*'):
  if path.is_file():files['mobile-native/'+path.relative_to(BASE/'native').as_posix()]=path.read_bytes()
 files['mobile/ORIGINAL_FILES.json']=manifest_raw
 catalog['mobile']={'original_file_count':len(originals),'source_tree':tree}
 files['desktop/explorer/dist/catalog.json']=json.dumps(catalog,ensure_ascii=False).encode()
 target=output/'repository.zip'
 with zipfile.ZipFile(target,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as archive:
  for name,raw in sorted(files.items()):
   entry=zipfile.ZipInfo(name,date_time=(1980,1,1,0,0,0));entry.compress_type=zipfile.ZIP_DEFLATED;entry.external_attr=0o100644<<16;archive.writestr(entry,raw)
 archive_sha=digest(target.read_bytes());output.joinpath('repository.sha256').write_text(archive_sha+'\n')
 with zipfile.ZipFile(target) as archive:
  if archive.testzip() is not None:raise ValueError('Archive CRC failure')
  for name,expected in originals.items():
   if digest(archive.read(name))!=expected:raise ValueError('Original source bytes changed: '+name)
 return {'snapshot':snapshot,'source_tree':tree,'original_files':len(originals),'original_missing':[],'original_changed':[],'archive_files':len(files),'archive_bytes':target.stat().st_size,'archive_sha256':archive_sha,'commands':len(catalog['commands']),'lean_files':sum(n.endswith('.lean') for n in originals)}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=ROOT);p.add_argument('--ref',default='HEAD');p.add_argument('--ui',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
 report=package(args.root,args.ref,args.ui,args.output);BASE.joinpath('CONTENT_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
