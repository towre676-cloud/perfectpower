"""Keep original repository bytes, with generated Android interface and native overlays."""
from pathlib import Path
import hashlib,json,zipfile,shutil
BASE=Path(__file__).resolve().parent
RELEASE=BASE.parent/'recovered/PerfectPower-Explorer-Complete.zip'
PREFIX='resources/app/repository/'
assets=BASE/'app/src/main/assets';assets.mkdir(parents=True,exist_ok=True)
def digest(b):return hashlib.sha256(b).hexdigest()
with zipfile.ZipFile(RELEASE) as original:
    records={n[len(PREFIX):]:original.read(n) for n in original.namelist() if n.startswith(PREFIX) and not n.endswith('/')}
    tracked={n:digest(b) for n,b in records.items() if not n.startswith('desktop/explorer/dist/')}
    if len(tracked)!=7501:raise ValueError(f'Expected all 7501 tracked files; found {len(tracked)}')
    files=dict(records)
    for p in (BASE/'ui/dist').iterdir():
        if p.is_file():files['desktop/explorer/dist/'+p.name]=p.read_bytes()
    for name in ['mobile.css','mobile-ui.js']:files['desktop/explorer/dist/'+name]=(BASE/name).read_bytes()
    for p in (BASE/'native').rglob('*'):
        if p.is_file():files['mobile-native/'+p.relative_to(BASE/'native').as_posix()]=p.read_bytes()
    files['docs/MOBILE_COVERAGE.md']=(BASE/'COVERAGE.md').read_bytes()
    for p in (BASE/'vendor-notices').glob('*'):
        if p.is_file():files['mobile/vendor-notices/'+p.name]=p.read_bytes()
    manifest={'snapshot':'a1502150ed1b3619715b3ff33c3cb3fd50b35ff3','source_tree':'768e66e3f4f58837dc98164f6209891bdd78fbe2','original_file_count':len(tracked),'files':tracked}
    assets.joinpath('original-files.json').write_text(json.dumps(manifest,separators=(',',':')))
    files['mobile/ORIGINAL_FILES.json']=assets.joinpath('original-files.json').read_bytes()
    catalog=json.loads(files['desktop/explorer/dist/catalog.json']);catalog['commit']=manifest['snapshot'];catalog['mobile']={'original_file_count':len(tracked),'source_tree':manifest['source_tree']}
    for name in ['docs/MOBILE_COVERAGE.md','mobile/ORIGINAL_FILES.json']:
        b=files[name];catalog['files'].append({'path':name,'title':'Mobile coverage and runtime boundaries' if name.endswith('.md') else 'Complete mobile source manifest','bytes':len(b),'kind':'document' if name.endswith('.md') else 'data','folder':name.split('/')[0],'sha256':digest(b),'summary':b[:500].decode()})
    catalog['total_bytes']=sum(f['bytes'] for f in catalog['files'])
    files['desktop/explorer/dist/catalog.json']=json.dumps(catalog,ensure_ascii=False).encode()
    archive=assets/'repository.zip'
    with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as out:
        for name,b in sorted(files.items()):out.writestr(name,b)
    assets.joinpath('repository.sha256').write_text(digest(archive.read_bytes()))
    with zipfile.ZipFile(archive) as verify:
        assert verify.testzip() is None
        for name,sha in tracked.items():assert digest(verify.read(name))==sha,name
    report={'original_files':len(tracked),'original_missing':[],'original_changed':[],'archive_files':len(files),'archive_bytes':archive.stat().st_size,'archive_sha256':digest(archive.read_bytes()),'commands':len(catalog['commands']),'lean_files':sum(n.endswith('.lean') for n in tracked),'source_tree':manifest['source_tree']}
    BASE.joinpath('CONTENT_CHECKS.json').write_text(json.dumps(report,indent=2));print(json.dumps(report))
