import importlib.util
import json
import subprocess
import zipfile
from pathlib import Path
import pytest

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('mobile_package',ROOT/'mobile/android/package_assets.py')
package_module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(package_module)


def test_selected_git_snapshot_is_complete_and_deterministic(tmp_path,monkeypatch):
    root=tmp_path/'repo';root.mkdir()
    subprocess.run(['git','init','-q',str(root)],check=True)
    (root/'source.txt').write_text('original source\n')
    subprocess.run(['git','add','source.txt'],cwd=root,check=True)
    subprocess.run(['git','-c','user.name=Test','-c','user.email=test@example.com','commit','-qm','fixture'],cwd=root,check=True)
    sha=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
    (root/'source.txt').write_text('uncommitted change must not enter source snapshot\n')
    (root/'untracked.txt').write_text('not source')
    dist=root/'desktop/explorer/dist';dist.mkdir(parents=True)
    (dist/'catalog.json').write_text(json.dumps({'commit':sha,'commands':{'test':{}},'files':[]}))
    base=tmp_path/'mobile';base.mkdir();(base/'native').mkdir()
    for name in ('mobile.css','mobile-ui.js'):(base/name).write_text('overlay')
    ui=base/'ui';ui.mkdir();(ui/'index.html').write_text('generated UI')
    monkeypatch.setattr(package_module,'BASE',base)
    reports=[package_module.package(root,sha,ui,tmp_path/str(i)) for i in range(2)]
    assert reports[0]['archive_sha256']==reports[1]['archive_sha256']
    assert reports[0]['original_files']==1
    with zipfile.ZipFile(tmp_path/'0/repository.zip') as z:
        assert z.read('source.txt')==b'original source\n'
        assert 'untracked.txt' not in z.namelist()
        assert z.read('desktop/explorer/dist/index.html')==b'generated UI'
    (dist/'catalog.json').write_text(json.dumps({'commit':'wrong'}))
    with pytest.raises(ValueError):package_module.package(root,sha,ui,tmp_path/'bad')
