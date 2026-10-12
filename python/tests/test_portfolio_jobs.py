import importlib.util
import json
import sys
import tempfile
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('explorer_test_server',ROOT/'desktop/explorer/server.py')
server=importlib.util.module_from_spec(spec);spec.loader.exec_module(server)

def wait(e,id):
    until=time.monotonic()+15
    while time.monotonic()<until:
        if e.jobs[id]['status']!='running':return e.jobs[id]
        time.sleep(.02)
    raise AssertionError('Portfolio job did not terminate')

def test_cancel_then_fresh_exact_result(tmp_path):
    e=server.Explorer(ROOT,tmp_path)
    try:
        old=tmp_path/'runs/previous';old.mkdir();(old/'user-data.txt').write_text('keep')
        id=e.submit({'kind':'portfolio','action':'build','timeout':1200})['id']
        until=time.monotonic()+5
        while '_process' not in e.jobs[id] and time.monotonic()<until:time.sleep(.01)
        e.jobs[id]['cancel_requested']=True;e.jobs[id]['_process'].kill()
        assert wait(e,id)['status']=='cancelled'
        source=json.loads((ROOT/'examples/planning/petersen_50_population.json').read_text())['specification']
        limits=[dict(r,max=0) for r in source['resources']]
        id=e.submit({'kind':'portfolio','action':'build','resources':limits})['id']
        r=wait(e,id);assert r['status']=='complete';assert r['result']['summary']['count']=='1'
        assert (old/'user-data.txt').read_text()=='keep'
        assert (tmp_path/'runs'/id/'portfolio-evidence.json').exists()
    finally:e.close()

def test_session_reused_across_jobs(tmp_path):
    e=server.Explorer(ROOT,tmp_path)
    try:
        source=json.loads((ROOT/'examples/planning/petersen_50_population.json').read_text())['specification']
        body={'kind':'portfolio','action':'build','resources':[dict(r,max=0) for r in source['resources']]}
        first=wait(e,e.submit(body)['id']);second=wait(e,e.submit(body)['id'])
        assert first['result']['session_reused'] is False
        assert second['result']['session_reused'] is True
    finally:e.close()
