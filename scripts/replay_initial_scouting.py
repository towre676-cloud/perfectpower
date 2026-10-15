#!/usr/bin/env python3
"""Replay retained pre-guard mathematics using the current CLI and exact initial core.

Pass the same arguments as run_scouting_expansion.py. The protocol hash reflects
current documentation; retained initial receipt preserves its original hash.
"""
import hashlib,importlib.util,json,runpy,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import perfectpower
source=ROOT/'research/scouting_expansion/initial/scouting_metrics.py'
spec=importlib.util.spec_from_file_location('perfectpower.scouting_metrics',source);module=importlib.util.module_from_spec(spec);sys.modules[spec.name]=module;spec.loader.exec_module(module)
runpy.run_path(str(ROOT/'scripts/run_scouting_expansion.py'),run_name='__main__')
output=Path(sys.argv[sys.argv.index('--aggregate')+1]);r=json.loads(output.read_text());r['evaluation_mode']='initial_core_replay';r['source_sha256']['python/perfectpower/scouting_metrics.py']=hashlib.sha256(source.read_bytes()).hexdigest();r['loaded_core_path']=str(source.relative_to(ROOT));output.write_text(json.dumps(r,indent=2)+'\n')
