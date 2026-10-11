#!/usr/bin/env python3
"""Fresh kernel checks of general obligations and bounded literal protein inputs."""
import argparse,subprocess,os,json,gzip,time,re,sys
from hashlib import sha256
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
from perfectpower.blast_io import tabular
from perfectpower.blast_benchmark import load_dataset,stream_hits
OUT=ROOT/'receipts/blast/oxbench';BUILD=ROOT/'.lake/build/lib/lean'
def main():
    p=argparse.ArgumentParser();p.add_argument('--lean',default='lean');a=p.parse_args()
    _,records,groups,_,_=load_dataset(ROOT/'data/oxbench')
    family_of={k:g for g,ids in groups.items() for k in ids}
    certificates=['import PerfectPower.BlastSourceReplay','set_option maxRecDepth 16384','set_option maxHeartbeats 2000000','namespace PerfectPower.OxbenchInputs','open PerfectPower.BlastSourceReplay']
    selected=[]
    for task in ('blastp','blastp-fast'):
        hits=stream_hits(ROOT/'data/oxbench'/(task+'.tsv.xz'))
        families=set()
        for n,h in enumerate(hits):
            f=h.fields;family=family_of[f['qseqid']]
            if f['qseqid']==f['sseqid'] or family in families:continue
            families.add(family);name=f'witness_{task.replace("-","_")}_{len(families)}'
            certificates.append(f'def {name} : Input := ⟨{json.dumps(records[f["qseqid"]])}, {json.dumps(records[f["sseqid"]])}, {f["qstart"]}, {f["qend"]}, {f["sstart"]}, {f["send"]}, {json.dumps(f["btop"])}⟩')
            certificates.append(f'theorem {name}_accepted : accepts {name} = true := by decide')
            certificates.append(f'#print axioms {name}_accepted')
            selected.append({'task':task,'raw_row_zero_based':n,'fields':dict(f),'query_sha256':sha256(records[f['qseqid']].encode()).hexdigest(),'subject_sha256':sha256(records[f['sseqid']].encode()).hexdigest()})
            if len(families)==12:break
    certificates.extend(['example : accepts ⟨"AA", "AC", 1, 2, 1, 2, "2"⟩ = false := by decide','example : accepts ⟨"AA", "AA", 0, 2, 1, 2, "2"⟩ = false := by decide','end PerfectPower.OxbenchInputs'])
    path=ROOT/'PerfectPower/Generated/OxbenchInputs.lean';path.write_text('\n'.join(certificates)+'\n')
    env=dict(os.environ,LEAN_PATH=str(BUILD)+':'+os.environ.get('LEAN_PATH',''))
    rows=[]
    version=subprocess.run([a.lean,'--version'],check=True,capture_output=True,text=True,env=env).stdout.strip()
    for module in ('PerfectPower/BlastRecurrence.lean','PerfectPower/BlastSourceReplay.lean','PerfectPower/Generated/OxbenchInputs.lean'):
        target=BUILD/Path(module).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        start=time.perf_counter();r=subprocess.run([a.lean,'-o',str(target),module],cwd=ROOT,env=env,capture_output=True,text=True,timeout=120)
        log=r.stdout+r.stderr;(OUT/(Path(module).stem+'.log')).write_text(log)
        accepted=r.returncode==0 and not re.search(r'sorryAx|declaration uses .sorry.|error:',log)
        rows.append({'module':module,'source_sha256':sha256((ROOT/module).read_bytes()).hexdigest(),'returncode':r.returncode,'accepted':accepted,'seconds':time.perf_counter()-start,'log':Path(module).stem+'.log'})
        if not accepted:raise RuntimeError(log)
    receipt={'schema':'pp-oxbench-kernel/1','lean_version':version,'modules':rows,'literal_inputs':selected,'literal_inputs_accepted':len(selected),'negative_decisions':2,'accepted':True,'per_module_timeout_seconds':120,'reused_general_modules_from':'existing local BLAST certification work at parent 367147e; unchanged SHA256 sources, freshly checked','scope':'generic recurrence equals finite path-language coefficients, decreasing-rank completeness and no duplicate paths under distinct successors; generic raw BTOP acceptance soundness and bounds. Listed literal protein inputs checked with decide. Python/XML/tar parsers, hashes, annotations and BLAST search completeness are not Lean-proved.'}
    (OUT/'kernel.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Kernel accepted',len(rows),'modules;',len(selected),'literal protein inputs')
if __name__=='__main__':main()
