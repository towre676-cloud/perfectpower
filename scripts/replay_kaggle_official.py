#!/usr/bin/env python3
"""Execute the output-free Kaggle notebook against nine hash-pinned CSVs.

Private extraction, plots and logs stay outside the checkout. Receipt is public.
"""
import argparse,contextlib,hashlib,json,os,platform,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(8*1024*1024),b''):h.update(block)
    return h.hexdigest()

def replay(data,work,receipt,refits=20,permutations=16):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    data=data.resolve();work=work.resolve()
    if ROOT==work or ROOT in work.parents:raise ValueError('private work must stay outside checkout')
    if work.exists() and any(work.iterdir()):raise ValueError('fresh empty work directory required')
    work.mkdir(parents=True,exist_ok=True)
    notebook=ROOT/'notebooks/Combine_Movement_Continuation.ipynb'
    n=json.loads(notebook.read_text());pins=json.loads((ROOT/'research/kaggle_combine/upstream/manifest.json').read_text())['official_source_sha256']
    checked={}
    for name,h in pins.items():
        if sha(data/name)!=h:raise ValueError('official file changed '+name)
        checked[name]={'sha256':h,'bytes':(data/name).stat().st_size}
    prior={k:os.environ.get(k) for k in ['BDB_DATA_ROOT','BDB_WORK_ROOT','BDB_PLAYERS','BDB_EVENTS','BDB_REFITS','BDB_PERMUTATIONS','BDB_GETOFF_RUSHES']}
    os.environ.update(BDB_DATA_ROOT=str(data),BDB_WORK_ROOT=str(work),BDB_REFITS=str(refits),BDB_PERMUTATIONS=str(permutations))
    os.environ.pop('BDB_PLAYERS',None);os.environ.pop('BDB_EVENTS',None);os.environ.pop('BDB_GETOFF_RUSHES',None)
    start=time.perf_counter();scope={'__name__':'__kaggle_official_replay__'};executed=[]
    try:
        with (work/'notebook_execution.log').open('w') as log:
            for i,cell in enumerate(n['cells']):
                if cell['cell_type']!='code':continue
                print(json.dumps({'cell_started':i}),flush=True)
                with contextlib.redirect_stdout(log),contextlib.redirect_stderr(log):exec(compile(''.join(cell['source']),str(notebook)+f':cell{i}','exec'),scope)
                executed.append(i)
                for number in plt.get_fignums():plt.figure(number).savefig(work/f'cell_{i}_figure_{number}.png',dpi=120,bbox_inches='tight')
                plt.close('all')
    finally:
        for k,v in prior.items():
            if v is None:os.environ.pop(k,None)
            else:os.environ[k]=v
    actual=json.loads((work/'aggregate_compact.json').read_text());old=json.loads((ROOT/'receipts/kaggle_combine/compact.json').read_text())
    diffs=[]
    for stage in ['development']:
        for model,v in old[stage]['comparisons'].items():diffs.append(abs(actual[stage]['comparisons'][model]['mse']-v['mse']))
    for stage,v in old['temporal'].items():
        for model,m in v['evaluation']['comparisons'].items():diffs.append(abs(actual['temporal'][stage]['evaluation']['comparisons'][model]['mse']-m['mse']))
    getoff_file=work/'aggregate_getoff.json'
    if not getoff_file.exists():raise ValueError('get-off evaluation was skipped')
    getoff=json.loads(getoff_file.read_text());reference=json.loads((ROOT/'receipts/kaggle_combine/getoff.json').read_text());getoff_diffs=[]
    for name in ['development',*reference['temporal']]:
        a=getoff['development'] if name=='development' else getoff['temporal'][name]
        b=reference['development'] if name=='development' else reference['temporal'][name]
        for metric in ['primary','auxiliary']:
            for model,v in b[metric]['comparisons'].items():getoff_diffs.append(abs(a[metric]['comparisons'][model]['mse_seconds2']-v['mse_seconds2']))
    if max(getoff_diffs)>1e-12:raise ValueError('getoff raw notebook differs from standalone execution')
    result={'schema':'pp-kaggle-official-rebuild/2','official_raw_rebuild_executed':True,'trusted_extracted_bypass':False,'official_files':checked,'notebook_sha256':sha(notebook),'source_sha256':sha(Path(__file__)),'executed_code_cells':executed,'full_refits':2*refits,'mislinking_runs':permutations,'cohort':actual['cohort'],'models_promoted':False,'independent_confirmation':False,'sealed_two_season_outcomes_opened':False,'maximum_mse_difference_from_saved_input_run':max(diffs),'comparisons_checked':len(diffs),'getoff_evaluation_executed':True,'getoff_comparisons_checked':len(getoff_diffs),'getoff_maximum_mse_difference':max(getoff_diffs),'getoff_result_sha256':sha(getoff_file),'aggregate_result_sha256':sha(work/'aggregate_compact.json'),'figure_count':len(list(work.glob('cell_*_figure_*.png'))),'elapsed_seconds':time.perf_counter()-start,'python':platform.python_version()}
    if max(diffs)>1e-12:raise ValueError('official rebuild differs from saved-input run')
    receipt.parent.mkdir(parents=True,exist_ok=True);receipt.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['data','work','receipt']:p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--refits',type=int,default=20);p.add_argument('--permutations',type=int,default=16)
    a=p.parse_args();replay(**vars(a))
