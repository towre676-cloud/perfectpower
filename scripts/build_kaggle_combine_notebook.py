#!/usr/bin/env python3
"""Build a self-contained public-code Kaggle notebook, without competition rows."""
import ast
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
UPSTREAM=ROOT/'research/kaggle_combine/upstream'


def markdown(s):return {'cell_type':'markdown','metadata':{},'source':s.splitlines(keepends=True)}
def code(s):return {'cell_type':'code','execution_count':None,'metadata':{},'outputs':[],'source':s.splitlines(keepends=True)}


def build():
    manifest=json.loads((UPSTREAM/'manifest.json').read_text())
    modules={}
    for name,expected in manifest['files'].items():
        raw=(UPSTREAM/name).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=expected:raise ValueError('upstream changed: '+name)
        modules['upstream/'+name]=raw.decode()
    paths=[
        'python/perfectpower/__init__.py',
        'python/perfectpower/core.py',
        'python/perfectpower/movement_language.py',
        'python/perfectpower/movement_features.py',
        'python/perfectpower/movement_residual.py',
        'python/perfectpower/combine_compact.py',
        'scripts/run_movement_transfer.py',
        'scripts/run_movement_residual.py',
        'docs/COMBINE_COMPACT_PROTOCOL.json',
        'scripts/prepare_movement_residual.py',
        'scripts/run_combine_compact.py',
        'scripts/audit_combine_repeatability.py',
    ]
    for relative in paths:modules[relative]=(ROOT/relative).read_text()
    # The old negative receipt is aggregate evidence, not fitted data.
    history=json.loads((ROOT/'receipts/movement_language/residual.json').read_text())
    old=history['development']
    hashes={p:hashlib.sha256(s.encode()).hexdigest() for p,s in modules.items()}
    source_receipt={'schema':'pp-kaggle-notebook-code/1','module_sha256':hashes,'upstream_notebook_sha256':manifest['source_notebook_sha256'],'no_competition_rows_bundled':True}
    cells=[markdown('''# Can a small Combine movement block survive player-held-out testing?

**NFL Big Data Bowl2027: research continuation, not a submitted or validated scouting model.**

We test whether a fixed, interpretable movement block adds information to conventional Combine measurements for recorded rookie pressure frequency. This is a smaller follow-up to the baseline-preserving residual experiment. That experiment's selected strategy **worsened repeated nested MSE2.878%**; its temporal fits chose zero correction. Earlier favorable movement comparisons and all2025 comparisons remain exploratory. Both engines reuse players and are not independent replications.

The official challenge requires Combine sensor tracking linked to regular-season NFL performance. This notebook rebuilds the historical eligible rush cohort from official files and extracts source-only movement features. The roster remains conditional on observed NFL participation, charted get-off and at least30 eligible records; it does not represent all prospects. The response is a charted pressure-event fraction, not pressures per pass-rush opportunity for every player or a causal athletic effect.

**No competition data are bundled, downloaded or fabricated.** Attach the official competition dataset. The default input path is `/kaggle/input/nfl-big-data-bowl-2027`, overridable through `BDB_DATA_ROOT`. The supplied input hashes pin the original dataset version; a newer version must be reconciled explicitly before continuing.

The separate two-season2025 linebacker confirmation project is not opened or scored here.
'''),code('''import os, sys, json, hashlib, tempfile, contextlib, importlib.util
from pathlib import Path
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
try:
    from IPython.display import display
except ImportError:
    display=print

WORK=Path(os.environ.get('BDB_WORK_ROOT', tempfile.mkdtemp(prefix='bdb_compact_'))).resolve()
WORK.mkdir(parents=True,exist_ok=True)
REPO=WORK/'public_code';REPO.mkdir(exist_ok=True)
'''+f'MODULES={modules!r}\nSOURCE_RECEIPT={source_receipt!r}\n'+'''
for relative,source in MODULES.items():
    target=REPO/relative;target.parent.mkdir(parents=True,exist_ok=True)
    assert hashlib.sha256(source.encode()).hexdigest()==SOURCE_RECEIPT['module_sha256'][relative]
    target.write_text(source)
sys.path[:0]=[str(REPO/'python'),str(REPO/'scripts'),str(REPO/'upstream')]
print('Verified public code modules:',len(MODULES))
'''),markdown('''## Reconstruct the same sample, then use source Combine position

The historical cohort adapter is preserved byte for byte and only its preparation function is called. It selects the old participation-conditioned cohort using NFL records. The prediction code uses **source Combine position** and source measurements; it does not use eventual NFL position, NFL movement, pressure outcomes or future exposures as movement inputs. The extraction audit rejects inconsistent player-level source values.

For a trusted saved continuation, set both `BDB_PLAYERS` and `BDB_EVENTS` to the exact private extracted files already authorized by you. Pickle files execute Python on loading, so this optional path is only for your own trusted saved files. A supplied continuation bypasses raw reconstruction; its receipt records that fact and it is not a substitute for a full official-data reproducibility run.
'''),code(f'OFFICIAL_HASHES={manifest["official_source_sha256"]!r}\n'+'''
provided_players=os.environ.get('BDB_PLAYERS')
provided_events=os.environ.get('BDB_EVENTS')
if bool(provided_players)!=bool(provided_events):raise ValueError('Set BDB_PLAYERS and BDB_EVENTS together')
if provided_players:
    PLAYERS=Path(provided_players).resolve();EVENTS=Path(provided_events).resolve()
    if not PLAYERS.is_file() or not EVENTS.is_file():raise FileNotFoundError('Trusted continuation files missing')
    input_mode='trusted extracted continuation; official raw reconstruction skipped'
else:
    DATA=Path(os.environ.get('BDB_DATA_ROOT','/kaggle/input/nfl-big-data-bowl-2027')).resolve()
    if not (DATA/'players.csv').is_file():raise FileNotFoundError('Attach official competition data or set BDB_DATA_ROOT')
    for name,expected in OFFICIAL_HASHES.items():
        h=hashlib.sha256()
        with (DATA/name).open('rb') as stream:
            for chunk in iter(lambda:stream.read(8*1024*1024),b''):h.update(chunk)
        if h.hexdigest()!=expected:raise ValueError('Official dataset version differs: '+name)
    import front_transfer as historical_cohort
    import prepare_movement_residual as prepare_current
    COHORT=WORK/'private_front';EXTRACTED=WORK/'private_current'
    with (WORK/'private_extraction.log').open('w') as log,contextlib.redirect_stdout(log):
        historical_cohort.prepare(DATA,COHORT)
        prepare_current.prepare(DATA,COHORT/'private_rows.pkl',EXTRACTED)
    PLAYERS=EXTRACTED/'players.pkl';EVENTS=EXTRACTED/'events.pkl'
    input_mode='nine source hashes verified; official raw cohort reconstructed'
print(input_mode)
'''),markdown('''## Fixed compact comparison

The experiment specification fixes the compact movement block before this run. Whole athletes remain together through outer folds, inner tuning and training resamples. Conventional preprocessing and correction fits use training players only. The policy may return the baseline exactly. A zero option is a model-selection safeguard, not a promise of better future prediction.

The primary outcome is equal-player squared error on the existing conditional pressure-rate target. Earlier classes are development;2025 is exploratory. No new cohort becomes independent merely because this notebook is new. The runner saves private player predictions outside the public-code directory and exposes only aggregate receipts below. Set `BDB_REFITS` to the desired predeclared full-refit count before running; the default is20 and its interval is a coarse diagnostic.
'''),code('''import run_combine_compact as compact_runner
REFITS=int(os.environ.get('BDB_REFITS','20'))
PERMUTATIONS=int(os.environ.get('BDB_PERMUTATIONS','16'))
if REFITS<0 or PERMUTATIONS<0:raise ValueError('Iteration counts must be nonnegative')
RESULT=WORK/'aggregate_compact.json'
PRIVATE=WORK/'private_compact_results'
argv=['run_combine_compact.py','--players',str(PLAYERS),'--events',str(EVENTS),'--private-out',str(PRIVATE),'--aggregate',str(RESULT),'--refits',str(REFITS),'--permutations',str(PERMUTATIONS)]
old_argv=sys.argv
try:
    sys.argv=argv
    with (WORK/'private_models.log').open('w') as log,contextlib.redirect_stdout(log):
        compact_runner.main()
finally:sys.argv=old_argv
result=json.loads(RESULT.read_text())
import audit_combine_repeatability as repeatability_audit
repeatability=repeatability_audit.audit(pd.read_pickle(EVENTS))
(WORK/'aggregate_repeatability.json').write_text(json.dumps(repeatability,indent=2,allow_nan=False)+'\\n')
print('Aggregate receipt:',RESULT.name)
print(json.dumps({k:v for k,v in result.items() if k not in ('source_sha256','input_sha256','repeats')},indent=2)[:15000])
'''),markdown('''## Results: keep gain, loss and fallback visible

The three figures below summarize only recorded aggregate comparisons. Positive relative gain means lower error. The first figure keeps the earlier negative study visible. The next two report this run's comparisons and source-attempt repeatability; missing expected receipt fields cause a clear error rather than a fabricated chart. Intervals are conditional diagnostics and do not cover the full adaptive research history or future class shift. The exact aggregate receipt is the authority. Class stability appears in the table. Alternating event-ID split agreement uses only2023/2024 Combine attempts and no NFL outcomes; it is descriptive agreement across potentially different instructions, not biological reliability or calibrated physiology.
'''),code(f'HISTORICAL_DEVELOPMENT={old!r}\n'+'''
old_rows=[(name,value['relative_gain']*100) for name,value in HISTORICAL_DEVELOPMENT['comparisons'].items()]
fig,ax=plt.subplots(figsize=(8,3.6))
ax.barh([x[0] for x in old_rows],[x[1] for x in old_rows],color=['#327860' if x[1]>0 else '#b55d45' for x in old_rows])
ax.axvline(0,color='#444',linewidth=.8);ax.set_xlabel('Earlier residual study: relative MSE gain (%)')
ax.set_title('Historical negative evidence remains part of the record')
plt.tight_layout();plt.show()

# Runner schema: development.comparisons maps model name to relative_gain.
development=result['development']
comparison_rows=[(name,value['relative_gain']*100) for name,value in development['comparisons'].items()]
fig,ax=plt.subplots(figsize=(8,3.6))
ax.barh([x[0] for x in comparison_rows],[x[1] for x in comparison_rows],color=['#327860' if x[1]>0 else '#b55d45' for x in comparison_rows])
ax.axvline(0,color='#444',linewidth=.8);ax.set_xlabel('Compact study: relative MSE gain (%)')
ax.set_title('Fixed comparisons, including losses')
plt.tight_layout();plt.show()

class_rows=[]
for name,value in development['comparisons'].items():
    for year,cell in value.get('by_class',{}).items():class_rows.append({'model':name,'draft_class':year,'relative_gain_percent':100*cell['relative_gain']})
if not class_rows:raise ValueError('Aggregate receipt lacks required class stability diagnostics')
class_table=pd.DataFrame(class_rows)
display(class_table)

measurement_rows=[]
for name,cell in repeatability['features'].items():
    measurement_rows.append({'feature':name.replace('movement__','').replace('__',' / '),'repeat_players':cell['repeat_players'],'split_spearman':cell['split_spearman']})
measurement_table=pd.DataFrame(measurement_rows)
fig,ax=plt.subplots(figsize=(8,3.6))
for row in measurement_rows:
    if row['split_spearman'] is not None:
        ax.scatter(row['repeat_players'],row['split_spearman'],s=60)
        ax.annotate(row['feature'],(row['repeat_players'],row['split_spearman']),xytext=(4,4),textcoords='offset points',fontsize=8)
ax.axhline(0,color='#444',linewidth=.8);ax.set_xlabel('Players with repeated source attempts')
ax.set_ylabel('Alternating-split Spearman correlation');ax.set_ylim(-1.1,1.1)
ax.set_title('Measurement support before scouting claims; absent points mean insufficient support')
plt.tight_layout();plt.show()
display(measurement_table)
'''),markdown('''## Football interpretation and submission boundary

In the recovered74-player cohort, the supplied source Combine position is `DL` for every player. The trained role-mean control therefore equals the global-mean control here; these are intentionally retained as transparent equivalent controls, not independent stratified benchmarks.

A movement metric can be a useful measurement without yet being a dependable scouting predictor. A favorable point estimate here is a hypothesis for later players, not a validated talent ranking. Source noise, sparse repeated attempts, selection into NFL opportunities, position and usage differences all remain plausible explanations.

For coaches, the operational takeaway must match the actual result: use reproducible movement profiles to describe and investigate a player's drill behavior; retain conventional forecasts unless incremental value survives the declared comparisons. No physiological phase calibration or causal development recommendation is claimed.

This notebook is a reproducible continuation artifact. It has not been published or submitted to Kaggle by this code. The competition Writeup must remain within2000 words and fewer than10 tables/figures, explicitly link Combine sensor tracking with NFL performance, and attach a public Kaggle notebook. Verify current official requirements before final submission: https://www.kaggle.com/competitions/nfl-big-data-bowl-2027/overview/timeline .
''')]
    notebook={'cells':cells,'metadata':{'kernelspec':{'display_name':'Python3','language':'python','name':'python3'},'language_info':{'name':'python','version':'3.12'},'perfectpower':source_receipt},'nbformat':4,'nbformat_minor':5}
    for i,c in enumerate(cells):
        c['id']=f'combine-{i:02d}'
        if c['cell_type']=='code':ast.parse(''.join(c['source']))
    path=ROOT/'notebooks/Combine_Movement_Continuation.ipynb';path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(notebook,indent=1)+'\n')
    print(json.dumps({'notebook':str(path.relative_to(ROOT)),'code_modules':len(modules),'cells':len(cells),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'raw_data_bundled':False}))
    return path

if __name__=='__main__':build()
