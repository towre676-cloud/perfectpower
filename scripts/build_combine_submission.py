#!/usr/bin/env python3
"""Build a review notebook from the unchanged, historically replayed notebook.

Receipt mode makes no fresh empirical claim. Raw mode calls existing compute
cells, without rerunning a feature search or changing any estimator.
"""
import ast
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]


def md(s):return {'cell_type':'markdown','metadata':{},'source':s.splitlines(True)}
def code(s):return {'cell_type':'code','metadata':{},'source':s.splitlines(True),'outputs':[],'execution_count':None}


def build():
    original=ROOT/'notebooks/Combine_Movement_Continuation.ipynb'
    raw=original.read_bytes();old=json.loads(raw)
    historical=json.loads((ROOT/'receipts/kaggle_combine/official_rebuild_full.json').read_text())
    if hashlib.sha256(raw).hexdigest()!=historical['notebook_sha256']:
        raise ValueError('Historical notebook no longer matches the raw rebuild receipt')
    names=['compact.json','getoff.json','repeatability.json','official_rebuild_full.json','getoff_extraction.json','reliability_pair_review.json','loss_geometry.json','rules_review.json']
    receipts={n:(ROOT/'receipts/kaggle_combine'/n).read_text() for n in names}
    pins={n:hashlib.sha256(s.encode()).hexdigest() for n,s in receipts.items()}
    cell_sources={i:''.join(old['cells'][i]['source']) for i in (1,3,5,9)}
    renderer=(ROOT/'scripts/combine_submission_analysis.py').read_text()
    pair_source=(ROOT/'scripts/audit_combine_reliability_pair.py').read_text()
    cells=[md('''# Before ranking the rush: measure, then test NFL value

**NFL Big Data Bowl 2027 · proposed public companion notebook. Not published or submitted.**

The linked writeup separates descriptive repeat-attempt rank stability from incremental NFL forecasting. The historical data contain 74 players, 361 source attempts and 14,665 retained rookie records. All 2025 comparisons remain exploratory. No separate linebacker results enter this analysis.

This notebook extends the existing official reconstruction; it does not replace completed experiments. The original notebook and its historical execution receipt remain unchanged. **Default receipt mode audits saved aggregate evidence and recreates four figures. It does not read tracking rows or refit a model.** Raw mode below uses the original compute cells, the same estimators, and the same nine official SHA-256 pins.

Use `BDB_SUBMISSION_MODE=raw` before Run All for an official-data run. Attach the authorized competition data and set `BDB_DATA_ROOT` if its mount differs from `/kaggle/input/nfl-big-data-bowl-2027`. No dataset is downloaded. The data version is checked before extraction. Raw outputs are private temporary files outside `/kaggle/working`; only the four aggregate figures and aggregate audit are written to the public output directory.

Raw dependencies: numpy 2.3.5, scipy 1.17.0, pandas 2.2.3, scikit-learn 1.8.0, plus matplotlib. Different versions may change numerical replay and must be disclosed. The default uses 20 full pressure refits per temporal comparison and 16 mislinking runs. Reduced counts are diagnostics, not full reproduction.
'''),code('''import os, json, hashlib, tempfile, sys, contextlib, io, platform
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from IPython.display import display, Image
MODE=os.environ.get('BDB_SUBMISSION_MODE','receipts')
if MODE not in ('receipts','raw'): raise ValueError('Mode must be receipts or raw')
OUT=Path(os.environ.get('BDB_SUBMISSION_OUTPUT','/kaggle/working/combine_submission' if Path('/kaggle').exists() else 'combine_submission_output')).resolve()
OUT.mkdir(parents=True,exist_ok=True)
'''+f'RECEIPT_TEXT={receipts!r}\nRECEIPT_SHA256={pins!r}\nHISTORICAL_NOTEBOOK_SHA256={hashlib.sha256(raw).hexdigest()!r}\n'+'''
for name,source in RECEIPT_TEXT.items():
    if hashlib.sha256(source.encode()).hexdigest()!=RECEIPT_SHA256[name]:raise ValueError('Receipt changed: '+name)
EVIDENCE={name:json.loads(source) for name,source in RECEIPT_TEXT.items()}
print('Mode:',MODE)
print('Receipt mode uses historical aggregate evidence; raw tracking requested:',MODE=='raw')
'''),md('''## Reuse the existing experiment, with explicit execution status

The next cell embeds only public source from the historically replayed notebook. In raw mode it executes that notebook's setup, reconstruction, compact model and get-off model cells; its older plotting cells are replaced by the presentation below. Saved-input pickle bypasses are disabled, and missing get-off context fails the raw run rather than being silently treated as completion. The official source hash pins, cohort definitions, outcome definitions, folds and estimators are unchanged.

The historical raw receipt records 12 pressure and 30 get-off MSE comparisons with zero maximum difference. That receipt certifies the historical notebook hash, not this wrapper. Execution status below distinguishes a new raw run from a historical aggregate audit. Private logs, reconstructed records and per-player forecasts stay in a temporary directory outside the notebook's public output tree. Do not export that private directory.
'''),code(f'ORIGINAL_COMPUTE_CELLS={cell_sources!r}\nPAIR_AUDIT_SOURCE={pair_source!r}\n'+'''
RAW_EXECUTED=False
RAW_COMPARISONS=None
if MODE=='raw':
    # Never allow trusted extracted inputs to masquerade as an official rebuild.
    for key in ('BDB_PLAYERS','BDB_EVENTS','BDB_GETOFF_RUSHES'):
        if os.environ.get(key):raise ValueError('Unset trusted bypass for official raw mode: '+key)
    private=Path(tempfile.mkdtemp(prefix='bdb_submission_private_')).resolve()
    if private==OUT or OUT in private.parents:raise ValueError('Private work must be outside public outputs')
    prior=os.environ.get('BDB_WORK_ROOT');os.environ['BDB_WORK_ROOT']=str(private)
    scope={'__name__':'__submission_raw_replay__'}
    try:
        with (private/'wrapper.log').open('w') as log,contextlib.redirect_stdout(log),contextlib.redirect_stderr(log):
            for index in (1,3,5,9):
                exec(compile(ORIGINAL_COMPUTE_CELLS[index],f'historical_notebook_cell_{index}','exec'),scope)
        if not scope.get('RAW_INPUTS_VERIFIED'):raise ValueError('Official hash validation did not run')
        if scope.get('GETOFF_RESULT') is None:raise ValueError('Get-off experiment skipped: incomplete raw run')
        EVIDENCE['compact.json']=scope['result']
        EVIDENCE['getoff.json']=scope['GETOFF_RESULT']
        EVIDENCE['repeatability.json']=scope['repeatability']
        diffs=[]
        current=EVIDENCE['compact.json'];reference=json.loads(RECEIPT_TEXT['compact.json'])
        for key in ('development','2023_to_2024','exploratory_2025'):
            aa=current['development'] if key=='development' else current['temporal'][key]['evaluation']
            bb=reference['development'] if key=='development' else reference['temporal'][key]['evaluation']
            diffs.extend(abs(v['mse']-bb['comparisons'][m]['mse']) for m,v in aa['comparisons'].items())
        pressure_diffs=diffs.copy();diffs=[]
        current=EVIDENCE['getoff.json'];reference=json.loads(RECEIPT_TEXT['getoff.json'])
        for key in ('development','2023_to_2024','exploratory_2025'):
            aa=current['development'] if key=='development' else current['temporal'][key]
            bb=reference['development'] if key=='development' else reference['temporal'][key]
            for metric in ('primary','auxiliary'):
                diffs.extend(abs(v['mse_seconds2']-bb[metric]['comparisons'][m]['mse_seconds2']) for m,v in aa[metric]['comparisons'].items())
        RAW_COMPARISONS={'pressure_count':len(pressure_diffs),'getoff_count':len(diffs),'maximum_mse_difference':max(pressure_diffs+diffs)}
        if RAW_COMPARISONS['maximum_mse_difference']>1e-12:raise ValueError('Raw replay differs from historical MSE: '+str(RAW_COMPARISONS))
        paired_scope={'__name__':'submission_paired_audit'}
        exec(compile(PAIR_AUDIT_SOURCE,'audit_combine_reliability_pair.py','exec'),paired_scope)
        import pandas as pd
        EVIDENCE['reliability_pair_review.json','loss_geometry.json','rules_review.json']=paired_scope['audit'](pd.read_pickle(scope['EVENTS']))
        RAW_EXECUTED=True
    finally:
        if prior is None:os.environ.pop('BDB_WORK_ROOT',None)
        else:os.environ['BDB_WORK_ROOT']=prior
print('Fresh official tracking run executed:',RAW_EXECUTED)
'''),md('''## Audit the claims before drawing the figures

Relative reduction is `(baseline MSE − candidate MSE) / baseline MSE`; positive values favor movement. Pressure uses equal-player error on an observed charted pressure-event fraction. Get-off primary loss squares each player's mean residual; auxiliary loss averages squared residuals within player and then gives players equal weight.

For one player with residuals e, `mean(e²) = mean(e)² + mean((e − mean(e))²)`. Adding a constant per player leaves the centered-residual term unchanged. The code checks this identity against the aggregate get-off losses for context-only, conventional-plus-context, fixed launch and selected launch. The additional insight is an exact decomposition of prior results, not a new experiment or estimate of irreducible noise.

Rank stability is descriptive: speed gain is net change over a longer active window, not the separate half-second launch measure. The saved-attempt audit now supplies a joint paired-player bootstrap of the reliability difference: 0.260, descriptive 95% interval −0.105–0.650. This exploratory diagnostic was selected after the marginal results were known. It does not establish superiority of one feature. Receipt mode reads its aggregate result; raw mode recomputes it from extracted attempts.
'''),code('RENDERER_SOURCE='+repr(renderer)+'\n'+'''
analysis_scope={'__name__':'submission_analysis'}
exec(compile(RENDERER_SOURCE,'combine_submission_analysis.py','exec'),analysis_scope)
AUDIT=analysis_scope['analyze'](EVIDENCE)
AUDIT['raw_reexecution']=RAW_EXECUTED
AUDIT['mode']=MODE
AUDIT['historical_receipt_sha256']=RECEIPT_SHA256
AUDIT['historical_notebook_sha256']=HISTORICAL_NOTEBOOK_SHA256
AUDIT['versions']={'python':platform.python_version(),'numpy':np.__version__,'matplotlib':matplotlib.__version__}
if RAW_EXECUTED:
    AUDIT['raw_run']={'refits_per_temporal':int(os.environ.get('BDB_REFITS','20')),'mislinking_runs':int(os.environ.get('BDB_PERMUTATIONS','16')),'comparisons':RAW_COMPARISONS,'current_compact_sha256':hashlib.sha256(json.dumps(EVIDENCE['compact.json'],sort_keys=True).encode()).hexdigest(),'current_getoff_sha256':hashlib.sha256(json.dumps(EVIDENCE['getoff.json'],sort_keys=True).encode()).hexdigest()}
(OUT/'aggregate_audit.json').write_text(json.dumps(AUDIT,indent=2)+'\\n')
print(json.dumps({k:AUDIT[k] for k in ('mode','raw_reexecution','getoff_fallback_fits','pressure','getoff_decomposition')},indent=2))
FIGURES=analysis_scope['render'](EVIDENCE,OUT)
'''),md('''## Four figures for the writeup

1. Repeat-attempt rank stability: show support and descriptive uncertainty, including drills with insufficient repeats.
2. Pressure transfer: retain fixed and selected corrections, all negative results and exact fallback.
3. Mechanism-matched get-off: retain the wide conditional intervals and all three evaluations.
4. Loss decomposition: show why player-mean calibration and individual-snap prediction require different evidence.

All figures use only aggregate receipts. Positive gain is better. Interval bars are pointwise, conditional on fitted predictions, not simultaneous claims. They omit adaptive research and new-cohort uncertainty; get-off intervals additionally omit model refitting and shared-game dependence. A zero interval for exact fallback is algebraic identity with the baseline, not perfect knowledge about future outcomes.
'''),code('''for name in FIGURES:
    display(Image(filename=str(OUT/name)))
'''),md('''## Football interpretation and next checks

Retain conventional prospect forecasts. Use repeated source measurements to organize film and drill review; do not promote a hidden-talent ranking or training intervention. The longer-window speed-gain result does not establish reliability of the half-second launch metric. Both must be measured separately.

The within-player residual share is 92.1% in development, 95.4% in 2024 and 96.1% in exploratory 2025. It is unchanged by this model's constant-per-player launch correction. Even a label-aware oracle choosing arbitrary player constants could reduce play-level MSE by at most 7.86%, 4.56% and 3.94%, respectively, with the baseline and evaluated records fixed. These are sharp structural ceilings, not achieved gains. The bounded oracle uses clip(mean player residual, -cap, cap). A centered movement-by-context interaction might target within-player variation without changing mean calibration, but would be a new experiment requiring separate validation. The mathematical companion proves both statements and shows why a failed full-strength correction alone cannot identify whether additional shrinkage would help.

Restricted data are needed to re-extract trajectories, rerun estimator fits, test alternate attempt splits or onset/smoothing choices, estimate repeatability of the new launch block, inspect snap/game clustering, and audit player-level outliers or opportunity sensitivity. The historical marginal repeatability audit was exactly replayed from the saved attempt file during this revision, and the new paired difference diagnostic was executed. The other listed checks have not been freshly executed in receipt mode. Aggregate receipt arithmetic cannot replace them.

Every source class has been inspected. A new wrapper, new endpoint or new split of these players does not create independent confirmation. Do not inspect the separate sealed linebacker study for this entry.

Official requirements reviewed 4 November 2026: at most 2,000 writeup words, fewer than 10 combined tables/figures, explicit Combine-tracking-to-NFL linkage, readable markdown, embedded visuals and an attached public Kaggle notebook. Judging: football 30%, data science 30%, writing 20%, visualization 20%. Deadline: 6 January 2027, 23:59 UTC. The full Rules tab was inspected directly in the rendered browser on 4 November 2026. Hackathon teams have one submission and at most five members. Competition data remain noncommercial and protected from nonparticipant access. Public code must also be shared through the competition-associated Kaggle forum or notebooks under an OSI-approved license allowing commercial code use; winning solutions carry related license/reproduction obligations. No agreement or entry was accepted by this notebook.

Sources: [official overview](https://www.kaggle.com/competitions/nfl-big-data-bowl-2027/overview/submission-requirements), [original PR 14](https://github.com/towre676-cloud/perfectpower/pull/14), [get-off monograph](https://github.com/towre676-cloud/perfectpower/blob/main/docs/COMBINE_GETOFF_MONOGRAPH.md). This notebook has not been uploaded, published or submitted. Attach it only after the author has reviewed and authorized publication.
''')]
    for i,c in enumerate(cells):
        c['id']=f'submission-{i:02d}'
        if c['cell_type']=='code':ast.parse(''.join(c['source']))
    nb={'nbformat':4,'nbformat_minor':5,'metadata':{'kernelspec':{'name':'python3','display_name':'Python 3','language':'python'},'language_info':{'name':'python','version':'3.12'},'perfectpower':{'mode_default':'receipts','historical_notebook_sha256':hashlib.sha256(raw).hexdigest(),'restricted_rows_bundled':False,'publication_authorized':False}},'cells':cells}
    path=ROOT/'notebooks/Combine_Submission_2027.ipynb';path.write_text(json.dumps(nb,indent=1)+'\n')
    return path


if __name__=='__main__':print(build())
