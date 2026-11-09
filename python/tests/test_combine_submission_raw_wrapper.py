"""Exercise wrapper orchestration without claiming an official-data replay."""
import ast
import copy
import json
from pathlib import Path
import numpy as np
import pandas as pd
import pytest
ROOT=Path(__file__).resolve().parents[2]


def setup_scope(monkeypatch,tmp_path):
    monkeypatch.setenv('BDB_SUBMISSION_MODE','receipts')
    monkeypatch.setenv('BDB_SUBMISSION_OUTPUT',str(tmp_path/'public'))
    notebook=json.loads((ROOT/'notebooks/Combine_Submission_2027.ipynb').read_text())
    cells=[''.join(c['source']) for c in notebook['cells'] if c['cell_type']=='code']
    scope={};exec(cells[0],scope)
    return cells,scope


def execute_stubbed_raw(monkeypatch,tmp_path,refits=20):
    cells,scope=setup_scope(monkeypatch,tmp_path)
    reference=copy.deepcopy(scope['EVIDENCE'])
    scope['MODE']='raw'
    for key in ('BDB_PLAYERS','BDB_EVENTS','BDB_GETOFF_RUSHES'):monkeypatch.delenv(key,raising=False)
    # Replace only the costly experiment boundary. Real wrapper dispatch,
    # comparison validation, paired-result assignment and status logic execute.
    tree=ast.parse(cells[1])
    tree.body=[n for n in tree.body if not (isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ('ORIGINAL_COMPUTE_CELLS','PAIR_AUDIT_SOURCE'))]
    scope['ORIGINAL_COMPUTE_CELLS']={1:'RAW_INPUTS_VERIFIED=True',3:'',5:f"result={reference['compact.json']!r}\nrepeatability={reference['repeatability.json']!r}\nREFITS={refits}\nPERMUTATIONS=16\nEVENTS='synthetic_test_boundary'",9:f"GETOFF_RESULT={reference['getoff.json']!r}\ngetoff_extraction={reference['getoff_extraction.json']!r}"}
    scope['PAIR_AUDIT_SOURCE']="def audit(events): return {'fresh_test_marker': True}"
    monkeypatch.setattr(pd,'read_pickle',lambda path:pd.DataFrame())
    exec(compile(tree,'raw_wrapper_test','exec'),scope)
    return scope,reference


@pytest.mark.parametrize('refits,expected',[(20,True),(0,False)])
def test_raw_wrapper_replaces_pair_and_labels_full_reproduction(monkeypatch,tmp_path,refits,expected):
    scope,_=execute_stubbed_raw(monkeypatch,tmp_path,refits)
    assert scope['RAW_EXECUTED'] is True
    assert scope['FULL_REPRODUCTION'] is expected
    assert scope['EVIDENCE']['reliability_pair_review.json']=={'fresh_test_marker':True}
    assert all(isinstance(k,str) for k in scope['EVIDENCE'])
    assert scope['RAW_COMPARISONS']=={'pressure_count':12,'getoff_count':30,'baseline_count':9,'maximum_mse_difference':0.0}
    assert scope['private'].is_relative_to('/tmp')
    assert not scope['private'].is_relative_to(scope['OUT'])


def test_replay_rejects_missing_model_changed_baseline_and_nonfinite(monkeypatch,tmp_path):
    scope,reference=execute_stubbed_raw(monkeypatch,tmp_path)
    compare=scope['compare_replay']
    for change in ('missing','baseline','nan'):
        actual=copy.deepcopy(reference);metric=actual['compact.json']['development']
        if change=='missing':del metric['comparisons']['fixed']
        elif change=='baseline':metric['baseline_mse']+=.01
        else:metric['comparisons']['fixed']['mse']=np.nan
        with pytest.raises(ValueError):compare(actual,reference)
