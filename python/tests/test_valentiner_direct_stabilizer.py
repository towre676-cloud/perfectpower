"""Exact reconstruction and complete projectivity/curve checks."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import sys
import pytest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
from develop_valentiner_direct_stabilizer import exact_geometry, permutation_closure, filter_projectivities, covariant_script, prove
from develop_valentiner_three_exact_curves import prove as prove_curves


def test_exact_line_geometry_and_complete_projectivity_filter():
    F,_,lines,points,_=exact_geometry()
    receipt=json.loads((ROOT/'receipts/m22_interactions/valentiner_direct_stabilizer.json').read_text())
    assert len(lines)==45 and len(points)==201
    group=permutation_closure([tuple(g[:45]) for g in receipt['graph_generators']],45)
    assert len(group)==1440
    frame,witnesses,known=filter_projectivities(F,lines,group)
    assert frame==receipt['projective_frame_indices']
    assert witnesses==receipt['projectivity_failure_line_by_permutation_index']
    assert list(map(list,known))==receipt['known_projective_generators']
    assert sum(i==-1 for i in witnesses)==360


def test_covariant_script_and_transcript():
    folder=ROOT/'receipts/m22_interactions';stem='valentiner_direct_stabilizer'
    receipt=json.loads((folder/(stem+'.json')).read_text())
    script=(folder/(stem+'.sing')).read_bytes();log=(folder/(stem+'.log')).read_bytes()
    assert script.decode()==covariant_script()
    assert hashlib.sha256(script).hexdigest()==receipt['script_sha256']
    assert hashlib.sha256(log).hexdigest()==receipt['log_sha256']
    assert 'FACTOR_IDENTITY=1' in log.decode()
    assert receipt['classification_theorem_used'] is False


def test_complete_live_direct_count():
    binary=os.environ.get('SINGULAR_BINARY') or shutil.which('Singular')
    if not binary:pytest.skip('Singular optional; exact transcript committed')
    pytest.importorskip('pynauty')
    result=prove(binary)
    assert result['full_SU3_tensor_stabilizer_order']==1080
    assert result['full_45_line_factorization_verified']


def test_three_all_orders_curves_span_full_null_space():
    committed=json.loads((ROOT/'receipts/m22_interactions/valentiner_three_exact_curves.json').read_text())
    actual=prove_curves()
    assert actual==committed
    assert actual['exact_curve_count']==actual['tangent_rank']==3
    assert set(actual['null_coordinate_indices'])=={3,6,7}
    assert actual['all_nine_F_terms_vanish_on_each_curve']
