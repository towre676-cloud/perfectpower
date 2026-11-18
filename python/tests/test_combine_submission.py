"""Checks for the mathematical addition and evidence integrity; no NFL success test."""
import copy
import importlib.util
from pathlib import Path
import numpy as np
import pytest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('combine_submission_analysis',ROOT/'scripts/combine_submission_analysis.py')
a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)


def test_loss_identity_and_constant_correction_unequal_player_sizes():
    # Deliberately unequal exposures: equal-player weighting is distinct from pooling.
    errors=[np.array([-.4,.2]),np.array([.7,-.2,.1,.4,.6])]
    shifts=[.03,-.11]
    for e,d in zip(errors,shifts):
        def parts(x):return np.mean(x)**2,np.mean((x-np.mean(x))**2)
        primary,within=parts(e);new_primary,new_within=parts(e-d)
        assert np.isclose(np.mean(e**2),primary+within)
        assert np.isclose(within,new_within)
        assert np.isclose(np.mean(e**2)-np.mean((e-d)**2),primary-new_primary)
        assert np.isclose(primary-new_primary,2*np.mean(e)*d-d*d)


def test_receipt_analysis_rejects_altered_gain_or_loss_denominator():
    e=a.load(ROOT/'receipts/kaggle_combine');result=a.analyze(e)
    assert result['getoff_fallback_fits']==14
    assert result['getoff_decomposition'][1]['within_share_percent']==pytest.approx(95.437588038)
    changed=copy.deepcopy(e)
    changed['compact.json']['development']['comparisons']['selected']['relative_gain']=.1
    with pytest.raises(AssertionError):a.analyze(changed)
    changed=copy.deepcopy(e)
    v=changed['getoff.json']['development']['auxiliary']['comparisons']['fixed']
    v['mse_seconds2']+=.001
    base=changed['getoff.json']['development']['auxiliary']['baseline_mse_seconds2']
    v['relative_gain']=(base-v['mse_seconds2'])/base
    with pytest.raises(AssertionError):a.analyze(changed)


def test_paired_audit_does_not_consume_nfl_responses():
    import pandas as pd
    spec=importlib.util.spec_from_file_location('paired_audit',ROOT/'scripts/audit_combine_reliability_pair.py')
    paired=importlib.util.module_from_spec(spec);spec.loader.exec_module(paired)
    rng=np.random.default_rng(14);rows=[]
    for p in range(12):
        for j in range(2):rows.append({'nfl_id':p,'draft_year':2023+p%2,'event_id':100*p+j,'drill_name':'PASS_RUSH_DRILL','speed_gain':float(p+.2*rng.normal()),'recovery_accel':float(p*((-1)**j)+rng.normal()),'target':float(rng.normal())})
    data=pd.DataFrame(rows);before=paired.audit(data,draws=25)
    data['target']=1e30;data['player_get_off']=-1e30
    assert paired.audit(data,draws=25)==before


def geometry_module():
    spec=importlib.util.spec_from_file_location('loss_geometry',ROOT/'scripts/audit_combine_loss_geometry.py')
    g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g);return g


def test_oracle_ceiling_is_primary_over_auxiliary_not_within_share():
    g=geometry_module();r=g.oracle_ceilings(a.load(ROOT/'receipts/kaggle_combine')['getoff.json'])
    assert r[1]['maximum_constant_correction_relative_reduction_percent']==pytest.approx(4.562411961989192)
    assert r[1]['oracle_minimum_play_mse_s2']==pytest.approx(.05335194315870958)
    bad={'development':{'primary':{'baseline_mse_seconds2':2},'auxiliary':{'baseline_mse_seconds2':1}},'temporal':{}}
    with pytest.raises(ValueError):g.oracle_ceilings(bad)


def test_failed_full_strength_gain_has_incompatible_exact_shrinkage_optima():
    witness=geometry_module().exact_witnesses()['shrinkage_nonidentifiability']
    assert witness['case_A']['gain_at_one']==witness['case_B']['gain_at_one']=='-1'
    assert witness['case_A']['best_lambda_0_1']=='0'
    assert witness['case_B']['best_lambda_0_1']=='1/3'
    assert witness['case_B']['oracle_rescaled_gain']=='1/3'


def test_bounded_oracle_and_centered_interaction_exact_boundaries():
    from fractions import Fraction as F
    # Scalar bounded projection checked over a grid, including zero cap.
    for mu in map(F,[-2,-1,0,1,2]):
        for cap in [F(0),F(1,2),F(1)]:
            best=max(-cap,min(cap,mu));optimal=(max(abs(mu)-cap,F(0)))**2
            assert (mu-best)**2==optimal
            for d in [-cap,F(0),cap]:assert (mu-d)**2>=optimal
    checks=geometry_module().exact_witnesses()['exact_centered_interaction_checks']
    for c in checks:assert F(c['actual_gain'])==F(c['mean_component_gain'])+F(c['centered_component_gain'])
