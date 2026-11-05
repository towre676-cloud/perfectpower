#!/usr/bin/env python3
"""Exact-rational oracle ceilings derived from existing aggregate MSE receipts.

This is loss geometry, not a fitted or deployable oracle. Decimal JSON MSE
values are interpreted as exact rationals for reproducible arithmetic.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


def oracle_ceilings(receipt):
    rows=[]
    for name,stage in [('development',receipt['development']),*receipt['temporal'].items()]:
        p=F(str(stage['primary']['baseline_mse_seconds2']))
        a=F(str(stage['auxiliary']['baseline_mse_seconds2']))
        if not 0<=p<=a or a==0:raise ValueError('Invalid loss decomposition')
        v=a-p;ceiling=p/a
        rows.append({'stage':name,'primary_mse_s2':float(p),'play_mse_s2':float(a),'oracle_minimum_play_mse_s2':float(v),'maximum_constant_correction_relative_reduction_percent':100*float(ceiling),'exact_from_decimal_receipt':{'primary':str(p),'auxiliary':str(a),'minimum':str(v),'ceiling_fraction':str(ceiling)},'scope':'Fixed existing baseline and retained evaluation records. Labels used by hypothetical oracle; not an achieved or forecast improvement.'})
    return rows


def exact_witnesses():
    def mean(v):return sum(v,F(0))/len(v)
    # Same baseline and same full-strength loss; incompatible shrinkage optima.
    e=[F(1)]*4;d0=list(map(F,[1,-1,1,-1]));d1=list(map(F,[3,-1,1,1]))
    def curve(d):
        c=mean([x*y for x,y in zip(e,d)]);q=mean([x*x for x in d]);g=2*c-q
        lam=max(F(0),min(F(1),c/q)) if q else F(0)
        return {'C':str(c),'D':str(q),'gain_at_one':str(g),'best_lambda_0_1':str(lam),'oracle_rescaled_gain':str(2*lam*c-lam*lam*q)}
    a,b=curve(d0),curve(d1)
    if a['gain_at_one']!=b['gain_at_one'] or a['best_lambda_0_1']==b['best_lambda_0_1']:raise AssertionError('Witness failed')
    # Within-player interaction is nonconstant and centered; unequal exposures.
    errors=[[F(1),F(3)],[F(-2),F(0),F(4)]]
    constants=[F(1,2),F(-1,3)];raw_h=[[F(1),F(2)],[F(3),F(1),F(-1)]]
    checks=[]
    for e,offset,h in zip(errors,constants,raw_h):
        mu=mean(e);r=[x-mu for x in e];hh=mean(h);q=[x-hh for x in h]
        actual=mean([x*x-(x-offset-y)**2 for x,y in zip(e,q)])
        between=2*mu*offset-offset*offset;within=2*mean([x*y for x,y in zip(r,q)])-mean([x*x for x in q])
        if actual!=between+within or mean(q)!=0:raise AssertionError('Orthogonal interaction identity failed')
        checks.append({'players_play_count':len(e),'actual_gain':str(actual),'mean_component_gain':str(between),'centered_component_gain':str(within)})
    return {'shrinkage_nonidentifiability':{'baseline_mse':'1','full_strength_candidate_mse':'2','case_A':a,'case_B':b},'exact_centered_interaction_checks':checks}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--receipt',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    r={'schema':'pp-combine-loss-geometry/1','scope':'Proved finite-record identities and exact rational arithmetic; no NFL refit or independent validation','oracle_ceilings':oracle_ceilings(json.loads(a.receipt.read_text())),'exact_witnesses':exact_witnesses(),'input_sha256':hashlib.sha256(a.receipt.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
