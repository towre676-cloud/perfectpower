import copy
import numpy as np
import pandas as pd
import pytest
from perfectpower.scouting_confirmation import freeze,score

def rows():
 return pd.DataFrame([dict(pfr_id=str(i),draft_year=2025,pos='LB' if i%2 else 'DT',identity_status='verified_name_birth',asof_verified=True,combine=2.,aggregate=1.,role_mean=2.) for i in range(40)])
def packet():return freeze(rows(),'a'*64,dict(latest_training_class=2023,feature_manifest_sha256='a'*64,model_artifact_sha256='b'*64,training_manifest_sha256='c'*64))
def outcomes():return pd.DataFrame([dict(pfr_id=str(i),pressures=1,defensive_snaps=100,team_cluster=str(i%10)) for i in range(40)])
def test_outcome_blind():
 q=rows();q['target']=np.arange(40);assert freeze(q,'a'*64,{},True)==freeze(q.assign(target=-99),'a'*64,{},True)
def test_route_and_fallback():
 p=packet();q=pd.DataFrame(p['payload']['rows']);assert q.selected.sum()==20;assert (q.loc[~q.selected,'candidate']==2).all()
def test_guard_and_tamper():
 with pytest.raises(ValueError):score(packet(),outcomes(),'2026-10-28',True)
 p=packet();p['payload']['rows'][0]['combine']=99
 with pytest.raises(ValueError):score(p,outcomes(),'2027-03-01',True)
def test_duplicate_missing_nonfinite():
 for q in [pd.concat([rows(),rows().iloc[:1]]),rows().assign(combine=np.nan)]:
  with pytest.raises(ValueError):freeze(q,'a'*64,{},True)
 with pytest.raises(ValueError):score(packet(),outcomes().iloc[:-1],'2027-03-01',True)
def test_zero_exposure_and_determinism():
 o=outcomes();o.loc[0,['pressures','defensive_snaps']]=0
 a=score(packet(),o,'2027-03-01',True);assert a==score(packet(),o,'2027-03-01',True);assert a['zero_exposure']==1
 assert a['groups']['selected_LB']['comparisons']['aggregate']['absolute_gain']==0

def test_identity_availability_and_direction():
 q=rows();q.loc[1,'asof_verified']=False;q.loc[3,'identity_status']='ambiguous';q.loc[5,'aggregate']=3
 assert sum(r['selected'] for r in freeze(q,'a'*64,{},True)['payload']['rows'])==17

def test_real_cluster_interval():
 from perfectpower.scouting_confirmation import interval
 x=np.arange(16,dtype=float);g=np.repeat(np.arange(8),2)
 a=interval(x,g,.05,draws=200)
 assert a==interval(x,g,.05,draws=200) and a[0]<7.5<a[1]
