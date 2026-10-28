import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'scripts'))
import numpy as np
import pytest
from prepare_combine_getoff import launch_features
from perfectpower.combine_getoff import LAUNCH_COLUMNS

def test_rigid_transform_invariance():
 t=np.arange(12)*.1;s=1.1+t;p=np.c_[t,2*t]
 a=launch_features(t,p,s);b=launch_features(t,p@np.array([[0.,-1.],[1.,0.]])+[200.,-99.],s)
 for k in LAUNCH_COLUMNS:assert a[k]==pytest.approx(b[k],abs=1e-12)

def test_exact_time_endpoint_on_irregular_grid():
 t=np.arange(12)*.09;s=2+3*t;p=np.c_[4*t,np.zeros(len(t))]
 r=launch_features(t,p,s)
 assert r[LAUNCH_COLUMNS[0]]==pytest.approx(1.5)
 assert r[LAUNCH_COLUMNS[1]]==pytest.approx(2.)

def test_reject_gap_short_window_and_no_motion():
 for t,p,s in [(np.arange(12)*.2,np.zeros((12,2)),np.ones(12)*2),(np.arange(5)*.1,np.zeros((5,2)),np.ones(5)*2),(np.arange(12)*.1,np.zeros((12,2)),np.zeros(12))]:
  with pytest.raises(ValueError):launch_features(t,p,s)
