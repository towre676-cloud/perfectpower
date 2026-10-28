"""Four-coordinate, bounded, source-only movement correction.

Retrospective measurement study; predictions never depend on held-out labels.
"""
import numpy as np
from sklearn.linear_model import Ridge
from .movement_residual import Baseline, ConventionalDesign, Numeric, splits, separated, validate

COLUMNS = (
 'movement__PASS_RUSH_DRILL__speed_gain',
 'movement__PASS_RUSH_DRILL__recovery_accel',
 'movement__RUN_THE_HOOP_DRILL__redirect_turn',
 'movement__FOUR_BAG_AGILITY_DRILL__brake_accel',
)

class CompactFit:
    def __init__(self, train, seed=714):
        validate(train)
        if not set(COLUMNS)<=set(train):raise ValueError('four declared movement coordinates required')
        self.ids=set(train.nfl_id);self.baseline=Baseline(train,seed)
        response=np.empty(len(train))
        for f,(i,j) in enumerate(splits(train,3,seed+1)):
            response[j]=train.iloc[j].target.to_numpy()-Baseline(train.iloc[i],seed+20+f).predict(train.iloc[j])
        self.design=ConventionalDesign(train,'full15');b=self.design.transform(train)
        self.numeric=Numeric().fit(train[list(COLUMNS)]);z=self.numeric.transform(train[list(COLUMNS)])
        self.nuisance=Ridge(alpha=10).fit(b,z)
        z=np.clip(z-self.nuisance.predict(b).reshape(z.shape),-3,3)
        self.correction=Ridge(alpha=10,fit_intercept=False).fit(z,response)
        self.audit={'baseline':self.baseline.audit,'coordinates':list(COLUMNS),'missing_fraction':train[list(COLUMNS)].isna().mean().to_dict()}
    def predict(self, test):
        if self.ids & set(test.nfl_id):raise ValueError('athlete leakage')
        base=self.baseline.predict(test);z=self.numeric.transform(test[list(COLUMNS)])
        z=np.clip(z-self.nuisance.predict(self.design.transform(test)).reshape(z.shape),-3,3)
        change=np.clip(.5*self.correction.predict(z),-.02,.02)
        return base,np.clip(base+change,0,1)

def fit_predict(train,test,seed=714):
    separated(train,test);validate(train)
    train=train.reset_index(drop=True);base_oof=np.empty(len(train));fixed_oof=np.empty(len(train))
    for f,(i,j) in enumerate(splits(train,3,seed)):
        base_oof[j],fixed_oof[j]=CompactFit(train.iloc[i],seed+100+f).predict(train.iloc[j])
    gain=(train.target.to_numpy()-base_oof)**2-(train.target.to_numpy()-fixed_oof)**2
    se=float(gain.std(ddof=1)/np.sqrt(len(gain)));apply=bool(gain.mean()>se)
    fit=CompactFit(train,seed+200);base,fixed=fit.predict(test)
    prior=float(train.target.mean());counts=train.groupby('combine_position',dropna=False).target.agg(['sum','count'])
    role=[]
    for position in test.combine_position:
        c=counts.loc[position] if position in counts.index else None
        role.append((float(c['sum'])+20*prior)/(float(c['count'])+20) if c is not None else prior)
    pred={'conventional':base,'global_mean':np.full(len(test),prior),'role_mean':np.asarray(role),'fixed':fixed,'selected':fixed if apply else base.copy()}
    audit={**fit.audit,'apply_correction':apply,'inner_gain':float(gain.mean()),'inner_player_se':se,'maximum_absolute_fixed_change':float(np.max(np.abs(fixed-base)))}
    return pred,audit
