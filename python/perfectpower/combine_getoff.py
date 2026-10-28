"""Whole-player Combine launch transfer to charted NFL get-off.

Contextual predictions condition on NFL pre-snap circumstances. They are not
pre-draft forecasts or causal athlete effects. Held-out responses are never
read while fitting or predicting. Every class remains development/exploratory.
"""
import numpy as np
import pandas as pd
from sklearn.linear_model import Ridge
from .movement_residual import (PHYS, SETS, ALPHAS, Numeric,
                                ConventionalDesign, splits, separated)

LAUNCH_COLUMNS=('launch__speed_gain_0p5','launch__displacement_0p5')
CONTEXT_NUM=('down','yards_to_go','yardline_number','pre_snap_home_score',
             'pre_snap_visitor_score','quarter','snap_depth','snap_width','snap_speed')
CONTEXT_CAT=('lined_up_position','offense_formation','blitzing')
KEYS=('game_id','play_id','nfl_id')


def _validate(rows, outcome=False):
    required=set(KEYS)|{'draft_year','combine_position'}|set(PHYS)|set(LAUNCH_COLUMNS)|set(CONTEXT_NUM)|set(CONTEXT_CAT)
    if not required<=set(rows):raise ValueError('missing get-off schema: '+','.join(sorted(required-set(rows))))
    if rows.empty or rows[list(KEYS)+['draft_year']].isna().any().any():raise ValueError('nonempty complete play identities required')
    if rows.duplicated(list(KEYS)).any():raise ValueError('duplicate player/play identity')
    if rows.groupby('nfl_id').draft_year.nunique().gt(1).any():raise ValueError('player occurs in multiple draft classes')
    if rows.combine_position.isna().any():raise ValueError('source Combine position required')
    for c in PHYS+list(LAUNCH_COLUMNS)+['combine_position']+[c for c in rows if c.startswith('available__')]:
        if rows.groupby('nfl_id')[c].nunique(dropna=True).gt(1).any():raise ValueError('inconsistent source player metadata '+c)
    for c in PHYS+list(LAUNCH_COLUMNS)+list(CONTEXT_NUM):
        try:v=rows[c].to_numpy(dtype=float)
        except (TypeError,ValueError) as error:raise ValueError('invalid numeric input '+c) from error
        if np.isinf(v).any():raise ValueError('infinite numeric input '+c)
    if outcome and ('player_get_off' not in rows or not np.isfinite(rows.player_get_off.to_numpy(float)).all()):raise ValueError('finite charted get-off required')


def units(rows, target=None):
    """Audit source constancy, then emit one row per athlete in stable order."""
    _validate(rows)
    cols=['nfl_id','draft_year','combine_position']+PHYS+list(LAUNCH_COLUMNS)+sorted(c for c in rows if c.startswith('available__'))
    q=rows[cols].groupby('nfl_id',sort=True).first().reset_index()
    if target is not None:
        s=pd.Series(np.asarray(target,float),index=rows.index)
        q['target']=q.nfl_id.map(s.groupby(rows.nfl_id).mean()).to_numpy()
    return q


class Context:
    """Fixed Ridge10 nuisance with equal total training weight per player."""
    def __init__(self, rows):
        _validate(rows,True);self.ids=set(rows.nfl_id)
        self.numeric=Numeric().fit(rows[list(CONTEXT_NUM)])
        self.categories={c:sorted(rows[c].fillna('MISSING').astype(str).unique()) for c in CONTEXT_CAT}
        weights=1/rows.nfl_id.map(rows.nfl_id.value_counts()).to_numpy(float)
        self.model=Ridge(alpha=10).fit(self.transform(rows),rows.player_get_off.to_numpy(float),sample_weight=weights)
    def transform(self,rows):
        arrays=[self.numeric.transform(rows[list(CONTEXT_NUM)])]
        for c,levels in self.categories.items():
            v=rows[c].fillna('MISSING').astype(str).to_numpy()
            arrays.append(np.column_stack([v==level for level in levels]))
        return np.column_stack(arrays)
    def predict(self, rows):
        if self.ids & set(rows.nfl_id):raise ValueError('athlete leakage')
        return self.model.predict(self.transform(rows))


class RealBaseline:
    """Conventional subsets/grid on real get-off seconds; no rate clipping."""
    def __init__(self, rows, seed=714, config=None):
        self.ids=set(rows.nfl_id);y=rows.target.to_numpy(float)
        if not np.isfinite(y).all():raise ValueError('finite source response required')
        configs=[(s,a) for s in SETS for a in ALPHAS];loss=np.zeros(len(configs))
        if config is None:
            for i,j in splits(rows,3,seed):
                for si,s in enumerate(SETS):
                    d=ConventionalDesign(rows.iloc[i],s);x=d.transform(rows.iloc[i]);z=d.transform(rows.iloc[j])
                    for ai,a in enumerate(ALPHAS):
                        p=np.full(len(j),y[i].mean()) if np.isinf(a) else Ridge(alpha=a).fit(x,y[i]).predict(z)
                        loss[si*len(ALPHAS)+ai]+=np.square(y[j]-p).sum()/len(rows)
            best=int(np.argmin(loss));self.name,self.alpha=configs[best]
        else:self.name,self.alpha=config
        self.design=ConventionalDesign(rows,self.name);self.mean=float(y.mean())
        self.model=None if np.isinf(self.alpha) else Ridge(alpha=self.alpha).fit(self.design.transform(rows),y)
        self.audit={'physical_set':self.name,'alpha':'mean' if np.isinf(self.alpha) else float(self.alpha),'inner_mse':loss.tolist() if config is None else None,'configuration_source':'raw player-mean get-off CV' if config is None else 'reuse raw-selected conventional configuration; no residual-target tuning'}
    def predict(self, rows):
        if self.ids & set(rows.nfl_id):raise ValueError('athlete leakage')
        return np.full(len(rows),self.mean) if self.model is None else self.model.predict(self.design.transform(rows))


def _context_targets(train, seed):
    """OOF nuisance responses; separate every player including resample copies."""
    q=np.empty(len(train))
    for i,j in splits(train,3,seed):q[j]=Context(train.iloc[i]).predict(train.iloc[j])
    return units(train,train.player_get_off.to_numpy(float)-q)


class ContextSourceBase:
    """Whole context/source pipeline; its test players never enter nuisance fits.

    Select conventional config on raw player-mean get-off, then freeze it for
    the contextual residual fit. No CV uses peer residuals whose nuisance fits
    included that CV holdout's responses.
    """
    def __init__(self,train,seed=714):
        _validate(train,True);self.ids=set(train.nfl_id)
        raw=units(train,train.player_get_off.to_numpy(float))
        self.raw_baseline=RealBaseline(raw,seed)
        self.raw_mean=float(raw.target.mean());self.context=Context(train)
        residual=_context_targets(train,seed+1)
        self.baseline=RealBaseline(residual,seed+2,config=(self.raw_baseline.name,self.raw_baseline.alpha))
    def predict(self,test):
        if self.ids & set(test.nfl_id):raise ValueError('athlete leakage')
        u=units(test);index=pd.Index(u.nfl_id).get_indexer(test.nfl_id)
        context=self.context.predict(test)
        return {'raw_mean':np.full(len(test),self.raw_mean),
                'raw_conventional':self.raw_baseline.predict(u)[index],
                'context':context,'conventional':context+self.baseline.predict(u)[index]}


class GetoffFit:
    def __init__(self, train, seed=714):
        _validate(train,True);self.ids=set(train.nfl_id)
        self.base=ContextSourceBase(train,seed)
        raw=units(train,train.player_get_off.to_numpy(float))
        # Entire context+source baseline is fitted without each response player's
        # labels. In particular, peer nuisance targets cannot include that label.
        response=np.empty(len(train));self.crossfit_baseline_predictions=np.empty(len(train))
        for f,(i,j) in enumerate(splits(train,3,seed+4)):
            predicted=ContextSourceBase(train.iloc[i],seed+20+f).predict(train.iloc[j])['conventional']
            self.crossfit_baseline_predictions[j]=predicted
            response[j]=train.iloc[j].player_get_off.to_numpy(float)-predicted
        residual=units(train,response)
        self.numeric=Numeric().fit(residual[list(LAUNCH_COLUMNS)])
        self.design=ConventionalDesign(residual,'full15');b=self.design.transform(residual)
        z=self.numeric.transform(residual[list(LAUNCH_COLUMNS)])
        self.nuisance=Ridge(alpha=10).fit(b,z)
        z=np.clip(z-self.nuisance.predict(b).reshape(z.shape),-3,3)
        self.correction=Ridge(alpha=10,fit_intercept=False).fit(z,residual.target.to_numpy(float))
        self.cap=.5*float(np.std(raw.target.to_numpy(float)-float(raw.target.iloc[0]),ddof=0))
        self.audit={'conventional':self.base.baseline.audit,'raw_conventional':self.base.raw_baseline.audit,'correction_cap_seconds':self.cap,'training_players':len(raw),'target':'Mean charted NFL player_get_off seconds, conditional on pre-snap context','source_features':list(LAUNCH_COLUMNS),'nuisance_separation':'Every correction-response player excluded from complete context/source fitting, including peer nuisance targets.'}
    def predict(self,test):
        if self.ids & set(test.nfl_id):raise ValueError('athlete leakage')
        p=self.base.predict(test);u=units(test)
        z=self.numeric.transform(u[list(LAUNCH_COLUMNS)])
        z=np.clip(z-self.nuisance.predict(self.design.transform(u)).reshape(z.shape),-3,3)
        change=np.clip(.5*self.correction.predict(z),-self.cap,self.cap)
        index=pd.Index(u.nfl_id).get_indexer(test.nfl_id)
        p['fixed']=p['conventional']+change[index]
        return p


def player_loss(rows,prediction):
    """Primary squared mean forecast error per player (not mean play loss)."""
    e=pd.DataFrame({'nfl_id':rows.nfl_id.to_numpy(),'error':rows.player_get_off.to_numpy(float)-prediction})
    return e.groupby('nfl_id',sort=True).error.mean().pow(2)


def fit_predict(train,test,seed=714):
    """Return play-aligned predictions and audit, never consulting test labels."""
    separated(train,test);_validate(train,True);_validate(test)
    train=train.reset_index(drop=True);base=np.empty(len(train));fixed=np.empty(len(train))
    for f,(i,j) in enumerate(splits(train,3,seed)):
        p=GetoffFit(train.iloc[i],seed+100+f).predict(train.iloc[j]);base[j]=p['conventional'];fixed[j]=p['fixed']
    gain=(player_loss(train,base)-player_loss(train,fixed)).to_numpy()
    se=float(gain.std(ddof=1)/np.sqrt(len(gain))) if len(gain)>1 else np.inf
    apply=bool(gain.mean()>se)
    fit=GetoffFit(train,seed+200);p=fit.predict(test);p['selected']=p['fixed'] if apply else p['conventional'].copy()
    return p,{**fit.audit,'apply_correction':apply,'inner_player_gain':float(gain.mean()),'inner_player_se':se}
